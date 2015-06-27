; Erlang External Term Format (http://erlang.org/doc/apps/erts/erl_ext_dist.html)

(defvar *erlang-socket* nil)
(defstruct abuf more buf len cur)
(defmacro abuf-ref (i) `(aref (abuf-buf ab) ,i))

; erlang-binary-term format
(defun encode-erlang-item (arr item)
  (cond
    ((numberp item)
      (cond
        ((< item 256)
          (vector-push-extend 97 arr)
          (vector-push-extend item arr))
        (t
          (vector-push-extend 98 arr)
          ;(vector-push-extend (logand item #xff) arr)
          ;(vector-push-extend (logand (ash item  -8) #xff) arr)
          ;(vector-push-extend (logand (ash item -16) #xff) arr)
          ;(vector-push-extend (logand (ash item -24) #xff) arr)
          (vector-push-extend (logand (ash item -24) #xff) arr)
          (vector-push-extend (logand (ash item -16) #xff) arr)
          (vector-push-extend (logand (ash item  -8) #xff) arr)
          (vector-push-extend (logand item #xff) arr))))
    ((keywordp item)
      (let ((str (string-downcase (string item))))
        (vector-push-extend 115 arr)
        (vector-push-extend (length str) arr)
        (loop for c across str do
          (vector-push-extend (char-code c) arr))))
    ((stringp item)
      (vector-push-extend 107 arr)
      (vector-push-extend 0 arr)
      (vector-push-extend (length item) arr)
      (loop for c across item do
        (vector-push-extend (char-code c) arr)))
    ((not item)
      (vector-push-extend 115 arr)
      (vector-push-extend 3 arr)
      (vector-push-extend 110 arr) ; nil
      (vector-push-extend 105 arr)
      (vector-push-extend 108 arr))
    (t
      (L "ERROR: unknown item ~s, to erlang-encode" item))))

(defun erlang-net-tuple (s cmd lst)
  (declare (ignorable s))
  ;(L "erlang-net-tuple: cmd=~s lst=~s" cmd lst)
  (let ((arr (make-array 0 :fill-pointer 0 :adjustable t :element-type '(unsigned-byte 8))))
    (vector-push-extend 80 arr) ; 'P'
    (vector-push-extend 66 arr) ; 'B'
    (vector-push-extend 88 arr) ; 'X'
    (vector-push-extend 67 arr) ; 'C'
    (vector-push-extend (ecase cmd
                          (:nil 0)
                          (:ping 1)
                          (:pre-add 2)
                          (:pre-del 3)
                          (:mex-state 4)
                          (:mex-conf  5)
                          (:sync 48)
                          (:subscribe 49)
                          (:set-cfwd 65)
                          (:clr-cfwd 66)
                          (:reload 252))
                        arr)
    (vector-push-extend 0 arr) ;  value, length of rest of data
    (vector-push-extend 131 arr) ; erlang binary-term-format version
    (vector-push-extend 104 arr) ; erlang-tuple holding all items
    (vector-push-extend (length lst) arr) ; tuple-size(number of items)
    (loop for item in lst do
      ;(L "  decode ~s" item)
      (encode-erlang-item arr item))
    (setf (aref arr 5) (- (length arr) 6)) ; set length in the erlang-binary-term
    ;(L "to-erlang: ~s" arr)
    (sb-bsd-sockets:socket-send s arr (length arr))))

; pop of a single byte from the buffer, if needed grow the buffer using the stream/socket
(defun abuf-pop (ab)
  (cond
    ((< (abuf-cur ab) (abuf-len ab))
      (let ((c (abuf-ref (abuf-cur ab))))
        (incf (abuf-cur ab))
        (char-code c)))
    (t (multiple-value-bind (buf len addr) (sb-bsd-sockets:socket-receive (abuf-more ab) nil 1024)
         (declare (ignore addr))
         (cond
           ((zerop len)
             (L "ERROR: erlang side has closed, lets close too")
             nil)
           (t
             (setf (abuf-buf ab) buf)
             (setf (abuf-len ab) len)
             (setf (abuf-cur ab) 1)
             (char-code (aref buf 0))))))))

(defun erlang-read-uint8 (ab)
  (abuf-pop ab))

(defun erlang-read-uint16 (ab)
  (let (a b)
    (setf a (abuf-pop ab))
    (if (not a) (return-from erlang-read-uint16))
    (setf b (abuf-pop ab))
    (if (not b) (return-from erlang-read-uint16))
    (+ (* a 256) b)))

(defun erlang-read-uint32 (ab)
  (let (a b c d)
    (setf a (abuf-pop ab))
    (if (not a) (return-from erlang-read-uint32))
    (setf b (abuf-pop ab))
    (if (not b) (return-from erlang-read-uint32))
    (setf c (abuf-pop ab))
    (if (not c) (return-from erlang-read-uint32))
    (setf d (abuf-pop ab))
    (if (not d) (return-from erlang-read-uint32))
    (+ (* a (ash 1 24))
       (* b (ash 1 16))
       (* c (ash 1 8))
       d)))

(defun erlang-read-string (ab len)
  (let ((str (make-array 0 :fill-pointer 0 :adjustable t :element-type 'character)))
    (loop repeat len do
      (let ((c (abuf-pop ab)))
        (if (not c) (return-from erlang-read-string))
        (vector-push-extend (code-char c) str)))
    str))

(defun erlang-read-binary-term (ab depth)
  (when (> depth 16)
    (L "ERROR: to recursive depth in erlang term")
    (return-from erlang-read-binary-term))
  (let ((type (abuf-pop ab))
        (dep ""))
    (loop repeat depth do (setf dep (concatenate 'string dep "  ")))
    ;(L "~aerlang-read-binary-term" dep)
    (if (not type) (return-from erlang-read-binary-term))
    ;(L "    erlang type ~a" type)
    (cond
      ((= type 97) ; small-integer
        ;(L "~asmall-int" dep)
        (erlang-read-uint8 ab))
      ((= type 98) ; integer
        (erlang-read-uint32 ab))
      ((= type 104) ; small-tuple
        (let ((arity (erlang-read-uint8 ab)))
          (when arity
            ;(L "~astuple-len ~a" dep arity)
            (loop repeat arity collect
              (let ((item (erlang-read-binary-term ab (1+ depth))))
                (if (not item) (return-from erlang-read-binary-term))
                item)))))
      ((= type 100) ; atom
        (let ((len (erlang-read-uint16 ab)) name)
          (when len
            ;(L "~aatom-len ~a" dep len)
            (setf name (erlang-read-string ab len))
            ;(L "~aatom-dat ~a" dep name)
            name)))
      ((= type 110) ; small-big-int
        (let ((len (erlang-read-uint8 ab)) (int 0))
          (when len
            (let ((sign (erlang-read-uint8 ab)))
              (when sign
                (loop for i from 0 below len do
                  (let ((c (erlang-read-uint8 ab)))
                    (if (not c) (return-from erlang-read-binary-term))
                    (incf int (* c (ash 1 (* i 8))))))
                (unless (zerop sign) (setf int (- int)))
                ;(L "~asmall-big-int ~a ~a = ~a" dep len sign int)
                int)))))
      ((= type 106) ; nil
        t)
      ((= type 115) ; small-atom
        (let ((len (erlang-read-uint8 ab))
              name)
          (when len
            ;(L "~asatom-len ~a" dep len)
            (setf name (erlang-read-string ab len))
            ;(L "~asatom-dat ~a" dep name)
            name)))
      ((= type 107) ; string
        (let ((len (erlang-read-uint16 ab))
              str)
          (when len
            ;(L "~astring-len ~a" dep len)
            (setf str (loop repeat len collect
                        (let ((c (abuf-pop ab)))
                          (if (not c) (return-from erlang-read-binary-term))
                          c)))
            ;(L "~astring-dat ~a" dep str)
            str)))
      ((= type 108) ; list
        (let ((len (erlang-read-uint32 ab)))
          (when len
            ;(L "~alist-len ~a" dep len)
            (loop repeat len collect
              (let ((item (erlang-read-binary-term ab (1+ depth))))
                (if (not item) (return-from erlang-read-binary-term))
                item)))))
      (t
        (L "WARNING: unknown erlang type ~a" type)
        t))))

