;
; buffer/pdu handling
;

(defmacro bufcpy (buf str offset)
  `(loop for i from 0 for a across ,str do
    (setf (aref ,buf (+ ,offset i)) (char-code a))))

(defun buf2str (buf off len)
  (let ((arr (make-array len :element-type 'character)))
    (loop for i from 0 below len do
      (setf (aref arr i) (code-char (aref buf (+ i off)))))
    arr))

(defmacro buf-8bit (buf off) `(aref ,buf ,off))

(defmacro buf-16bit (buf off)
  `(+ (ash (aref ,buf ,off) 8)
      (aref ,buf (1+ ,off))))

(defun buf-16bit-set (buf n word)
  (setf (aref buf n)      (ldb (byte 8  8) word))
  (setf (aref buf (1+ n)) (ldb (byte 8  0) word)))

(defmacro buf-32bit (buf off)
  `(+ (ash (aref ,buf ,off)       24)
      (ash (aref ,buf (+ ,off 1)) 16)
      (ash (aref ,buf (+ ,off 2)) 8)
           (aref ,buf (+ ,off 3))))

(defun buf-32bit-set (buf n word)
  (setf (aref buf n)       (ldb (byte 8 24) word))
  (setf (aref buf (+ n 1)) (ldb (byte 8 16) word))
  (setf (aref buf (+ n 2)) (ldb (byte 8  8) word))
  (setf (aref buf (+ n 3)) (ldb (byte 8  0) word)))

(defun make-pdu (lst)
  (let ((len 0))
    (loop for item in lst do
      (incf len
            (cond
              ((numberp item) 1)
              ((stringp item) (length item))
              ((arrayp  item) (length item))
              ((eq item '16bit) 2)
              (t (error "unknown item type: ~s~%" item)))))
    (let ((arr (make-array len :element-type '(unsigned-byte 8)))
          (n 0))
      (loop for item in lst do
        (cond
          ((numberp item)
            (setf (aref arr n) item)
            (incf n))
          ((stringp item)
            (loop for i from 0 for a across item do
              (setf (aref arr (+ n i)) (char-code a)))
            (incf n (length item)))
          ((arrayp item)
            (loop for i from 0 for a across item do
              (setf (aref arr (+ n i)) a))
            (incf n (length item)))
          ((eq item '16bit)
            (incf n 2))))
      arr)))

(defun make-pdu32 (lst)
  (let ((len 0))
    (loop for item in lst do
      (incf len
            (cond
              ((numberp item) 1)
              ((stringp item) (length item))
              ((arrayp  item) (length item))
              ((eq item '32bit) 4)
              (t (error "unknown item type: ~s~%" item)))))
    (let ((arr (make-array len :element-type '(unsigned-byte 8)))
          (n 0))
      (loop for item in lst do
        (cond
          ((numberp item)
            (setf (aref arr n) item)
            (incf n))
          ((stringp item)
            (loop for i from 0 for a across item do
              (setf (aref arr (+ n i)) (char-code a)))
            (incf n (length item)))
          ((arrayp item)
            (loop for i from 0 for a across item do
              (setf (aref arr (+ n i)) a))
            (incf n (length item)))
          ((eq item '32bit)
            (incf n 4))))
      arr)))

;
; distribution cache
;

(defun erl-distcache-fetch (cache ref)
  (aref cache ref))

;
; Erlang binary term format
;

(defun erl-decode-binary-term (cache buf n)
  (let ((type (aref buf n)))
    ;(L "erl-decode-binary-term: n=~s type=~a~%" n type)
    (incf n)
    (cond
      ((= type 82) ; atom-cache-ref
        (cons (erl-distcache-fetch cache (buf-8bit buf n)) (1+ n)))
      ((= type 97)
        (cons (buf-8bit buf n) (1+ n)))
      ((= type 98)
        (cons (buf-32bit buf n) (+ 4 n)))
      ((= type 103) ; PID
        (let ((item (erl-decode-binary-term cache buf n)))
          (setf n (cdr item))
          (cons (list :pid
                      (first item)
                      (buf-32bit buf n)      ; get id
                      (buf-32bit buf (+ n 4)) ; get serial
                      (buf-8bit buf (+ n 8))) ; get creation
                (+ n 9))))
      ((= type 104)
        (let ((arity (buf-8bit buf n)))
          (incf n)
          (let ((arr (make-array arity)))
            ;(L "   collecting tuple items n=~a~%" n)
            (loop for i from 0 below arity do
              (destructuring-bind (item . nn) (erl-decode-binary-term cache buf n)
                (setf n nn)
                (setf (aref arr i) item)))
            ;(L "   done collecting tuple items n=~a~%" n)
            (cons arr n))))
      ((= type 106) ; NIL_EXT
        (cons nil n))
      ; put rarely used term below
      ((= type 108) ; LIST_EXT
        (let ((len (buf-32bit buf n)))
          ;(L "list, ~a elements~%" len)
          (incf n 4)
          (cons (append (loop repeat len collect
                          (destructuring-bind (item . nn)
                                              (erl-decode-binary-term cache buf n)
                            (setf n nn)
                            item))
                        (list (destructuring-bind (item . nn)
                                                  (erl-decode-binary-term cache buf n)
                                (setf n nn)
                                item)))
                n)))
      ((= type 107) ; STRING_EXT
        (let* ((len (buf-16bit buf n))
               (str (make-array len :element-type 'character)))
          (incf n 2)
          (loop for i from 0 below len do
            (setf (aref str i) (code-char (aref buf (+ n i)))))
          (incf n len)
          ;(L "decoded string: ~s n=~s~%" str n)
          (cons str n)))
      ((= type 114) ; NEW_REFERENCE_EXT
        (let ((len (buf-16bit buf n)))
          (incf n 2)
          (destructuring-bind (node . nn) (erl-decode-binary-term cache buf n)
            (setf n nn)
            (let ((creation (buf-8bit  buf n))
                  (id       (buf-32bit buf (+ n 1))))
              (incf n (1+ (* len 4)))
              (cons (list :ref2 node creation id) n)))))
      (t
        (error "unknown binary-term type ~a" type)))))

;
; erlang distribution protocol
;

(macrolet
  ((make-state-macro (n name)
   (let ((sym (intern (concatenate 'string "ERL-STATE-" (string name)))))
     `(defmacro ,sym (erl) `(aref ,erl ,,n)))))
  (make-state-macro 0 epmd)       ; alive socket to epmd (keep it open) (make this a global socket/thread)
  (make-state-macro 1 cookie)     ; socket to other node
  (make-state-macro 2 bar)        ; remote node
  (make-state-macro 3 name)       ; this nodes sname/name
  (make-state-macro 4 node)       ; remote node sname/name
  (make-state-macro 5 atom-cache) ; this nodes sname/name
  (make-state-macro 6 creation)   ; creation number of this node-name (given by epmd)
  )
(defmacro erl-make-state ()
  `(make-array 7 :initial-element nil))

(defun erl-dist-init (&key name cookie)
  (let ((state (erl-make-state)))
    (setf (erl-state-name       state) name)
    (setf (erl-state-cookie     state) cookie)
    (setf (erl-state-atom-cache state) (make-array 2048))
    state))

(defun erl-send-req (socket buf)
  (L "-------- sending, using socket ~s" socket)
  (let ((buflen (length buf)))
    (setf (aref buf 0) (ash (- buflen 2) -8))
    (setf (aref buf 1) (logand #xff (- buflen 2)))
    (socket-write socket buf buflen)))

(defun erl-send-req32 (socket buf)
  (let ((buflen (length buf)))
    (setf (aref buf 0) (ash (- buflen 4) -24))
    (setf (aref buf 1) (ash (- buflen 4) -16))
    (setf (aref buf 2) (ash (- buflen 4)  -8))
    (setf (aref buf 3) (logand #xff (- buflen 4)))
    (L "pdu len: ~x'~x'~x'~x" (aref buf 0) (aref buf 1) (aref buf 2) (aref buf 3))
    (socket-write socket buf buflen)))

(defun erl-recv-16bit-pdu (socket)
  ; read two bytes worth of length
  (destructuring-bind (buf len) (socket-read socket 2)
    (declare (ignore len))
    (let ((len (buf-16bit buf 0)))
      (destructuring-bind (buf2 len2) (socket-read socket len) ; read rest
        (cons buf2 len2)))))

(defun erl-recv-32bit-pdu (socket)
  ; read two bytes worth of length
  (destructuring-bind (buf len) (socket-read socket 4)
    (declare (ignore len))
    (let ((len (buf-32bit buf 0)))
      (cond
        ((> len 65535)
          (error "WARNING: to large pdu ~s > 4096" len))
        ((= len 0) ; this is an ack-packet
          (L "received a tickle")
          (cons nil 0))
        (t
          (destructuring-bind (buf2 len2) (socket-read socket len) ; read rest
            (cons buf2 len2)))))))

;
;
; EPMD (Erlang Port Mapper Deamon) client
; all request begins with a 2byte length, length of the bytes that follows
;

(defun erl-epmd-connect (erl)
  (setf (erl-state-epmd erl) (make-socket :tcp))
  (socket-connect (erl-state-epmd erl) #(127 0 0 1) 4369))

(defun erl-epmd-close (erl)
  (let ((socket (erl-state-epmd erl)))
    (when socket
      (socket-close socket)
      (setf (erl-state-epmd erl) nil))))

; ALIVE2_REQ
; 1byte = 120
; 2byte = port number where node accepts connections
; 1byte = nodetype (77=normal, 72=hidden)
; 1byte = protocol (0 = tcp/ipv4)
; 2byte = highestversion = 5
; 2byte = lowestversion = 5
; 2byte = Nlen
; Nlen  = Nodename
; 2byte = Elen
; Elen  = Extra
;
; ALIVE2_RESP
; 1byte = 121
; 1byte = result (0 ok, * error)
; 2byte = creation
(defun erl-epmd-alive (erl)
  (let* ((socket (erl-state-epmd erl))
         (nodename (subseq (erl-state-name erl) 0 (search "@" (erl-state-name erl))))
         (nodelen (length nodename))
         ;(buf (make-array (+ 16 nodelen) :element-type '(unsigned-byte 8)))
         (buf (make-pdu (list '16bit ; buffer length
                              120  ; ALIVE2_REQ
                              88 88  ; port-number
                              72   ; hidden node
                              0    ; protocol
                              0 5  ; highestversion
                              0 5  ; lowestversion
                              0 nodelen ; length of nodename
                              nodename
                              0 0)))) ; extra-length
    (erl-send-req socket buf)
    ; get the ALIVE_RESP2 response
    (destructuring-bind (buf len) (socket-read socket 4)
      (cond
        ((/= len 4) :error) ; ALIVE_RESP2 should be 4 bytes in size
        ((/= (buf-8bit buf 0) 121) :error) ; ALIVE_RESP2 type of response
        ((/= (buf-8bit buf 1)   0) :error) ; epmd responds with error
        (t (buf-16bit buf 2)))))) ; return the Creation number to use

; PORT_PLEASE2_REQ
; 1byte = 122
; nbyte = nodename
;
; PORT2_RESP (error result)
; 1byte = 119
; 1byte = result (error > 0)
;
; 1byte = 119
; 1byte = result = 0
; 2byte = PortNo
; 1byte = nodetype
; 1byte = protocol
; 2byte = highestversion
; 2byte = lowestversion
; 2byte = Nlen
; Nlen  = nodename
; 2byte = Elen
; Elen  = Extra
(defun epmd-please (socket nodename)
  (let* ((nodelen (length nodename))
         (buf (make-array (+ 3 nodelen) :element-type '(unsigned-byte 8))))
    (setf (aref buf 2) 122) ; PORT_PLEASE2_REQ
    (bufcpy buf nodename 3)
    (setf (aref buf 0) (ash (+ 1 nodelen) -8))
    (setf (aref buf 1) (logand #xff (+ 1 nodelen)))
    (socket-write socket buf (+ 3 nodelen))))

(defun erl-epmd-nodename (sock s erl nodename)
  (declare (ignore erl))
  (if (search "@" nodename) ; shave of anything at and after @
    (setf nodename (subseq nodename 0 (search "@" nodename))))
  (let ((c (setf (aref sock s) (make-socket :tcp)))
        portno)
    (unless c (return-from erl-epmd-nodename))
    (socket-connect c #(127 0 0 1) 4369)
    (epmd-please c nodename)
    (destructuring-bind (buf len) (socket-read c)
      (when (> len 1) ; atleast two bytes needed
        (cond
          ((zerop (aref buf 1)) ; EPMD has found the name
            (assert (= (aref buf 0) 119)) ; PORT2_RESP
            (L "epmd: PLEASE_RESP: ~s" (loop for i from 0 below len collect (aref buf i)))
            (let ((nodetype (aref buf 4))
                  (protocol (aref buf 5))
                  (highver (buf-16bit buf 6)) ;     (+ (ash (aref buf 6) 8)
                                             ;      (aref buf 7)))
                  (lowver  (buf-16bit buf 8)) ;(+ (ash (aref buf 8) 8)
                                              ;        (aref buf 9)))
                  (nodelen (buf-16bit buf 10)) ;(+ (ash (aref buf 10) 8)
                                               ;        (aref buf 11))
                  )
              (assert (zerop protocol))
              (assert (= highver 5))
              (assert (= lowver 5))
              (assert (or (= nodetype 77)   ; normal erlang node
                          (= nodetype 72))) ; hidden erlang node
              (let ((node (make-array nodelen :element-type 'character)))
                (loop for i from 0 below nodelen do
                  (setf (aref node i) (code-char (aref buf (+ 12 i)))))
                (if (string/= node nodename) (L "WARNING: nodename mismatch: ~s/~s" node nodename)))
              (setf portno (+ (ash (aref buf 2) 8)
                                   (aref buf 3)))))
          (t ; error
            (L "epmd response for port2-please error-code: ~s" (aref buf 1))))))
    (socket-close c)
    (setf (aref sock s) nil)
    portno))

(defun erl-encode-tuple (&rest tuples)
  (let ((len 0))
    (loop for tuple in tuples do
      (incf len (cond
                  ((arrayp tuple)
                    (if (array-has-fill-pointer-p tuple)
                      (fill-pointer tuple)
                      (length tuple)))
                  ((numberp tuple) 2)
                  (t (error "unknown tuple-item type: ~s" tuple)))))
    (let ((i 2)
          (buf (make-array (+ 2 len))))
      (setf (aref buf 0) 104) ; SMALL_TUPLE_EXT
      (setf (aref buf 1) (length tuples))
      (loop for tuple in tuples do
        (cond
          ((arrayp tuple)
            (let ((len (if (array-has-fill-pointer-p tuple) (fill-pointer tuple) (length tuple))))
              (loop for n from 0 below len do
                (setf (aref buf i) (aref tuple n))
                (incf i))))
          ((numberp tuple)
            (setf (aref buf i) #x61) (incf i) ; SMALL_INT_EXT
            (setf (aref buf i) tuple) (incf i))
          (t
            (error "unknown type of item in tuple; ~s" tuple))))
      buf)))

(defun erl-encode-newref (node id creation)
  (let ((arr (make-array 18 :element-type '(unsigned-byte 8)))
        (n 10))
    (setf (aref arr 0) 114) ; NEW_REFERENCE_EXT
    (setf (aref arr 1) 0)
    (setf (aref arr 2) 3)
    (setf (aref arr 3) 82) ; atomref
    (setf (aref arr 4) node) ; atomref-index
    (setf (aref arr 5) creation)
    (setf (aref arr 6)  0) ; first ID word
    (setf (aref arr 7)  0)
    (setf (aref arr 8)  0)
    (setf (aref arr 9) id)
    (loop repeat (* 2 4) do ; fill in the rest of ID
      (setf (aref arr n) 0)
      (incf n))
    arr))

(defun erl-encode-pid (node id serial creation)
  (let ((arr (make-array 12 :element-type '(unsigned-byte 8))))
    (setf (aref arr 0) 103) ; PID_EXT
    (setf (aref arr 1) 82) ; atomref
    (setf (aref arr 2) node) ; atomref-index

    (buf-32bit-set arr 3 id)
    (buf-32bit-set arr 7 serial)
    (setf (aref arr 11) creation)
    arr))

(defun erl-encode-list (elements)
  (let ((arr (make-array 128 :fill-pointer 5 :adjustable t)))
    (labels ((grow (len)
               (let ((alen (length arr))
                     (f (fill-pointer arr)))
                 (when (>= (+ f len) alen) ; need to expand array
                   (adjust-array arr (+ alen len) :fill-pointer f))))
             (set-4 (x)
               (grow 4)
               (let ((f (fill-pointer arr)))
                 (setf (fill-pointer arr) (+ f 4))
                 (buf-32bit-set arr f x)))
             (set-2 (x)
               (grow 2)
               (let ((f (fill-pointer arr)))
                 (setf (fill-pointer arr) (+ f 2))
                 (buf-16bit-set arr f x)))
             (set-1 (x)
               (vector-push-extend x arr))
             (encode (item)
               (cond
                 ((integerp item)
                   (set-1 #x62) ; INTEGER_EXT
                   (set-4 item))
                 ((stringp item)
                   (set-1 #x6b) ; STRING_EXT
                   (set-2 (length item)) ; length of string
                   (loop for i from 0 below (length item) do
                     (set-1 (char-code (aref item i)))))
                 ((not item) ; encode a NIL into an empty string, which in erlang is equal to []
                   (set-1 #x6b) ; STRING_EXT
                   (set-2 0)) ; zero length string
                 ((vectorp item)
                   (set-1 104) ; SMALL_TUPLE_EXT
                   (set-1 (length item)) ; arity
                   (loop for x across item do (encode x)))
                 ((keywordp item)
                   (let* ((str (string-downcase (string item)))
                          (len (length str)))
                     (set-1 #x64) ; ATOM_EXT
                     (set-2 len)  ; length of atom
                     (loop for i from 0 below len do
                       (set-1 (char-code (aref str i))))))
                 (t (error "Unknown element to encode: ~s" item)))))
      (loop for item in elements do
        (encode item))
      (set-1 #x6a) ; Tail
      (setf (aref arr 0) #x6c) ; LIST_EXT
      (setf (aref arr 1) 0) ; higher 16bit of 32bit length
      (setf (aref arr 2) 0)
      (buf-16bit-set arr 3 (length elements)) ; number of elements in list
      arr)))

(defun erl-encode-atomref (num)
  (let ((arr (make-array 2 :element-type '(unsigned-byte 8))))
    (setf (aref arr 0) #x52)
    (setf (aref arr 1) num)
    arr))

(defun erl-distheader-decode-message (erl aarr buf n)
  (declare (ignore erl))
  (let ()
    (L "< decoding message at ~s, buflen ~s" n (length buf))
    (destructuring-bind (msg . n) (erl-decode-binary-term aarr buf n)
      (assert (arrayp msg))
      (L "< msg: ~s, n: ~s" msg n)
      msg)))

(defun erl-distheader (erl buf)
  (let ((pdulen (buf-32bit buf 0))
        (numofatoms (aref buf (+ 2)))
        numflags aarr atomlenbytes n)
    (L "< distheader: size ~s" pdulen)
    (setf numflags (truncate (if (evenp numofatoms)
                               (1+ (/ numofatoms 2))
                               (+ 0.5 (/ numofatoms 2)))))
    (when (and (= (aref buf 0) 131)
               (= (aref buf 1) 68))
      (L "< found distribution header, num of atomcacherefs ~a" numofatoms)
      (L "< number of flag bytes ~s" numflags)
      (setf aarr (make-array numofatoms)); atomcacherefs used in this distheader
      (let ((flagn 0))
        (flet ((set-aarr (b)
                 (L "< newbit+segment index: ~s" b)
                 (setf (aref aarr flagn) b)
                 (incf flagn)))
          (loop for i from 0 below numflags do
            (let* ((flagbyte (aref buf (+ i 3)))
                   (hi (ldb (byte 4 4) flagbyte)) ; high nibble
                   (lo (ldb (byte 4 0) flagbyte)) ; low  nibble
                   bb)
              (L "< ~a/~a flag byte ~x~x" flagn numofatoms hi lo)
              (setf bb lo)
              (cond
                ((< flagn numofatoms) (set-aarr bb))
                (t (if (logbitp 0 hi) (setf atomlenbytes t))
                   (L "< 2atomwide lo")
                   (return)))
              (setf bb hi)
              (cond
                ((< flagn numofatoms) (set-aarr bb))
                (t (if (logbitp 0 hi) (setf atomlenbytes t))
                   (L "< 2atomwide hi")
                   (return)))))))
      (L "< aarr: ~x" aarr)
      ; reading each atomcacheref
      (setf n (+ 3 numflags))
      (let (aidx alen
            (cache (erl-state-atom-cache erl))) ; current cache
        (loop for idx from 0 repeat numofatoms do
          (setf aidx (aref buf n)) (incf n)
          (let* ((bits (aref aarr idx))
                 (cidx (logior (ash (logand 7 bits) 8) aidx)))
            (when (logbitp 3 bits) ; NewCacheEntryFlag
              (setf alen (aref buf n)) (incf n)
              (setf (aref cache cidx) (buf2str buf n alen))
              (incf n alen)
              (L "< storing new atom at index ~x, str ~s" cidx (aref cache cidx)))
            (L "< writing to atomcacheref ~s => ~s" idx (aref cache cidx))
            (setf (aref aarr idx) (aref cache cidx))))
        ;(L "< decoding CMSG at ~s~%buf: ~x" n buf)
        (destructuring-bind (cmsg . n) (erl-decode-binary-term aarr buf n)
          (assert (arrayp cmsg))
          (let ((type (aref cmsg 0)))
            (cond
              ((= type 6) ; cmsg = {6, FromPid, Cookie, ToName}
                (L "< REG_SEND: ~s" cmsg)
                (list :reg-send (erl-distheader-decode-message erl aarr buf n)))
              ((= type 19) ; cmsg = {19, FromPid, ToProc, Ref}
                (L "< MONITOR_P: ~s" cmsg)
                (list :monitor cmsg))
              ((= type 2) ; SEND
                (L "< SEND cmsg: ~x" cmsg)
                (list :send (erl-distheader-decode-message erl aarr buf n)))
              (t (error "unknown control-message ~s" type)))))))))

(defun erl-handshake2 (erl socket digest)
  (declare (ignore erl))
  (let ((buf (make-pdu (list '16bit
                             (char-code #\r)
                             1 2 3 4 ; challenge
                             digest))))
    (erl-send-req socket buf)
    (destructuring-bind (buf . len) (erl-recv-16bit-pdu socket)
      (L "our chall-resp: ~s, ~s" len buf)
      (let ()
        (L "2 buflen: ~a" len)
        (when (= (aref buf 0) 97) ; 'a' tag
          (L "answer tag") ; skip checking the digest
          (assert (= len 17))))))) ; no more data to read

(defun erl-handshake (erl socket)
  (destructuring-bind (buf . len) (erl-recv-16bit-pdu socket)
    (L "got another answer: ~s, ~s" len buf)
    (let ((buflen (buf-16bit buf 0)))
      (L "buflen: ~a" buflen)
      (cond
        ((= (aref buf 0) 110) ; 'n' send_challenge
          (let* ((version (buf-16bit buf 1))
                 (chall   (format nil "~a" (buf-32bit buf 7)))
                 (cookie (erl-state-cookie erl))
                 (arr (make-array (+ (length cookie) (length chall)) :element-type '(unsigned-byte 8))))
            (assert (= version 5))
            (L "challenge: ~s" chall)
            (loop for i from 0 for a across (concatenate 'string cookie chall) do
              (setf (aref arr i) (char-code a)))
            (setf arr (sb-md5:md5sum-sequence arr))
            (erl-handshake2 erl socket arr)))
        (t nil)))))

(defun erl-connect (erl portno)
  (assert (not (erl-state-bar erl)))
  (let ((socket (setf (erl-state-bar erl) (make-socket :tcp)))
        (name (erl-state-name erl)))
    (L "connecting to remote node")
    (socket-connect socket #(127 0 0 1) portno)
    (L "connected to remote node")
    (let ((buf (make-pdu (list '16bit
                         (char-code #\n) ; message tag
                         0 5 ; version
                         0 3 #x7f #xfd ; flag (see lib/kernel/include/dist.hrl)
                         name))))
      (erl-send-req socket buf)
      (destructuring-bind (buf . len) (erl-recv-16bit-pdu socket)
        (L "got answer: ~s, ~s" len buf)
        (cond
          ((= (aref buf 0) 115) ; 's' tag
            (let ((arr (make-array len :element-type 'character)))
              (loop for i from 0 below len do
                (setf (aref arr i) (code-char (aref buf i))))
              (L "connection response: ~s" arr)
              (erl-handshake erl socket)
              t))
          (t
            (L "bad reply: tag=~s" (aref buf 2))
            (socket-close (erl-state-bar erl))
            nil))))))

(defun erl-disconnect (erl)
  (let ((socket (erl-state-bar erl)))
    (socket-close socket)
    (setf (erl-state-bar erl) nil)))

(defun erl-recv-packet (erl)
  (destructuring-bind (buf . len) (erl-recv-32bit-pdu (erl-state-bar erl))
    (when (> len 0)
      (assert (and (= (aref buf 0) 131) (= (aref buf 1) 68)))
      (L "--------- parsing distheader -------------")
      (erl-distheader erl buf))))

; test, send a MONITOR_P
(defun erl-monitor (erl)
  (let ((buf (make-pdu32 (list '32bit ; buffer length
   131 68 ; magic
   2 ; numberofatoms
   #xfe #x00 ; atomsflags
   ; atomcacherefs
   #xde   #x08   (erl-state-name erl) ; (segment, length, atomstring)
   #xc2   #x03   "rex"
   ; control message
   (erl-encode-tuple
     #(#x61 #x13) ; small int
     (erl-encode-pid 0 #x27 0 1)
     (erl-encode-atomref 1)
     (erl-encode-newref 0 48 3))))))
    (L "> Sending MONITOR_P")
    (erl-send-req32 (erl-state-bar erl) buf)))

(defun erl-demonitor (erl)
  (let ((buf (make-pdu32 (list '32bit ; buffer length
   131 68 ; magic, distheader
   2 ; numberofatoms
   #x76 #x00 ; atomsflags
   ; atomcacherefs
   #xde
   #xc2
   ; control message
   (erl-encode-tuple
     #(#x61 20) ; small int
     (erl-encode-pid 0 #x27 0 1)
     (erl-encode-atomref 1)
     (erl-encode-newref 0 48 3))))))
    (L "> Sending DEMONITOR_P")
    (erl-send-req32 (erl-state-bar erl) buf)))

(defun erl-req_send (erl modname funname args)
;00 00 00 89 pdulen
  (let ((buf (make-pdu32 (list '32bit ; buffer length
   131 68 ; magic
   7 ; numberofatoms
   #x87 #xa6 #x8a #x09 ; atomsflags
   #xc2 ; atomcacheref-index
   #x05 #x00 
   #xde
   #xc4 (length funname) funname
   #xf3 (length modname) modname
   #x0a #x04 "call"
   #xd8 #x09 "$gen_call"
   ; control-message
   (erl-encode-tuple
     6 ; small-integer #(#x61 #x06)
     (erl-encode-pid 2 #x20 0 1)
     (erl-encode-atomref 1)
     (erl-encode-atomref 0))
   ; message
   (erl-encode-tuple
     (erl-encode-atomref 6)
     (erl-encode-tuple
       (erl-encode-pid 2 #x27 0 1)
       (erl-encode-newref 2 48 1))
     (erl-encode-tuple
       (erl-encode-atomref 5)
       (erl-encode-atomref 4)
       (erl-encode-atomref 3)
       (cond
         ((listp args)
           (erl-encode-list args))
         (t
           (error "unknown argument type ~s" args)))
       (erl-encode-pid 2 #x27 0 1)))))))
    (L "> Sending REQ_SEND")
    ;(L "> pdu: ~x" buf)
    (erl-send-req32 (erl-state-bar erl) buf)))

(defun erl-start-node (name cookie)
  (let ((erl (erl-dist-init :name name
                            :cookie cookie)))
    (erl-epmd-connect erl)
    (assert (erl-state-epmd erl)) ; check we got the connection socket
    (setf (erl-state-creation erl) (erl-epmd-alive erl))
    (assert (numberp (erl-state-creation erl)))
    erl))

(defun erl-stop-node (erl)
  ; close any connection to other nodes (erl-disconnect erl-state-bar)
  (erl-epmd-close erl))

(defun erl-connect-node (erl nodename)
  (let ((portno (erl-epmd-nodename (make-array 1) 0 erl nodename)))
    (if portno (erl-connect erl portno))))

(defun erl-disconnect-node (erl nodename)
  (declare (ignore nodename))
  (erl-disconnect erl))

(defun erl-message-node (erl msg)
  (let (ret)
    (erl-monitor erl)
    (apply #'erl-req_send (list* erl msg))
    (loop for i from 0 below 10 do ; give up after this many tries
      (if (= i 9) (return-from erl-message-node :error))
      ;(unless (socket-open-p (erl-state-bar erl)) (return)) ; not reliable FIX, check this by forcing a BAD-RPC message from remote erlang, which will TCP-FIN the connection
      (let ((res (erl-recv-packet erl)))
        (when (eq (car res) :send)
          ; FIX: we should verify the pid at aref=0 is ours
          (setf ret (aref (second res) 1))
          (return))))
    (erl-demonitor erl)
     ret))
