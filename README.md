# proop
Protocol Octopussy

Gränssnitt för att flytta data och meddelanden över nätverket och mellan processer.
Interface to move data/messages over network / IPC.
```
   +-----------+------+---------+
   | ASN.1 BER | JSON | Erlang  |
   +-----+-----+------+---------+
   | udp | tcp | http/websocket |
   +-----+-----+----------------+
```

