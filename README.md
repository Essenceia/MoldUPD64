# MoldUPD64

RTL implementation of a MoldUPD64 receiver. 

## Limitiations

- Mold messages must be at least 6 bytes long.

- Missing session id gap has a maximum, can only detect if the 
  gap is less than `SID_GAP_MAX`.

## Assumptions 

- Next expected session id will only be incremented when an End-of-Sequence 
  packet is received and not by sequence counter overflow.

## Packet view

This code takes as input an AXI stream of the UPD payload and decapsulates the
multiple MoldUDP messages.

![MoldUDP packet!](doc/moldudp.png)

## Test bench

This reposity contains a small testbench, a more complete testbench is
available at the top level.

Run test :
```
make run
```

( Optional ) Run with `DEBUG` macro defined :
```
make run debug=1
```

Clean :
```
make clean
```

### Debug id

When the `DEBUG` macro is defined the `moldudp64` module output an
`debug_id_o` alongside each message. This signal is used to help 
track each message individually for debug.

This id is created by combining the session id and the sequence number.

By default the `DEBUG` macro is not defined.

## UDP : AXI stream 

This module accepts upd packets via an AXI stream interface, this module
is the slave. 

AXI interface :

```
// AXI stream interface from udp ethernet
input [63:0] upd_axis_tdata_i,
input [7:0]  upd_axis_tkeep_i,
input        upd_axis_tvalid_i,
input        upd_axis_tlast_i,
input        upd_axis_tuser_i,

output       upd_axis_tready_i, 
```

- `tvalid` : indicates that the master is driving a valid transfer.
    A transfer takes place when both `tvalid` and `tready` are asserted.

- `tready` : indicates that the slave can accept a transfer in the
    current cycle

- `tdata` : is the primary payload that is used to provide the data
    that is passing across the interface. The width of the data
    payload is an intger number of bytes.

- `tkeep` : is the byte qualifier that indicates whether the content
    of the associated byte of `tdata` is processed as part of the data stream.
    Associated bytes that have the `tkeep` byte qualifier deasserted
    are null bytes and can be removed from the data stream.

- `tlast` : indicates the boundary of a packet. / End-of-frame

- `tuser` : user defined / Bad frame (valid with `tlast` & `tvalid`)

## License

This code is licensed under CC BY-NC 4.0, to obtain a commercial license
reach out to the author .
