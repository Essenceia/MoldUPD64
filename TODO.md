- Documentation
- tb : msg len sent over 2 different axi payloads
- Optional feature defines rework : remove present sid and seq flops if needer miss detection 
    or transmission alongside msg are selected
- Fix endianness 
- FSM bug : no transition between msg valid -> header, need to pass by invalid state
- FSM bug : no overlap of header receive and purging last bytes of previous message still in flop when mold packets back to back ( no gap )
