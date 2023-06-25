- Code clean
- Documentation
- Remove seq/sid interface : was replaced by debug\_id
- Remove backpressure : add second itch output interface and demux aixs between them to guaranty 
    alignement, this will involve a significant reworking of the mold module, as such little
    additional work will be performed on the current rtl as most of it will be discarded.

