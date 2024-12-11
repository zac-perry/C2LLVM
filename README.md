# CSEM 
CESM reads a C program (actually a subset of C) from its standard input and compiles it into LLVM intermediate representation (IR) on its standard output.

### Supported operations (todo) 


### How to run / compile (todo) 


### BIG CONFIG NOTES: 
- I had to change a couple things for this to actually compile and run on MacOS (the hydra machine was painfully slow) 
    - commented out #Include <malloc.h>, since this is included in a different header file on mac? (sym.c)
    - Updated makefile to use different sed command -> added an additional '' for it to work on mac
    - Also, updated the 'LIBS: ' part of the makefile and include my path for lncurses and lunwind instead of ltinfo, since that's a linux thing.

- Just be aware that when this is tested on a linux machine, this is what i need to change back
