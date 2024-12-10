# CSEM 
CESM reads a C program (actually a subset of C) from its standard input and compiles it into LLVM intermediate representation (IR) on its standard output.


### Supported operations (todo) 


### How to run / compile (todo) 

## Development Notes
- Currently implementing required things for the first input
- Many of the functions are still not finished, will need to mainly finish backpatching, etc. 
- rewatch lectures if needed, provide good direction and way to think about everything
- [x] Input #1
- [x] Input #2
- [x] Input #3
- [x] Input #4
- [x] Input #5
- [x] Input #6
- [x] Input #7
- [ ] Input #8

# BIG CONFIG NOTES: 
- I had to change a couple things for this to actually compile and run on MacOS (the hydra machine was painfully slow) 
    - commented out #Include <malloc.h>, since this is included in a different header file on mac? (sym.c)
    - Updated makefile to use different sed command -> added an additional '' for it to work on mac
    - Also, updated the 'LIBS: ' part of the makefile and include my path for lncurses and lunwind instead of ltinfo, since that's a linux thing.

- Just be aware that when this is tested on a linux machine, this is what i need to change back

Notes
- id
    - If it doesn't exist, install into symbol table
    - package up as sem_record, pass to compiler
    - returns a semantic record that has a pointer to the symbol table entry for this identifier
    - semantic record keeps some type info

- for branching
    - m represents a label
    - n represents a goto

- doif
    - since everyhting has been parsed already...
    - just need to backpatch, using the true part of the conditional and the false part of the conditional 
    - since now, you just fill in the true and false branches :D

- backpatch
    - Takes a semantic records (produced by cexpr routine) 
    - Expecting a branch instr
    - successor - blocks you can go to in a branch (different places to jump to)

 backpatch
    - Takes a semantic records (produced by cexpr routine) 
- Expecting a branch instr
- successor - blocks you can go to in a branch (different places to jump to)



##### Input 2 TODO

- genstring done? 
    - Was calling with weird arguments, just pass string and its good now.
- exprs now
    - One issue i rant into: wasn't going to the end of the list before adding new args
    - As a result, a ton of them get overwritten 
    - Fixed, just loop to the end (linked list) fasion, add there.
- call now 
    - Look up the function in the lookup table to ensure it exists before calling 
    - get the function, add all args for it to a vector, then make a new node, with the LLVM function CreateCall()

##### Input 3 TODO
- rel > 
- ccand 
- rel == 
- ccor 
- n 
- doifelse
- backpatch
    - Added recursive call to backpatch the entire list of branch instructions
    - Without this, was only backpatching the first call, not the rest


##### Input 4 TODO
- ccnot
    - just return a node with the true and false swap, ez

##### Input 5 TODO
- set 
    - op2 
    - op1
    - opb
- indx
- dofor


NOTE: when debugging, found that when comparing types, you NEED TO USE &, as one record could have multiple types (T_ARRAY and T_INT for example) 
    - Use bitwise & to get the type


##### Input 6 todo
- docontinue
- do break
- Had to fix dowhile + dofor to handle these cases as well.


##### Input 7 todo
- dodo
    - was easy
- Add rest of the rel
- also had to add type conversion wtihin op2, i guess this doensn't always get called from set() so you still need to do it in op2.





