## FIT

Note that this plugin is in an experimental state.

## PURPOSE

Semantic inference of auxiliary annotations in Frama-C. Frama-C is a software suite for analysis of C code. Importantly, Frama-C offers powerful value analysis and weakest precondition plugins over C source code. 

The purpose of this Frama-C plugin is to automatically provide contract components for interacting with the WP plugin of Frama-C.

## INSTALL

* For Frama-C version 26 and onward:
```dune build @install && dune install```

## USE

Annotate your program with ACSL postconditions / ensures clauses. Then our plugin creates auxiliary requires and assigns clauses.
There is limited support for also inferring some ensures clauses.
                                             
## THEORY

We perform semantic annotation of a program. We provide requires clauses and assigns clauses. Requires clauses are 
synthesized from possible run-time exceptions, where the EVA plugin provides semantic discharging of always true preconditions.

Our method is based on the value analysis of Frama-C, which can bound the possible values of program variables at different program points. In this way we can proceed to deduce necessary pre-conditions to prevent run-time errors in a program, bound the return values of functions, and realize a memory model specification for a program automatically. Various heuristics are used and several approaches are tried, each realized as a separate Frama-C visitor.

## Main authors
- Daniel Skantz
- Hovig Manjikian