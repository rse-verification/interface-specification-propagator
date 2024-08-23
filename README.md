## FIT

[![Build Status](https://github.com/rse-verification/interface-specification-propagator/actions/workflows/build.yml/badge.svg?branch=master)](https://github.com/rse-verification/interface-specification-propagator/actions/workflows/build.yml)

Note that this plugin is in an experimental state.

This plugin is licensed under the GPL2 license, see license headers in source code files and the full license in the LICENSE file.

## PURPOSE

Semantic inference of auxiliary annotations in Frama-C. Frama-C is a software suite for analysis of C code. Importantly, Frama-C offers powerful value analysis and weakest precondition plugins over C source code. 

The purpose of this Frama-C plugin is to automatically provide contract components for interacting with the WP plugin of Frama-C.

## INSTALL

For Frama-C version 26 and onward:
```dune build @install && dune install```

To run the test suite: ```frama-c-ptests && dune build @ptests```

## USE

Annotate your program with ACSL postconditions / ensures clauses. Then our plugin creates auxiliary requires and assigns clauses.
There is limited support for also inferring some ensures clauses.

To run the plugin on file test.c, use the following command: ```frama-c -isp test.c```

##### Options ####

- Use ```-isp-print``` if you want the result to be printed.
- Use ```-isp-entry-point "function" ``` if you want to use a different function as the entry point for the analysis than the default ```main```.
                                             
## THEORY

We perform semantic annotation of a program. We provide requires clauses and assigns clauses. Requires clauses are 
synthesized from possible run-time exceptions, where the EVA plugin provides semantic discharging of always true preconditions.

Our method is based on the value analysis of Frama-C, which can bound the possible values of program variables at different program points. In this way we can proceed to deduce necessary pre-conditions to prevent run-time errors in a program, bound the return values of functions, and realize a memory model specification for a program automatically. Various heuristics are used and several approaches are tried, each realized as a separate Frama-C visitor.

For reference, these are the Master's thesis reports by Skantz and Manjikian:
- [Synthesis of annotations for partially automated deductive verification](https://kth.diva-portal.org/smash/get/diva2:1564101/FULLTEXT01.pdf) by Daniel Skantz
- [Improving the Synthesis of Annotations for Partially Automated Deductive Verification](https://kth.diva-portal.org/smash/get/diva2:1801578/FULLTEXT01.pdf) by Hovig Manjikian

## Limitations

C language limitations:
* Does currently not support complex expressions for indexing arrays, pointer arithmetic other than array indexing, nested pointers, or nested structs.
* Does not support programs with local static variables.

Regarding ACSL, support exist for requires, ensures, and assign clauses, as well as the behavior construct. Supports most ACSL operators (implication, nested inequalities, etc.), and the built-in predicates \valid and \valid_read.
Other ACSL constructs and built-ins than the above are generally not supported currently.

## Main authors
- Daniel Skantz
- Hovig Manjikian
