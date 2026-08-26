## FIT

[![Build Status](https://github.com/rse-verification/interface-specification-propagator/actions/workflows/build.yml/badge.svg?branch=master)](https://github.com/rse-verification/interface-specification-propagator/actions/workflows/build.yml)

Note that this plugin is in an experimental state.

This plugin is licensed under the GPL2 license, see license headers in source code files and the full license in the LICENSE file.

## PURPOSE

Semantic inference of auxiliary annotations in Frama-C. Frama-C is a software suite for analysis of C code. Importantly, Frama-C offers powerful value analysis and weakest precondition plugins over C source code.

The purpose of this Frama-C plugin is to automatically provide contract components for interacting with the WP plugin of Frama-C.

## INSTALL

This plugin currently targets Frama-C 31.0, as declared in `dune-project`.

```sh
dune build @install
dune install
```

To run the test suite locally:

```sh
frama-c-ptests
dune build @ptests
```

## USE

ISP analyzes C programs with existing ACSL contracts and generates auxiliary ACSL annotations for Frama-C/WP.

Depending on the program shape, ISP may emit:

- `requires` clauses for Eva-derived value ranges
- `requires \valid_read(...)` and `requires \valid(...)`
- `requires \separated(...)` for multiple mutated pointer arguments
- `assigns` clauses for mutated globals and pointer targets
- Eva-derived range `ensures` clauses
- arithmetic safety preconditions for simple single pointer updates such as `*p = *p + 1`

These arithmetic safety clauses are preconditions only. ISP does not infer relational pointer postconditions such as `*p == \old(*p) + 1`.

To run the plugin on file `test.c`, use:

```sh
frama-c -isp test.c
```

##### Options ####

- Use ```-isp-print``` if you want the result to be printed.
- Use ```-isp-print-file out.c``` if you want the result to be printed to file ```out.c```.
- Use ```-isp-entry-point "function" ``` if you want to use a different function as the entry point for the analysis than the default ```main```.
- Use ```-isp-missing-helper-contracts``` to report functions that are reachable
  from contracted functions but do not have ACSL contracts themselves.
- Use ```-isp-missing-helper-contracts-json report.json``` to write that report
  as JSON for tools such as AutoDeduct.
                                             
## THEORY

We perform semantic annotation of a program. We provide requires clauses and assigns clauses. Requires clauses are synthesized from possible run-time exceptions, where the Eva plugin provides semantic discharging of always true preconditions.

Our method is based on the value analysis of Frama-C, which can bound the possible values of program variables at different program points. In this way we can proceed to deduce necessary pre-conditions to prevent run-time errors in a program, bound the return values of functions, and realize a memory model specification for a program automatically.

The implementation uses a Frama-C visitor to collect accessed and mutated globals, pointer argument usage, function argument ranges, and simple arithmetic pointer mutations. Emission modules then add ACSL clauses based on the collected state and Eva results.

## Architecture and module responsibilities

ISP has two related execution paths. The normal `-isp` path runs Eva and
propagates auxiliary ACSL annotations. The `-isp-missing-helper-contracts`
path builds a call graph and reports reachable functions that do not have ACSL
contracts. The JSON form of that report is consumed by tools such as
AutoDeduct.

```text
Frama-C input with ACSL contracts
  |
  +-- isp_main / isp_options
  |     |
  |     +-- -isp
  |     |     `-> isp_visitor + Eva
  |     |           `-> isp_local_states
  |     |                 `-> isp_emitters -> generated ACSL project/output
  |     |
  |     `-- -isp-missing-helper-contracts[-json]
  |           `-> isp_missing_helpers -> text/JSON report
```

The main source modules have the following responsibilities:

- `isp_main.ml`: Frama-C plug-in entry point; dispatches propagation and
  missing-helper reporting.
- `isp_options.ml`: registers the ISP-specific Frama-C options.
- `isp_visitor.ml`: traverses the Frama-C AST, uses Eva results, and starts
  annotation generation for each visited function.
- `isp_local_states.ml`: stores the temporary state collected during a visit,
  including global accesses, pointer arguments, and mutations.
- `isp_emitters.ml`: converts collected state and Eva values into ACSL
  `requires`, `ensures`, and `assigns` clauses.
- `isp_utils.ml` and `isp_lval.ml`: provide expression/lvalue conversion,
  comparison, array/struct, and ACSL-term helper functions.
- `isp_missing_helpers.ml`: builds the contract-reachability call graph and
  emits the text or JSON missing-helper report.

The generated annotations are placed in a Frama-C project created from the
visitor, or written to the requested output, so the original source is not
rewritten by the propagation path. WP can then use the generated ACSL during
deductive verification.

## Diagnostics and failure handling

ISP keeps Frama-C's normal warning and failure behaviour, but prefixes the
messages it owns with stable identifiers. This makes warnings searchable in
ptests and CI logs and distinguishes an intentionally unsupported construct
from an internal state failure.

| ID | Meaning | Typical action |
| --- | --- | --- |
| `ISP-W001` | Unsupported global or instruction construct | Review the generated annotations for the affected construct. |
| `ISP-W002` | Unreachable function or statement | Check the selected entry point and call graph. |
| `ISP-W003` | Unsupported pointer, dereference, or memory lvalue | Simplify the expression or review `assigns`/`ensures` clauses. |
| `ISP-W004` | Unsupported expression, type, or Eva term | Review the generated contract and the source expression. |
| `ISP-W005` | Loop, exception, or unspecified control flow is not covered | Supply loop invariants where needed and review the output. |
| `ISP-W006` | NaN or incomplete numeric range | Review the corresponding range contract. |
| `ISP-W007` | Eva cannot evaluate a pointer term | Review the generated contract; no clause is emitted for that term. |
| `ISP-W008` | Frama-C has no global access summary | Review the generated `assigns` clause. |
| `ISP-W009` | Arithmetic safety inference skipped for a repeatedly assigned lvalue | Add or review the necessary overflow/underflow preconditions manually. |
| `ISP-E001`-`ISP-E007` | Input construct cannot be converted or emitted | Inspect the input construct and the surrounding diagnostic. |
| `ISP-E008`-`ISP-E009` | Required visitor/Eva state is missing | Retry with the same input; report the diagnostic if it persists. |
| `ISP-E010` | An array is nested inside a struct during recursive field-offset expansion | ISP stops with a clear unsupported-input diagnostic; simplify the aggregate or review the contract manually. |
| `ISP-E011` | Eva cannot finitely resolve a direct variable array index, or resolving it would expand more than 1024 values | Constrain the index range or review the affected contract manually. |

Warnings do not make ISP abort, but they mean the generated specification may
be partial and must be reviewed before relying on it in WP. Fatal diagnostics
are reported through Frama-C's usual non-zero failure path, with the stable ID
included in the message. ISP does not assign a separate process exit-code
scheme; callers should use Frama-C's exit status together with these IDs.

The `ISP-E011` guard currently applies to direct lvalue index forms such as
`array[index]`. Casts, arithmetic index expressions, memory-based indices, and
variable indices deeper in an offset chain are not covered by this expansion
path. The 1024-value limit bounds generated-contract size; it does not check
that every Eva value is within the array's declared extent.

For reference, these are the Master's thesis reports by Skantz and Manjikian:
- [Synthesis of annotations for partially automated deductive verification](https://kth.diva-portal.org/smash/get/diva2:1564101/FULLTEXT01.pdf) by Daniel Skantz
- [Improving the Synthesis of Annotations for Partially Automated Deductive Verification](https://kth.diva-portal.org/smash/get/diva2:1801578/FULLTEXT01.pdf) by Hovig Manjikian

## Limitations

C language limitations:
* Does currently not support complex expressions for indexing arrays, pointer arithmetic other than array indexing, nested pointers, or nested structs.
* Recursive auxiliary annotation generation does not currently support arrays
  contained in struct fields. In particular, repeated aggregate paths such as
  `records[slot].f1[i].f2[j]` are outside the supported boundary. The merged
  enum-indexed struct support covers flat struct fields after an enum-indexed
  array access; it does not cover arbitrary nested `Field -> Index` paths.
* Does not support programs with local static variables.

Regarding ACSL, support exist for requires, ensures, and assign clauses, as well as the behavior construct. Supports most ACSL operators (implication, nested inequalities, etc.), and the built-in predicates \valid and \valid_read.
Other ACSL constructs and built-ins than the above are generally not supported currently.
