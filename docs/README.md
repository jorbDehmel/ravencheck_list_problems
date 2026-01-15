
# `ravencheck` Linked-List Benchmarks

Jordan Dehmel, Spring '26

## About

This repo documents an independent study taking place in Spring
2026 at CU Boulder in the CUPLV lab.

The files of `../problems` are copied directly from the TIP
benchmark set. They are used without permission. The associated
license can be found in the first half of `./LICENSE`.

## Abstract

Existing work has created `ravencheck`, an axiomatic Rust
verification system. One benchmark for such systems is TIP (Tons
of Inductive Problems), a subset of which describe linked-list
behaviors. To evaluate `ravencheck` on these, list axioms must be
derived. This work would implement these problems and evaluate
`ravencheck` on them.

## Learning objectives and outcomes

- Axiomatic system development
- Lemma development
- Familiarity with `ravencheck` and TIP

## Assignments

- 1/16/26: Get at least one benchmark problem working
- 2/27/26: Get at least half the benchmark problems working
- 4/17/19: Draft report due
- 4/24/26: Final report due

Interpolating:
- 1/16/26 (requirement): 1
- 1/23/26: 4
- 1/30/26: 7
- 2/06/26: 11
- 2/13/26: 15
- 2/20/26: 19
- 2/27/26 (requirement): 23
- 3/06/26: 27
- 3/13/26 (break): 31
- 3/20/26: 35
- 3/27/26: 39
- 4/03/26: 42
- 4/10/26: 44
- 4/17/26 (requirement): 46
- 4/24/26 (end of semester)

Expect to do between 3-4 problems per week.

## Resources

- [ravencheck](https://github.com/cuplv/ravencheck)
- [TIP](https://github.com/tip-org/benchmarks)
- [TIP format](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2017-07-18.pdf)
- [CVC5 SMT solver](https://cvc5.github.io/)

## Final Product

Report detailing the implementation process and summarizing
`ravencheck`'s performance. Also, a git repo implementing
the axioms and demonstrating benchmark completion.
