
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

## Resources

- [ravencheck](https://github.com/cuplv/ravencheck)
- [TIP](https://github.com/tip-org/benchmarks)
- [CVC5 SMT solver](https://cvc5.github.io/)

## Final Product

Report detailing the implementation process and summarizing
`ravencheck`'s performance. Also, a git repo implementing
the axioms and demonstrating benchmark completion.
