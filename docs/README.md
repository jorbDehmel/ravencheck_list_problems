
# `ravencheck` Linked-List Benchmarks

Jordan Dehmel, Spring '26

## About

This repo documents an independent study taking place in Spring
2026 at CU Boulder in the CUPLV lab.

The files of `../problems` are copied directly from the TIP
benchmark set. They are used without permission. The associated
license can be found in the first half of `../LICENSE`.

## Final summary (April 24, '26)

I finished 9 problems. Problem 46 may be possible, but I was
not able to complete it in time. Implementing lemmas based on
a lean proof of the problem was insufficient. The remaining 36
problems either use currently unsupported features or I suspect
to be impossible to encode. The maximum number of lemmas for a
problem was 12, but most completed problems used zero lemmas.
Please see `./progress.md` for more details. Overall, I logged
81.5 hours, well in-line with the required 80 hours of work.
This is a conservative estimate, I also spent a lot of unlogged
time thinking about the problems, reading, and learning
techniques.

When I wrote the goals, I did not realize there were 46
problems: I thought there would be around 10 or 15. Therefore,
my goals of "complete half / all the problems" were always
doomed to fail. That being said, I have merged all the completed
work and documentation to the main TIP repo and therefore have
completed the stated goals of the independent study.

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
- [TIP format](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2017-07-18.pdf)
- [CVC5 SMT solver](https://cvc5.github.io/)

## Final Product

Report detailing the implementation process and summarizing
`ravencheck`'s performance. Also, a git repo implementing
the axioms and demonstrating benchmark completion.
