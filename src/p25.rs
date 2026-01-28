// ./problems/list_nat_append_inj_1.smt2

/*
; Injectivity of append
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(prove
  (par (a)
    (forall ((xs (list a)) (ys (list a)) (zs (list a)))
      (=> (= (++ xs zs) (++ ys zs)) (= xs ys)))))
*/

// Note: I think this is a duplicate of p8

#[ravencheck::check_module]
#[allow(dead_code)]
mod p25 {
  #[import]
  use crate::list::linked_list::*;

  #[annotate_multi]
  #[for_values(xs: LinkedList, ys: LinkedList, zs: LinkedList)]
  fn foo() -> bool {
    implies(
      append(xs, zs) == append(ys, zs),
      xs == ys
    )
  }
}
