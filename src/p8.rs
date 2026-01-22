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

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p8 {
  #[import]
  use crate::list::linked_list::*;

  #[annotate_multi]
  #[for_values(xs: LinkedList, ys: LinkedList, zs: LinkedList)]
  #[for_call(append(xs, zs) => a)]
  #[for_call(append(ys, zs) => b)]
  fn injectivity_of_append() -> bool {
    implies(
      a == b,
      xs == ys
    )
  }
}
