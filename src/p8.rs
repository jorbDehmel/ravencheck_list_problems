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
  use crate::poly_list::poly_linked_list::*;

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[induct(xs: LinkedList<T>, ys: LinkedList<T>, zs: LinkedList<T>)]
  fn injectivity_of_append<T>(xs: LinkedList<T>, ys: LinkedList<T>, zs: LinkedList<T>) -> bool {
    implies(
      append::<T>(xs, zs) == append::<T>(ys, zs),
      xs == ys
    )
  }
}
