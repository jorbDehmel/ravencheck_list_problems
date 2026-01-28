// ./problems/list_elem.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(declare-const undefined (par (a) a))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  at
  (par (a) (((x (list a)) (y Int)) a))
  (match x
    ((nil (_ undefined a))
     ((cons z x2)
      (ite (= y 0) z (ite (> y 0) (at x2 (- y 1)) (_ undefined a)))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=> (elem x xs) (exists ((y Int)) (= x (at xs y)))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p14 {
  #[import]
  use crate::list::linked_list::*;

  // This is the same as 29, but with integers instead of nats
}
