// ./problems/list_nat_elem.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-const undefined (par (a) a))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  at
  (par (a) (((x (list a)) (y Nat)) a))
  (match x
    ((nil (_ undefined a))
     ((cons z x2)
      (match y
        ((zero z)
         ((succ x3) (at x2 x3))))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=> (elem x xs) (exists ((y Nat)) (= x (at xs y)))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p29 {
  #[import]
  use crate::list::linked_list::*;

  #[import]
  use crate::nat::nat::*;

  #[define]
  #[recursive]
  fn at(x: LinkedList, y: Nat) -> T {
    match x {
      LinkedList::Nil => UNDEFINED,
      LinkedList::Cons(z, x2) => match y {
        Nat::Z => z,
        Nat::S(x3) => at(*x2, *x3)
      }
    }
  }

  /*
  (prove
    (par (a)
      (forall ((x a) (xs (list a)))
        (=> (elem x xs) (exists ((y Nat)) (= x (at xs y)))))))
  */
  #[annotate_multi]
  #[for_values(x: T, xs: LinkedList)]
  #[for_call(elem(x, xs) => a)]
  fn f() -> bool {
    implies(
      a,
      exists(|y: Nat| {
        x == at(xs, y)
      })
    )
  }
}
