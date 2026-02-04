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
  use crate::poly_list::poly_linked_list::*;

  #[import]
  use crate::nat::nat::*;

  // Needed because ravencheck doesn't know about Option<T> and
  // we can't simply ensure that some UNDEFINED exists in T
  #[define]
  #[derive(PartialEq, Clone)]
  enum MyOpt<T> {
    Some(T),
    None
  }

  #[define]
  fn is_eq<T: PartialEq>(x: T, y: MyOpt<T>) -> bool {
    match y {
      MyOpt::<T>::None => false,
      MyOpt::<T>::Some(val) => x == val
    }
  }

  #[define]
  #[recursive]
  fn at<T: PartialEq + Clone>(x: LinkedList<T>, y: Nat) -> MyOpt<T> {
    match x {
      LinkedList::<T>::Nil => MyOpt::<T>::None,
      LinkedList::<T>::Cons(z, x2) => match y {
        Nat::Z => MyOpt::<T>::Some(z),
        Nat::S(x3) => at::<T>(*x2, *x3)
      }
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn f<T: PartialEq + Clone>(x: T, xs: LinkedList<T>) -> bool {
    implies(
      elem::<T>(x, xs),
      exists(|y: Nat| {
        is_eq::<T>(x, at::<T>(xs, y))
      })
    )
  }
}
