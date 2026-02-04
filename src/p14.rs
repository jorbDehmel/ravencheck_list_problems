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
  use crate::poly_list::poly_linked_list::*;

  // Positive numbers are successors of P, negative numbers are
  // successors of N. Zero is the only number whose
  // representation is ambiguous: It can be either P or N.
  // Therefore, these two should be assumed to be equal. I was
  // going to use Z/S/P (zero, successor-of, predecessor-of),
  // but that would introduce way too much complexity for
  // equality (EG S(Z) == P(S(S(Z)))).
  #[define]
  #[derive(PartialEq, Clone)]
  enum Int {
    P,
    N,
    S(Box<Int>)
  }

  #[assume]
  fn plus_minus_zero_eq() -> bool {
    Int::P == Int::N
  }

  #[define]
  fn is_positive(x: Int) -> bool {
    match x {
      Int::S(previous) => match *previous {
        Int::P => true,
        Int::N => false,
        _ => is_positive(*previous)
      },
      _ => false
    }
  }

  // This only takes positives herein, but generally functions
  // to reduce the magnitude by 1, with a fixed point at 0.
  #[define]
  fn previous(x: Int) -> Int {
    match x {
      Int::S(p) => *p,
      _ => x
    }
  }

  #[define]
  fn is_zero(x: Int) -> bool {
    match x {
      Int::P => true,
      Int::N => true,
      _ => false
    }
  }

  // This is the same as 29, but with integers instead of nats

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
  fn at<T: PartialEq + Clone>(x: LinkedList<T>, y: Int) -> MyOpt<T> {
    match x {
      LinkedList::<T>::Nil => MyOpt::<T>::None,
      LinkedList::<T>::Cons(z, x2) =>
        // (ite (= y 0) z (ite (> y 0) (at x2 (- y 1)) (_ undefined a)
        if is_zero(y.clone()) {
          MyOpt::<T>::Some(z)
        } else {
          if is_positive(y.clone()) {
            at(*x2, previous(y))
          } else {
            MyOpt::<T>::None
          }
        }
    }
  }

  // (prove
  //   (par (a)
  //     (forall ((x a) (xs (list a)))
  //       (=> (elem x xs) (exists ((y Int)) (= x (at xs y)))))))
  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn f<T: PartialEq + Clone>(x: T, xs: LinkedList<T>) -> bool {
    implies(
      elem::<T>(x, xs),
      exists(|y: Int| {
        is_eq::<T>(x, at::<T>(xs, y))
      })
    )
  }
}
