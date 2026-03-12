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
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum MyOpt<T> {
    Some(T),
    None
  }

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
  #[recursive]
  fn is_positive(x: Int) -> bool {
    match x {
      Int::S(previous) => match *previous.clone() {
        Int::P => true,
        Int::N => false,
        Int::S(_prev) => is_positive(*previous)
      },
      Int::P => false,
      Int::N => false
    }
  }

  // This only takes positives herein, but generally functions
  // to reduce the magnitude by 1, with a fixed point at 0.
  #[define]
  fn previous(x: Int) -> Int {
    match x {
      Int::S(p) => *p,
      Int::N => x,
      Int::P => x
    }
  }

  #[define]
  fn is_zero(x: Int) -> bool {
    match x {
      Int::P => true,
      Int::N => true,
      Int::S(_prev) => false
    }
  }

  #[define]
  #[recursive]
  pub fn elem<T: PartialEq>(x: T, y: LinkedList<T>) -> bool {
    match y {
      LinkedList::<T>::Nil => false,
      LinkedList::<T>::Cons(z, xs) =>
        z == x || elem::<T>(x, *xs)
    }
  }

  #[define]
  #[recursive]
  fn at<T: PartialEq + Clone>(x: LinkedList<T>, y: Int) -> MyOpt<T> {
    match x {
      LinkedList::<T>::Nil => MyOpt::<T>::None,
      LinkedList::<T>::Cons(z, x2) =>
        if is_zero(y.clone()) {
          MyOpt::<T>::Some(z)
        } else {
          if is_positive(y.clone()) {
            at::<T>(*x2, previous(y))
          } else {
            MyOpt::<T>::None
          }
        }
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn p14<T: PartialEq + Clone>(x: T) -> bool {
    implies(
      elem::<T>(x, xs),
      exists(|y: Int| {
        def_and_eq(
          at::<T>(xs, y),
          MyOpt::<T>::Some(x)
        )
      })
    )
  }
}
