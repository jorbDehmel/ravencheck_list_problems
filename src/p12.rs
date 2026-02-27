// ./problems/list_count_nub.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  filter
  (par (a) (((p (=> a Bool)) (x (list a))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xs) (ite (@ p y) (cons y (filter p xs)) (filter p xs))))))
(define-fun-rec
  nubBy
  (par (a) (((x (=> a (=> a Bool))) (y (list a))) (list a)))
  (match y
    ((nil (_ nil a))
     ((cons z xs)
      (cons z
        (nubBy x (filter (lambda ((y2 a)) (not (@ (@ x z) y2))) xs)))))))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  count
  (par (a) (((x a) (y (list a))) Int))
  (match y
    ((nil 0)
     ((cons z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=> (elem x xs)
        (= (count x (nubBy (lambda ((y a)) (lambda ((z a)) (= y z))) xs))
          1)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p12 {
  #[import]
  use crate::poly_list::poly_linked_list::*;

  #[define]
  #[derive(PartialEq, Clone)]
  enum Int {
    P,
    N,
    S(Box<Int>)
  }

  #[assume]
  fn pm_zero() -> bool {
    Int::N == Int::P
  }

  #[define]
  #[recursive]
  fn elem<T: PartialEq>(x: T, y: LinkedList<T>) -> bool {
    match y {
      LinkedList::<T>::Nil => false,
      LinkedList::<T>::Cons(z, xs) => z == x || elem::<T>(x, *xs)
    }
  }

  #[define]
  #[recursive]
  fn count<A: PartialEq>(x: A, y: LinkedList<A>) -> Int {
    match y {
      LinkedList::<A>::Nil => Int::P,
      LinkedList::<A>::Cons(z, ys) => if x == z {
        Int::S(Box::new(count::<A>(x, *ys)))
      } else {
        count::<A>(x, *ys)
      }
    }
  }

  #[define]
  #[recursive]
  #[total]
  fn filter<A: PartialEq + Clone, F: Fn(A) -> bool>(p: F, x: LinkedList<A>) -> LinkedList<A> {
    match x {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(y, xs) =>
        if p(y.clone()) {
          LinkedList::<A>::Cons(
            y,
            Box::new(
              filter::<A, F>(p, *xs)
            )
          )
        } else {
          filter::<A, F>(p, *xs)
        }
    }
  }

  #[define]
  #[recursive]
  #[total]
  fn nub_by<A: PartialEq + Clone, F2: Fn(A) -> bool, F: Fn(A) -> F2 + Clone>(x: F, y: LinkedList<A>) -> LinkedList<A> {
    match y {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(z, xs) => LinkedList::Cons(
        z.clone(),
        Box::new(nub_by(
          x.clone(),
          filter(
            |y2: A| {
              !x(z.clone())(y2)
            },
            *xs
          )
        ))
      )
    }
  }

  /*
  Non-thunk in Force position????
  IDK what that means
  */
  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p12<A: PartialEq>(x: A) -> bool {
    implies(
      elem::<A>(x, xs),
      count(
        x,
        nub_by(
          |y: A| {
            |z: A| {
              y == z
            }
          },
          xs
        )
      ) == Int::S(Int::P)
    )
  }
}
