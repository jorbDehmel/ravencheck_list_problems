/*
// ./problems/list_SelectPermutations'.smt2
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  select
  (par (a)
    (((x a) (y (list (pair a (list a))))) (list (pair a (list a)))))
  (match y
    ((nil (_ nil (pair a (list a))))
     ((cons z x2)
      (match z
        (((pair2 y2 ys) (cons (pair2 y2 (cons x ys)) (select x x2)))))))))
(define-fun-rec
  select2
  (par (a) (((x (list a))) (list (pair a (list a)))))
  (match x
    ((nil (_ nil (pair a (list a))))
     ((cons y xs) (cons (pair2 y xs) (select y (select2 xs)))))))
(define-fun-rec
  formula
  (par (a) (((x (list (pair a (list a))))) (list (list a))))
  (match x
    ((nil (_ nil (list a)))
     ((cons y z)
      (match y (((pair2 y2 ys) (cons (cons y2 ys) (formula z)))))))))
(define-fun-rec
  count
  (par (a) (((x a) (y (list a))) Int))
  (match y
    ((nil 0)
     ((cons z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
(define-fun-rec
  all
  (par (a) (((p (=> a Bool)) (x (list a))) Bool))
  (match x
    ((nil true)
     ((cons y xs) (and (@ p y) (all p xs))))))
(prove
  (par (a)
    (forall ((xs (list a)) (z a))
      (all (lambda ((x (list a))) (= (count z xs) (count z x)))
        (formula (select2 xs))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p6 {
  #[import]
  use crate::poly_list::poly_linked_list::*;

  #[define]
  enum Pair<F, S> {
    Pair2(F, S)
  }

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
  fn select<T: PartialEq + Clone>(x: T, y: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match y {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(z, x2) =>
        match z {
          Pair::<T, LinkedList<T>>::Pair2(y2, ys) =>
            LinkedList::<Pair<T, LinkedList<T>>>::Cons(
              Pair::<T, LinkedList<T>>::Pair2(
                y2,
                LinkedList::<T>::Cons(x.clone(), Box::new(ys))
              ),
              Box::new(select::<T>(x, *x2))
            )
        }
    }
  }

  #[define]
  #[recursive]
  fn select2<T: PartialEq + Clone>(x: LinkedList<T>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match x {
      LinkedList::<T>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<T>::Cons(y, xs) =>
        LinkedList::<Pair<T, LinkedList<T>>>::Cons(
          Pair::<T, LinkedList<T>>::Pair2(y.clone(), *xs.clone()),
          Box::new(select::<T>(y, select2::<T>(*xs)))
        )
    }
  }

  #[define]
  #[recursive]
  fn formula<A>(x: LinkedList<Pair<A, LinkedList<A>>>) -> LinkedList<LinkedList<A>> {
    match x {
      LinkedList::<Pair<A, LinkedList<A>>>::Nil =>
        LinkedList::<LinkedList<A>>::Nil,
      LinkedList::<Pair<A, LinkedList<A>>>::Cons(y, z) =>
        match y {
          Pair::<A, LinkedList<A>>::Pair2(y2, ys) =>
            LinkedList::<LinkedList<A>>::Cons(
              LinkedList::<A>::Cons(y2, Box::new(ys)),
              Box::new(formula::<A>(*z))
            )
        }
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
  fn all<A>(p: fn(A) -> bool, x: LinkedList<A>) -> bool {
    match x {
      LinkedList::<A>::Nil => true,
      LinkedList::<A>::Cons(y, xs) => p(y) && all::<A>(p, *xs)
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  fn p6<A>(xs: LinkedList<A>, z: A) -> bool {
    all(|x: LinkedList<A>| {count(z, xs) == count(z, x)}, formula(select2(xs)))
  }
}
