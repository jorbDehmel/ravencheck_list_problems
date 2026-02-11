/*
// ./problems/list_SelectPermutations.smt2
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
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  (par (a) (((x (=> a (=> a Bool))) (y a) (z (list a))) (list a)))
  (match z
    ((nil (_ nil a))
     ((cons y2 ys)
      (ite (@ (@ x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  (par (a) (((x (list a)) (y (list a))) Bool))
  (match x
    ((nil
      (match y
        ((nil true)
         ((cons z x2) false))))
     ((cons x3 xs)
      (and (elem x3 y)
        (isPermutation xs
          (deleteBy (lambda ((x4 a)) (lambda ((x5 a)) (= x4 x5))) x3 y)))))))
(define-fun-rec
  all
  (par (a) (((p (=> a Bool)) (x (list a))) Bool))
  (match x
    ((nil true)
     ((cons y xs) (and (@ p y) (all p xs))))))
(prove
  (par (a)
    (forall ((xs (list a)))
      (all (lambda ((x (list a))) (isPermutation x xs))
        (formula (select2 xs))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p7 {
  #[import]
  use crate::poly_list::poly_linked_list::*;

  #[define]
  enum Pair<F, S> {
    Pair2(F, S)
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
  fn all<A>(p: fn(A) -> bool, x: LinkedList<A>) -> bool {
    match x {
      LinkedList::<A>::Nil => true,
      LinkedList::<A>::Cons(y, xs) => p(y) && all::<A>(p, *xs)
    }
  }

  #[define]
  #[recursive]
  fn delete_by<A: PartialEq + Clone>(x: fn(A, A) -> bool, y: A, z: LinkedList<A>) -> LinkedList<A> {
    match z {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(y2, ys) =>
        if x(y.clone(), y2.clone()) {
          *ys
        } else {
          LinkedList::<A>::Cons(y2, Box::new(delete_by::<A>(x, y, *ys)))
        }
    }
  }

  #[define]
  #[recursive]
  fn is_permutation<A: PartialEq + Clone>(x: LinkedList<A>, y: LinkedList<A>) -> bool {
    match x {
      LinkedList::<A>::Nil => match y {
        LinkedList::<A>::Nil => true,
        LinkedList::<A>::Cons(_z, _x2) => false
      },
      LinkedList::<A>::Cons(x3, xs) =>
        elem::<A>(x3.clone(), y.clone()) && is_permutation::<A>(
          *xs,
          delete_by::<A>(
            |x4: A, x5: A| {
              x4 == x5
            },
            x3,
            y
          )
        )
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[induct(xs: LinkedList<A>)]
  fn p7<A: PartialEq + Clone>(xs: LinkedList<A>) -> bool {
    all(
      |x: LinkedList<A>| {
        is_permutation(x, xs)
      },
      formula(select2(xs))
    )
  }
}
