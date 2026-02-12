// ./problems/list_deleteAll_count.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  deleteBy
  (par (a) (((x (=> a (=> a Bool))) (y a) (z (list a))) (list a)))
  (match z
    ((nil (_ nil a))
     ((cons y2 ys)
      (ite (@ (@ x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  deleteAll
  (par (a) (((x a) (y (list a))) (list a)))
  (match y
    ((nil (_ nil a))
     ((cons z ys)
      (ite (= x z) (deleteAll x ys) (cons z (deleteAll x ys)))))))
(define-fun-rec
  count
  (par (a) (((x a) (y (list a))) Int))
  (match y
    ((nil 0)
     ((cons z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=>
        (= (deleteAll x xs)
          (deleteBy (lambda ((y a)) (lambda ((z a)) (= y z))) x xs))
        (<= (count x xs) 1)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p13 {
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
  fn delete_all<A: PartialEq + Clone>(x: A, y: LinkedList<A>) -> LinkedList<A> {
    match y {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(z, ys) => if x == z {
        delete_all(x, *ys)
      } else {
        LinkedList::<A>::Cons(z, Box::new(delete_all(x, *ys)))
      }
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p13<A: PartialEq + Clone>(x: A, xs: LinkedList<A>) -> bool {
    implies(
      deleteAll(x, xs)
      ==
      deleteBy(
        |y: A| {
          |z: A| {
            y == z
          }
        },
        x,
        xs
      ),
      le(
        count::<A>(x, xs),
        Int::S(Int::P)
      )
    )
  }
}
