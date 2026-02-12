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
  #[recursive]
  fn filter<A: PartialEq + Clone>(p: fn(A) -> bool, x: LinkedList<A>) -> LinkedList<A> {
    match x {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(y, xs) => if p(y.clone()) {
        LinkedList::Cons(y, Box::new(filter::<A>(p, *xs)))
      } else {
        filter(p, *xs)
      }
    }
  }

  // #[define]
  // #[recursive]
  // fn nub_by<A>(x: fn(A) -> fn(A) -> bool, y: LinkedList<A>) -> LinkedList<A> {
  //   match y {
  //     LinkedList::Nil => LinkedList::Nil,
  //     LinkedList::Cons(z, xs) => LinkedList::Cons(
  //       z,
  //       Box::new(nub_by(
  //         x,
  //         filter(
  //           |y2: A| {
  //             !x(z)(y2)
  //           },
  //           *xs
  //         )
  //       ))
  //     )
  //   }
  // }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  fn p12<A>(x: A, xs: LinkedList<A>) -> bool {
    implies(
      elem(x, xs),
      count(
        x,
        nub_by(
          |y: A| {
            |z: A| {
              y == z
            }
          }
        )
      ) == Nat::S(Nat::Z)
    )
  }
}
