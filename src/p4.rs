/*
// ./problems/list_PairUnpair.smt2
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  unpair
  (par (a) (((x (list (pair a a)))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xys)
      (match y (((pair2 z y2) (cons z (cons y2 (unpair xys))))))))))
(define-fun-rec
  pairs
  (par (b) (((x (list b))) (list (pair b b))))
  (match x
    ((nil (_ nil (pair b b)))
     ((cons y z)
      (match z
        ((nil (_ nil (pair b b)))
         ((cons y2 xs) (cons (pair2 y y2) (pairs xs)))))))))
(define-fun-rec
  length
  (par (a) (((x (list a))) Int))
  (match x
    ((nil 0)
     ((cons y l) (+ 1 (length l))))))
(prove
  (par (a)
    (forall ((xs (list a)))
      (=> (= (mod (length xs) 2) 0) (= (unpair (pairs xs)) xs)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p4 {
  #[import]
  use crate::poly_list::poly_linked_list::*;

  #[import]
  use crate::nat::nat::*;

  #[define]
  pub enum Pair<F, S> {
    Pair2(F, S)
  }

  #[define]
  #[recursive]
  fn pairs<T>(x: LinkedList<T>) -> LinkedList<Pair<T, T>> {
    match x {
      LinkedList::<T>::Nil => LinkedList::<Pair<T, T>>::Nil,
      LinkedList::<T>::Cons(y, z) => match *z {
        LinkedList::<T>::Nil => LinkedList::<Pair<T, T>>::Nil,
        LinkedList::<T>::Cons(y2, xs) =>
          LinkedList::<Pair<T, T>>::Cons(
            Pair::<T, T>::Pair2(y, y2),
            Box::new(
              pairs::<T>(*xs)
            )
          )
      }
    }
  }

  #[define]
  #[recursive]
  fn unpair<T>(x: LinkedList<Pair<T, T>>) -> LinkedList<T> {
    match x {
      LinkedList::<Pair<T, T>>::Nil => LinkedList::<T>::Nil,
      LinkedList::<Pair<T, T>>::Cons(y, xys) => match y {
        Pair::<T, T>::Pair2(z, y2) => LinkedList::<T>::Cons(
          z,
          Box::new(
            LinkedList::<T>::Cons(y2,
              Box::new(unpair::<T>(*xys))
            )
          )
        )
      }
    }
  }

  #[define]
  #[recursive]
  fn length<T>(x: LinkedList<T>) -> Nat {
    match x {
      LinkedList::<T>::Nil => Nat::Z,
      LinkedList::<T>::Cons(_data, l) => Nat::S(
        Box::new(length::<T>(*l))
      )
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn pair_unpair<T>(xs: LinkedList<T>) -> bool {
    implies(
      is_even(length::<T>(xs)),
      unpair::<T>(pairs::<T>(xs)) == xs
    )
  }
}
