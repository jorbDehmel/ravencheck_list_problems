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
  fn pairs<T: PartialEq + Clone>(x: LinkedList<T>) -> LinkedList<Pair<T, T>> {
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
  fn unpair<T: PartialEq + Clone>(x: LinkedList<Pair<T, T>>) -> LinkedList<T> {
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
  #[total]
  fn length<T: PartialEq + Clone>(x: LinkedList<T>) -> Nat {
    match x {
      LinkedList::<T>::Nil => Nat::Z,
      LinkedList::<T>::Cons(_data, l) =>
        Nat::S(
          Box::new(length::<T>(*l))
        )
    }
  }

  #[assume]
  #[for_type(LinkedList<T> => <T>)]
  fn differing_lengths_never_equal<T: PartialEq + Clone>(a: LinkedList<T>, b: LinkedList<T>) -> bool {
    implies(
      length::<T>(a) != length::<T>(b),
      a != b
    )
  }

  #[define]
  #[recursive]
  fn are_eq<T: PartialEq + Clone>(x: LinkedList<T>, y: LinkedList<T>) -> bool {
    match x {
      LinkedList::<T>::Nil => match y {
        LinkedList::<T>::Nil => true,
        LinkedList::<T>::Cons(_y_data, _y_next) => false
      },
      LinkedList::<T>::Cons(x_data, x_next) => match y {
        LinkedList::<T>::Cons(y_data, y_next) =>
          (x_data == y_data) && are_eq::<T>(*x_next, *y_next),
        LinkedList::<T>::Nil => false
      }
    }
  }

  #[assume]
  #[for_type(LinkedList<T> => <T>)]
  fn are_eq_def<T: PartialEq + Clone>(a: LinkedList<T>, b: LinkedList<T>) -> bool {
    implies(a == b, are_eq::<T>(a, b)) && implies(are_eq::<T>(a, b), a == b)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_1<T: PartialEq + Clone>() -> bool {
    length::<T>(LinkedList::<T>::Nil) == Nat::Z
  }

  #[annotate]
  #[induct(l: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_2<T: PartialEq + Clone>(t: T, l: LinkedList<T>) -> bool {
    let l_length = length::<T>(l);
    length::<T>(
      LinkedList::<T>::Cons(t, l)
    ) == Nat::S(l_length)
  }

  #[annotate]
  #[induct(l: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_3<T: PartialEq + Clone>(t1: T, t2: T, l: LinkedList<T>) -> bool {
    length::<T>(LinkedList::<T>::Cons(t1, l)) == length::<T>(LinkedList::<T>::Cons(t2, l))
  }

  #[annotate]
  #[induct(l: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_4<T: PartialEq + Clone>(l: LinkedList<T>) -> bool {
    length::<T>(l) == length::<T>(l.clone())
  }

  #[annotate]
  #[induct(l: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_5<T: PartialEq + Clone>(t: T, l: LinkedList<T>) -> bool {
    length::<T>(LinkedList::<T>::Cons(t, l)) != length::<T>(l)
  }

  #[annotate]
  #[induct(l: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_6<T: PartialEq + Clone>(t: T, l: LinkedList<T>) -> bool {
    LinkedList::<T>::Cons(t, l) != l
  }

  #[annotate]
  #[induct(l: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_7<T: PartialEq + Clone>(t: T, l: LinkedList<T>) -> bool {
    length::<T>(LinkedList::<T>::Cons(t, l)) != length::<T>(l)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_8<T: PartialEq + Clone>(t: T) -> bool {
    LinkedList::<T>::Cons(t, LinkedList::<T>::Nil) != LinkedList::<T>::Nil
  }

  #[annotate]
  #[induct(xs: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn pair_unpair<T: PartialEq + Clone>(xs: LinkedList<T>) -> bool {
    implies(
      is_even(length::<T>(xs)),
      unpair::<T>(pairs::<T>(xs)) == xs
    )
  }
}
