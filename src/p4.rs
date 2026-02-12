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
#[add_solver_args("--produce-models")]
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
  #[total]
  fn pairs<T: PartialEq + Clone>(x: LinkedList<T>) -> LinkedList<Pair<T, T>> {
    match x {
      LinkedList::<T>::Nil => LinkedList::<Pair<T, T>>::Nil,
      LinkedList::<T>::Cons(cur_val, next) => match *next {
        LinkedList::<T>::Nil => LinkedList::<Pair<T, T>>::Nil,
        LinkedList::<T>::Cons(next_val, next_next) =>
          LinkedList::<Pair<T, T>>::Cons(
            Pair::<T, T>::Pair2(cur_val, next_val),
            Box::new(
              pairs::<T>(*next_next)
            )
          )
      }
    }
  }

  #[define]
  #[recursive]
  #[total]
  fn unpair<T: PartialEq + Clone>(x: LinkedList<Pair<T, T>>) -> LinkedList<T> {
    match x {
      LinkedList::<Pair<T, T>>::Nil => LinkedList::<T>::Nil,
      LinkedList::<Pair<T, T>>::Cons(data, next) => match data {
        Pair::<T, T>::Pair2(first, second) => LinkedList::<T>::Cons(
          first,
          Box::new(
            LinkedList::<T>::Cons(second,
              Box::new(unpair::<T>(*next))
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

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn pairs_nil_to_nil<T>() -> bool {
    pairs::<T>(LinkedList::<T>::Nil)
    == LinkedList::<Pair<T, T>>::Nil
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn pairs_single_to_nil<T>(t1: T) -> bool {
    pairs::<T>(
      LinkedList::<T>::Cons(
        t1,
        LinkedList::<T>::Nil
      )
    ) == LinkedList::<Pair<T, T>>::Nil
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn pairs_add_pair<T>(t1: T, t2: T) -> bool {
    pairs::<T>(
      LinkedList::<T>::Cons(
        t1,
        LinkedList::<T>::Cons(
          t2,
          LinkedList::<T>::Nil
        )
      )
    ) == LinkedList::<Pair<T, T>>::Cons(
      Pair::<T, T>::Pair2(t1, t2),
      LinkedList::<Pair<T, T>>::Nil
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn unpair_nil_to_nil<T>() -> bool {
    unpair::<T>(LinkedList::<Pair<T, T>>::Nil)
    == LinkedList::<T>::Nil
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn unpair_pair<T>(t1: T, t2: T) -> bool {
    unpair::<T>(LinkedList::<Pair<T, T>>::Cons(
      Pair::<T, T>::Pair2(t1, t2),
      LinkedList::<Pair<T, T>>::Nil
    )) == LinkedList::<T>::Cons(
      t1,
      LinkedList::<T>::Cons(
        t2,
        LinkedList::<T>::Nil
      )
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn sanity_check_1<T>(t1: T, t2: T) -> bool {
    pairs::<T>(
      LinkedList::<T>::Cons(t1, LinkedList::<T>::Cons(t2, l))
    ) == LinkedList::<Pair<T, T>>::Cons(
      Pair::<T, T>::Pair2(t1, t2),
      pairs::<T>(l)
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<Pair<T, T>>)]
  fn sanity_check_2<T>(t1: T, t2: T) -> bool {
    unpair::<T>(LinkedList::<Pair<T, T>>::Cons(
      Pair::<T, T>::Pair2(t1, t2),
      l
    ))
    ==
    LinkedList::<T>::Cons(t1, LinkedList::<T>::Cons(t2, unpair::<T>(l)))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_5<T>() -> bool {
    is_even(length::<T>(LinkedList::<T>::Nil))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn sanity_check_6<T>(t: T) -> bool {
    !is_even(length::<T>(LinkedList::<T>::Cons(t, LinkedList::<T>::Nil)))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn sanity_check_7<T>(t: T) -> bool {
    is_even(length::<T>(l)) ==
    !is_even(length::<T>(LinkedList::<T>::Cons(t, l)))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn sanity_check_8<T>(t: T) -> bool {
      !is_even(length::<T>(l)) ==
      is_even(length::<T>(LinkedList::<T>::Cons(t, l))
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn sanity_check_9<T>(t1: T, t2: T) -> bool {
    is_even(length::<T>(l)) ==
    is_even(
      length::<T>(
        LinkedList::<T>::Cons(
          t1,
          LinkedList::<T>::Cons(
            t2,
            l
          )
        )
      )
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn decompose_even_len_list<T>(t1: T, t2: T) -> bool {
    is_even(
      length::<T>(
        LinkedList::<T>::Cons(
          t1,
          Box::new(
            LinkedList::<T>::Cons(
              t2,
              Box::new(l)
            )
          )
        )
      )
    )
    ==
    is_even(length::<T>(l))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn pair_unpair_append_2<T>(t1: T, t2: T, l: LinkedList<T>) -> bool {
    (unpair::<T>(pairs::<T>(l)) == l)
    ==
    (
      unpair::<T>(
        pairs::<T>(
          LinkedList::<T>::Cons(
            t1,
            LinkedList::<T>::Cons(
              t2,
              l
            )
          )
        )
      ) == LinkedList::<T>::Cons(
        t1,
        LinkedList::<T>::Cons(
          t2,
          l
        )
      )
    )
  }

  #[annotate]
  #[inductive(xs: LinkedList<T>)]
  #[for_type(LinkedList<T> => <T>)]
  fn pair_unpair<T: PartialEq + Clone>() -> bool {
    implies(
      is_even(length::<T>(xs)),
      unpair::<T>(pairs::<T>(xs)) == xs
    )
  }
}
