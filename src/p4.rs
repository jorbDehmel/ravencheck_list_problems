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

Note: I feel comfortable replacing "mod 2" with the "is_even"
predicate here, since "mod" is neither defined here nor the
thing we are testing.
- Jordan Dehmel

Lemmas: 12
Verification time: 2.29s
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p4 {
  #[define]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  pub enum Nat {
    Z,
    S(Box<Nat>)
  }

  #[define]
  pub enum Pair<F, S> {
    Pair2(F, S)
  }

  #[define]
  #[recursive]
  #[total]
  pub fn is_even(n: Nat) -> bool {
    match n {
      Nat::Z => true,
      Nat::S(m) => !is_even(*m)
    }
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

  //////////////////////////////////////////////////////////////
  /// Verification

  #[define]
  #[recursive]
  #[total]
  fn list_len_is_even<T: PartialEq + Clone>(l: LinkedList<T>) -> bool {
    match l {
      LinkedList::<T>::Nil => true, // len 0 is even
      LinkedList::<T>::Cons(_a, next) => match *next {
        LinkedList::<T>::Nil => false, // len 1 is odd
        LinkedList::<T>::Cons(_b, next_next) =>
          list_len_is_even::<T>(*next_next)
      }
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
  fn unpair_nil_to_nil<T>() -> bool {
    unpair::<T>(LinkedList::<Pair<T, T>>::Nil)
    == LinkedList::<T>::Nil
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn prepend_1_pair<T>(t1: T, t2: T) -> bool {
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
  fn pop_1_pair<T>(t1: T, t2: T) -> bool {
    unpair::<T>(LinkedList::<Pair<T, T>>::Cons(
      Pair::<T, T>::Pair2(t1, t2),
      l
    ))
    ==
    LinkedList::<T>::Cons(t1, LinkedList::<T>::Cons(t2,
      unpair::<T>(l)))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn empty_list_even_length<T>() -> bool {
    is_even(length::<T>(LinkedList::<T>::Nil))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn single_list_odd_length<T>(t: T) -> bool {
    !is_even(length::<T>(LinkedList::<T>::Cons(t, LinkedList::<T>::Nil)))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn empty_list_even_length_alt_def<T>() -> bool {
    list_len_is_even::<T>(LinkedList::<T>::Nil)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn single_list_odd_length_alt_def<T>(t: T) -> bool {
    !list_len_is_even::<T>(LinkedList::<T>::Cons(t, LinkedList::<T>::Nil))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn append_toggle_alt_def<T>(t: T) -> bool {
    list_len_is_even::<T>(l) ==
    !list_len_is_even::<T>(LinkedList::<T>::Cons(t, l))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn evenness_def_tie<T>() -> bool {
    is_even(length::<T>(l))
    ==
    list_len_is_even::<T>(l)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn middle_implication<T>() -> bool {
    implies(
      list_len_is_even::<T>(l),
      unpair::<T>(pairs::<T>(l)) == l
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn pair_unpair<T: PartialEq + Clone>() -> bool {
    implies(
      is_even(length::<T>(xs)),
      unpair::<T>(pairs::<T>(xs)) == xs
    )
  }
}
