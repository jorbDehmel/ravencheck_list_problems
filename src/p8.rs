/*
; Injectivity of append
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(prove
  (par (a)
    (forall ((xs (list a)) (ys (list a)) (zs (list a)))
      (=> (= (++ xs zs) (++ ys zs)) (= xs ys)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p8 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  pub fn append<T: PartialEq>(x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    match x {
      LinkedList::<T>::Nil => y,
      LinkedList::<T>::Cons(z, xs) => LinkedList::<T>::Cons(z, Box::new(append::<T>(*xs, y)))
    }
  }

  //////////////////////////////////////////////////////////////
  /// Verification

  // Returns true iff l1 is a suffix of l2
  #[define]
  #[recursive]
  fn is_suffix_of<T: PartialEq>(l1: LinkedList<T>, l2: LinkedList<T>) -> bool {
    if l1 == l2 {
      true
    } else {
      match l2 {
        LinkedList::<T>::Nil => false,
        LinkedList::<T>::Cons(_l2_data, l2_next) =>
          is_suffix_of::<T>(l1, *l2_next)
      }
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn lemma_1<T>() -> bool {
    is_suffix_of::<T>(l, l)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l1: LinkedList<T>, l2: LinkedList<T>)]
  fn lemma_2<T>() -> bool {
    is_suffix_of::<T>(l1, append::<T>(l2, l1))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l1: LinkedList<T>)]
  fn lemma_3<T>(t: T) -> bool {
    is_suffix_of::<T>(l1, LinkedList::<T>::Cons(t, l1))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l1: LinkedList<T>, l2: LinkedList<T>)]
  fn lemma_4<T>(t: T) -> bool {
    implies(
      !is_suffix_of::<T>(l1, l2),
      !is_suffix_of::<T>(LinkedList::<T>::Cons(t, l1), l2)
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l1: LinkedList<T>)]
  fn lemma_5<T>(t: T) -> bool {
    !is_suffix_of::<T>(LinkedList::<T>::Cons(t, l1), l1)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>, ys: LinkedList<T>, zs: LinkedList<T>)]
  fn injectivity_of_append<T>() -> bool {
    implies(
      append::<T>(xs, zs) == append::<T>(ys, zs),
      xs == ys
    )
  }
}
