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
  #[total]
  pub fn append<T: PartialEq>(x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    match x {
      LinkedList::<T>::Nil => y,
      LinkedList::<T>::Cons(z, xs) => LinkedList::<T>::Cons(z, Box::new(append::<T>(*xs, y)))
    }
  }

  //////////////////////////////////////////////////////////////
  /// Verification

  // This implies lemma 1
  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l1: LinkedList<T>, l2: LinkedList<T>)]
  fn lemma_2<T>(t: T, t1: T) -> bool {
    l1 != LinkedList::<T>::Cons(t, append::<T>(l2, LinkedList::<T>::Cons(t1, l1)))
  }

  // This implies injectivity of append
  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(zs: LinkedList<T>, l: LinkedList<T>)]
  fn lemma_1<T>(t: T) -> bool {
    zs != LinkedList::<T>::Cons(t, append::<T>(l, zs))
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
