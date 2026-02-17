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

  #[define]
  #[recursive]
  fn is_shorter_than<T>(a: LinkedList<T>, b: LinkedList<T>) -> bool {
    match a {
      LinkedList::<T>::Nil => match b {
        LinkedList::<T>::Nil => false,
        LinkedList::<T>::Cons(_b_data, _b_next) => true
      },
      LinkedList::<T>::Cons(_a_data, a_next) => match b {
        LinkedList::<T>::Nil => false,
        LinkedList::<T>::Cons(_b_data, b_next) =>
          is_shorter_than::<T>(*a_next, *b_next)
      }
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn lemma_1_1<T>(t: T) -> bool {
    LinkedList::<T>::Nil != LinkedList::<T>::Cons(t, append::<T>(l, LinkedList::<T>::Nil))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn lemma_1_2<T>(t: T, t1: T) -> bool {
    LinkedList::<T>::Cons(t1, LinkedList::<T>::Nil) != LinkedList::<T>::Cons(t, append::<T>(l, LinkedList::<T>::Cons(t1, LinkedList::<T>::Nil)))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(zs: LinkedList<T>)]
  fn lemma_1_3<T>(t: T) -> bool {
    zs != LinkedList::<T>::Cons(t, append::<T>(LinkedList::<T>::Nil, zs))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn append_to_nil<T>() -> bool {
    append::<T>(
      LinkedList::<T>::Nil,
      l
    ) == l
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn l_ne_cons_l<T>(t: T) -> bool {
    l != LinkedList::<T>::Cons(t, l)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>)]
  fn append_single<T>(t: T) -> bool {
    append::<T>(
      LinkedList::<T>::Cons(t, LinkedList::<T>::Nil),
      l
    ) == LinkedList::<T>::Cons(t, l)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>, x: LinkedList<T>)]
  fn append_single_2<T>(t: T) -> bool {
    x != append::<T>(l, LinkedList::<T>::Cons(t, x))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(x: LinkedList<T>, y: LinkedList<T>)]
  fn lemma_3<T>(t: T) -> bool {
    x != append::<T>(y, LinkedList::<T>::Cons(t, x))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(a: LinkedList<T>, b: LinkedList<T>)]
  fn strengthened_inequality<T>(t1: T, t2: T) -> bool {
    implies(
      a != b,
      LinkedList::<T>::Cons(t1, a) != LinkedList::<T>::Cons(t2, b)
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(a: LinkedList<T>, b: LinkedList<T>)]
  fn is_shorter_than_implies_ne<T>() -> bool {
    implies(
      is_shorter_than::<T>(a, b),
      a != b
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(zs: LinkedList<T>, l: LinkedList<T>)]
  fn is_shorter_than_appendation<T>(t: T) -> bool {
    is_shorter_than::<T>(zs, LinkedList::<T>::Cons(t, append::<T>(l, zs)))
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(a: LinkedList<T>, b: LinkedList<T>)]
  fn nil_nil_append<T>() -> bool {
    (a == LinkedList::<T>::Nil && b == LinkedList::<T>::Nil)
    ==
    (append::<T>(a, b) == LinkedList::<T>::Nil)
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(zs: LinkedList<T>)]
  fn lemma_1_4<T>(t: T, t1: T) -> bool {
    zs != LinkedList::<T>::Cons(
      t,
      append::<T>(
        LinkedList::<T>::Cons(t1, LinkedList::<T>::Nil),
        zs
      )
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(l: LinkedList<T>, l1: LinkedList<T>)]
  fn lemma_2<T>(t: T, t1: T) -> bool {
    LinkedList::<T>::Cons(t1, l1) != LinkedList::<T>::Cons(
      t,
      append::<T>(l, LinkedList::<T>::Cons(t1, l1))
    )
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(x: LinkedList<T>, y: LinkedList<T>, z: LinkedList<T>)]
  fn commutativity_of_append<T>() -> bool {
    append::<T>(x, append::<T>(y, z)) == append::<T>(append::<T>(x, y), z)
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
