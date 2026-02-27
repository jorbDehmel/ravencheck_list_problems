// ./problems/list_assoc.smt2

/*
; List monad laws
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  >>=
  (par (a b) (((x (list a)) (y (=> a (list b)))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons z xs) (++ (@ y z) (>>= xs y))))))
(prove
  (par (a b c)
    (forall ((m (list a)) (f (=> a (list b))) (g (=> b (list c))))
      (= (>>= (>>= m f) g) (>>= m (lambda ((x a)) (>>= (@ f x) g)))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p10 {
  #[derive(PartialEq)]
  #[define]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  pub fn append<T: PartialEq>(
      x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    match x {
      LinkedList::<T>::Nil => y,
      LinkedList::<T>::Cons(z, xs) =>
        LinkedList::<T>::Cons(z, Box::new(append::<T>(*xs, y)))
    }
  }

  /*
  Given a list and a function mapping list entries to new lists,
  return the concatenation of the lists created by applying the
  function to each entry in succession. This is ">>=" in the
  TIP specs.
  */
  #[define]
  #[recursive]
  fn map_concat<A, B: PartialEq>(x: LinkedList<A>,
      y: fn(A) -> LinkedList<B>) -> LinkedList<B> {
    match x {
      LinkedList::<A>::Nil => LinkedList::<B>::Nil,
      LinkedList::<A>::Cons(z, xs) => append::<B>(
        y(z),
        map_concat::<A, B>(*xs, y)
      )
    }
  }

  #[declare]
  #[phantom]
  fn f<A, B>(_: A) -> LinkedList<B> {}

  #[declare]
  #[phantom]
  fn g<B, C>(_: B) -> LinkedList<C> {}

  /*
  This has some type weirdness in the VC: I think this is an
  internal issue w/ polymorphic types, but IDK
  */
  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[for_type(LinkedList<B> => <B>)]
  #[for_type(LinkedList<C> => <C>)]
  #[inductive(m: LinkedList<A>)]
  fn list_assoc<A, B: PartialEq, C: PartialEq>() -> bool {
    map_concat::<B, C>(
      map_concat::<A, B>(m, f::<A, B>),
      g::<B, C>
    ) == map_concat::<A, C>(
      m,
      |x: A| {
        map_concat::<B, C>(f::<A, B>(x), g::<B, C>)
      }
    )
  }
}
