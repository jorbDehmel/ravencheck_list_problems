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
  #[derive(PartialEq, Clone)]
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

  #[define]
  enum MyType<A, B, C> {
    MyType(LinkedList<A>, LinkedList<B>, LinkedList<C>)
  }

  /*
  Via Nick: Create a new dummy type which uses all A, B, C and
  forces instantiations for all. Inductive doesn't need to be
  changed, but for_type does.
  */
  #[annotate]
  #[for_type(Mytype<A, B, C> => <A, B, C>)]
  #[inductive(m: LinkedList<A>)]
  fn list_assoc<A: PartialEq, B: PartialEq, C: PartialEq>() -> bool {
    let _: MyType<A, B, C> = MyType::<A, B, C>::MyType(LinkedList::<A>::Nil, LinkedList::<B>::Nil, LinkedList::<C>::Nil);

    map_concat::<B, C>(
      map_concat::<A, B>(m.clone(), f::<A, B>),
      g::<B, C>
    ) == map_concat::<A, C>(
      m,
      |x: A| {
        map_concat::<B, C>(f::<A, B>(x), g::<B, C>)
      }
    )
  }

  fn f_typecheck<A, B>(_: A) -> LinkedList<B> {
    LinkedList::<B>::Nil
  }
  fn g_typecheck<B, C>(_: B) -> LinkedList<C> {
    LinkedList::<C>::Nil
  }

  fn list_assoc_typecheck<A: Clone, B: PartialEq, C: PartialEq>(m: LinkedList<A>) -> bool {
    map_concat::<B, C>(
      map_concat::<A, B>(m.clone(), f_typecheck::<A, B>),
      g_typecheck::<B, C>
    ) == map_concat::<A, C>(
      m,
      |x: A| {
        map_concat::<B, C>(f_typecheck::<A, B>(x), g_typecheck::<B, C>)
      }
    )
  }
}
