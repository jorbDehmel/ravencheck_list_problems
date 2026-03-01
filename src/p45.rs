// ./problems/list_weird_concat_map_bind.smt2

/*
; List monad laws
;
; Here, weird_concat is a somewhat sensible concatenation function,
; and has a somewhat strange recursion pattern.
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  weird_concat
  (par (a) (((x (list (list a)))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xss)
      (match y
        ((nil (weird_concat xss))
         ((cons z xs) (cons z (weird_concat (cons xs xss))))))))))
(define-fun-rec
  map
  (par (a b) (((f (=> a b)) (x (list a))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons y xs) (cons (@ f y) (map f xs))))))
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
  (par (a b)
    (forall ((f (=> a (list b))) (xs (list a)))
      (= (weird_concat (map f xs)) (>>= xs f)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p45 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  pub fn append<A>(x: LinkedList<A>, y: LinkedList<A>) -> LinkedList<A> {
    match x {
      LinkedList::<A>::Nil => y,
      LinkedList::<A>::Cons(z, xs) => LinkedList::<A>::Cons(z, Box::new(append::<A>(*xs, y)))
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

  #[define]
  #[recursive]
  fn map<A, B>(f: fn(A) -> LinkedList<B>, x: LinkedList<A>) -> LinkedList<LinkedList<B>> {
    match x {
      LinkedList::<A>::Nil => LinkedList::<LinkedList<B>>::Nil,
      LinkedList::<A>::Cons(y, xs) =>
        LinkedList::<LinkedList<B>>::Cons(
          f(y),
          Box::new(map::<A, B>(f, *xs))
        )
    }
  }

  #[define]
  #[recursive]
  fn weird_concat<A>(x: LinkedList<LinkedList<A>>) -> LinkedList<A> {
    match x {
      LinkedList::<LinkedList<A>>::Nil => LinkedList::<A>::Nil,
      LinkedList::<LinkedList<A>>::Cons(y, xss) => match y {
        LinkedList::<A>::Nil => weird_concat::<A>(*xss),
        LinkedList::<A>::Cons(z, xs) => LinkedList::<A>::Cons(
          z,
          Box::new(
            weird_concat::<A>(
              LinkedList::<LinkedList<A>>::Cons(
                *xs,
                Box::new(*xss)
              )
            )
          )
        )
      }
    }
  }

  #[declare]
  #[phantom]
  fn f<A, B>(_: A) -> LinkedList<B> {}

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p45<A, B: PartialEq>() -> bool {
    weird_concat::<B>(map::<A, B>(f::<A, B>, xs))
    ==
    map_concat::<A, B>(xs, f::<A, B>)
  }
}
