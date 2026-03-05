// ./problems/list_weird_is_normal.smt2

/*
; List monad laws
;
; Here, weird_concat is a somewhat sensible concatenation function,
; and has a somewhat strange recursion pattern.
(declare-sort Any 0)
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
  ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  concat
  (par (a) (((x (list (list a)))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xs) (++ y (concat xs))))))
(prove
  (par (a)
    (forall ((x (list (list Any)))) (= (concat x) (weird_concat x)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p46 {
  // Note: I'm just going to use A == Any for generic A. I don't
  // know why they haven't done that in the spec.

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

  #[define]
  #[recursive]
  fn normal_concat<A>(x: LinkedList<LinkedList<A>>) -> LinkedList<A> {
    match x {
      LinkedList::<LinkedList<A>>::Nil => LinkedList::<A>::Nil,
      LinkedList::<LinkedList<A>>::Cons(y, xs) =>
        append::<A>(
          y,
          normal_concat::<A>(*xs)
        )
    }
  }

  //////////////////////////////////////////////////////////////

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(x: LinkedList<A>)]
  fn lemma_1<A>() -> bool {
    x == append::<A>(LinkedList::<A>::Nil, x)
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  fn lemma_2<A>() -> bool {
    normal_concat::<A>(LinkedList::<LinkedList<A>>::Nil)
    ==
    weird_concat::<A>(LinkedList::<LinkedList<A>>::Nil)
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>, b: LinkedList<A>)]
  fn append_one_identity<A>(z: A) -> bool {
    append::<A>(LinkedList::<A>::Cons(z, a), b)
    ==
    LinkedList::<A>::Cons(z, append::<A>(a, b))
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn lemma_4<A>(z: A) -> bool {
    append::<A>(
      LinkedList::<A>::Cons(z, xs),
      normal_concat::<A>(LinkedList::<LinkedList<A>>::Nil)
    ) == LinkedList::<A>::Cons(
      z,
      weird_concat::<A>(
        LinkedList::<LinkedList<A>>::Cons(xs, LinkedList::<LinkedList<A>>::Nil)
      )
    )
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>, x: LinkedList<LinkedList<A>>)]
  fn lemma_3<A>(z: A) -> bool {
    append::<A>(
      LinkedList::<A>::Cons(z, xs),
      normal_concat::<A>(x)
    ) == LinkedList::<A>::Cons(
      z,
      weird_concat::<A>(
        LinkedList::<LinkedList<A>>::Cons(xs, x)
      )
    )
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(x: LinkedList<LinkedList<A>>)]
  fn p46<A>() -> bool {
    normal_concat::<A>(x) == weird_concat::<A>(x)
  }
}
