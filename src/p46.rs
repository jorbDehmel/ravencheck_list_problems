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

  // Notably, this doesn't use append
  #[define]
  #[recursive]
  fn weird_concat<A>(x: LinkedList<LinkedList<A>>) -> LinkedList<A> {
    match x {
      LinkedList::<LinkedList<A>>::Nil => LinkedList::<A>::Nil,
      // Pick apart first node
      LinkedList::<LinkedList<A>>::Cons(y, xss) =>
        // Pick apart data of first node
        match y {
          // If first node is empty, concat the rest of the list
          LinkedList::<A>::Nil => weird_concat::<A>(*xss),
          LinkedList::<A>::Cons(z, xs) =>
            // Else, prepend the first element of the data and
            // recurse
            LinkedList::<A>::Cons(
              z,
              Box::new(
                weird_concat::<A>(
                  LinkedList::<LinkedList<A>>::Cons(
                    *xs,           // The next node of the data
                    Box::new(*xss) // The current list
                  )
                )
              )
            )
        }
    }
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
  #[inductive(a: LinkedList<A>)]
  fn lemma_16<A>(b: LinkedList<A>, c: LinkedList<A>) -> bool {
    implies(b == c, append::<A>(a, b) == append::<A>(a, c))
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(x: LinkedList<A>)]
  fn lemma_1<A>() -> bool {
    x == append::<A>(LinkedList::<A>::Nil, x)
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>, b: LinkedList<A>)]
  fn lemma_2<A>(z: A) -> bool {
    append::<A>(
      LinkedList::<A>::Cons(z, a),
      b
    ) == LinkedList::<A>::Cons(z, append::<A>(a, b))
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  fn lemma_3<A>() -> bool {
    normal_concat::<A>(LinkedList::<LinkedList<A>>::Nil) == LinkedList::<A>::Nil
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  fn lemma_4<A>() -> bool {
    weird_concat::<A>(LinkedList::<LinkedList<A>>::Nil) == LinkedList::<A>::Nil
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(y: LinkedList<A>)]
  fn lemma_5<A>() -> bool {
    append::<A>(y, LinkedList::<A>::Nil) == y
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>)]
  fn lemma_6<A>() -> bool {
    normal_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        LinkedList::<LinkedList<A>>::Nil
      )
    ) == a
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>)]
  fn lemma_7<A>() -> bool {
    weird_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        LinkedList::<LinkedList<A>>::Nil
      )
    ) == a
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>, b: LinkedList<A>)]
  fn lemma_10<A>() -> bool {
    normal_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        LinkedList::<LinkedList<A>>::Cons(
          b,
          LinkedList::<LinkedList<A>>::Nil
        )
      )
    ) == append::<A>(a, b)
  }

  // This verifies, so the solver knows that weird_concat can
  // emulate append, even though it doesn't use it
  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>, b: LinkedList<A>)]
  fn lemma_11<A>() -> bool {
    weird_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        LinkedList::<LinkedList<A>>::Cons(
          b,
          LinkedList::<LinkedList<A>>::Nil
        )
      )
    ) == append::<A>(a, b)
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  fn lemma_17<A>(b: LinkedList<LinkedList<A>>) -> bool {
    normal_concat::<A>(b) == normal_concat::<A>(b)
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>)]
  fn lemma_14<A>(b: LinkedList<LinkedList<A>>) -> bool {
    normal_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        b
      )
    ) == append::<A>(a, normal_concat::<A>(b))
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>, b: LinkedList<LinkedList<A>>)]
  fn lemma_15<A>() -> bool {
    weird_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        b
      )
    ) == append::<A>(a, weird_concat::<A>(b))
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>, b: LinkedList<A>)]
  fn lemma_12<A>() -> bool {
    normal_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        LinkedList::<LinkedList<A>>::Nil
      )
    ) == weird_concat::<A>(
      LinkedList::<LinkedList<A>>::Cons(
        a,
        LinkedList::<LinkedList<A>>::Nil
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
