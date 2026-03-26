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
    let y = append::<A>(LinkedList::<A>::Nil, x);
    x == y
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(a: LinkedList<A>, b: LinkedList<A>)]
  fn lemma_2<A>(z: A) -> bool {
    let c = append::<A>(LinkedList::<A>::Cons(z, a), b);
    let d = LinkedList::<A>::Cons(z, append::<A>(a, b));
    c == d
  }

  #[assume]
  #[for_type(LinkedList<A> => <A>)]
  // #[inductive(xs4: LinkedList<A>, xs: LinkedList<LinkedList<A>>)]
  fn lemma_3<A>(z3: A, z4: A, xs4: LinkedList<A>, xs: LinkedList<LinkedList<A>>) -> bool {
    let z = normal_concat::<A>(xs);
    let a = append::<A>(xs4, z);
    let b = LinkedList::<A>::Cons(z4, a);
    let y = LinkedList::<A>::Cons(z4, xs4);
    let e = LinkedList::<A>::Cons(z3, y);
    let c = LinkedList::<LinkedList<A>>::Cons(e, xs);
    let d = weird_concat::<A>(c);
    b == d
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(x: LinkedList<LinkedList<A>>)]
  fn p46<A>() -> bool {
    let a = normal_concat::<A>(x);
    let b = weird_concat::<A>(x);
    a == b
  }
}
