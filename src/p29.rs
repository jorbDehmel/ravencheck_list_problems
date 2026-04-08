// ./problems/list_nat_elem.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-const undefined (par (a) a))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  at
  (par (a) (((x (list a)) (y Nat)) a))
  (match x
    ((nil (_ undefined a))
     ((cons z x2)
      (match y
        ((zero z)
         ((succ x3) (at x2 x3))))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=> (elem x xs) (exists ((y Nat)) (= x (at xs y)))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p29 {
  /// Note: For this one I've chosen to use an Opt enum instead
  /// of 'undefined'.

  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum MyOpt<T> {
    Some(T),
    None
  }

  #[define]
  pub enum Nat {
    Z,
    S(Box<Nat>)
  }

  #[define]
  #[recursive]
  fn elem<A: PartialEq>(x: A, y: LinkedList<A>) -> bool {
    match y {
      LinkedList::<A>::Nil => false,
      LinkedList::<A>::Cons(z, xs) =>
        (z == x) || elem::<A>(x, *xs)
    }
  }

  #[define]
  #[recursive]
  fn at<A>(x: LinkedList<A>, y: Nat) -> MyOpt<A> {
    match x {
      LinkedList::<A>::Nil => MyOpt::<A>::None,
      LinkedList::<A>::Cons(z, x2) => match y {
        Nat::Z => MyOpt::<A>::Some(z),
        Nat::S(x3) => at::<A>(*x2, *x3)
      }
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn lemma_1<A>(x: A) -> bool {
    at::<A>(LinkedList::<A>::Cons(x, xs), Nat::Z) == MyOpt::<A>::Some(x)
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(x: LinkedList<A>, n: Nat)]
  fn lemma_2<A>(z: A) -> bool {
    at::<A>(x, n) == at::<A>(LinkedList::<A>::Cons(z, x), Nat::S(n))
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(x: LinkedList<A>)]
  fn lemma_3<A>(y: A, z: A) -> bool {
    implies(
      elem::<A>(y, x),
      elem::<A>(y, LinkedList::<A>::Cons(z, x))
    )
  }

  // // asserting or checking this one causes sort cycles in both
  // // this and the main VC
  // #[annotate]
  // #[for_type(LinkedList<A> => <A>)]
  // #[inductive(xs: LinkedList<A>, z: Nat)]
  // fn lemma_4<A>(x: A) -> bool {
  //   implies(
  //     def_and_eq(
  //       at::<A>(xs, z),
  //       MyOpt::<A>::Some(x)
  //     ),
  //     exists(
  //       |y: Nat| {
  //         def_and_eq(
  //           at::<A>(xs, y),
  //           MyOpt::<A>::Some(x)
  //         )
  //       }
  //     )
  //   )
  // }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p29<A: PartialEq + Clone>(x: A) -> bool {
    implies(
      elem::<A>(x, xs),
      exists(
        |y: Nat| {
          def_and_eq(
            at::<A>(xs, y),
            MyOpt::<A>::Some(x)
          )
        }
      )
    )
  }
}
