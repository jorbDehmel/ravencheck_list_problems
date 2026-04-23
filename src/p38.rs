// ./problems/list_nub_nub.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  filter
  (par (a) (((p (=> a Bool)) (x (list a))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xs) (ite (@ p y) (cons y (filter p xs)) (filter p xs))))))
(define-fun-rec
  nubBy
  (par (a) (((x (=> a (=> a Bool))) (y (list a))) (list a)))
  (match y
    ((nil (_ nil a))
     ((cons z xs)
      (cons z
        (nubBy x (filter (lambda ((y2 a)) (not (@ (@ x z) y2))) xs)))))))
(prove
  (par (a)
    (forall ((xs (list a)))
      (=
        (nubBy (lambda ((x a)) (lambda ((y a)) (= x y)))
          (nubBy (lambda ((z a)) (lambda ((x2 a)) (= z x2))) xs))
        (nubBy (lambda ((x3 a)) (lambda ((x4 a)) (= x3 x4))) xs)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p38 {
  #[derive(PartialEq)]
  #[define]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  #[total]
  fn filter<A: PartialEq + Clone, F: Fn(A) -> bool>(p: F, x: LinkedList<A>) -> LinkedList<A> {
    match x {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(y, xs) =>
        if p(y.clone()) {
          LinkedList::<A>::Cons(
            y,
            Box::new(
              filter::<A, F>(p, *xs)
            )
          )
        } else {
          filter::<A, F>(p, *xs)
        }
    }
  }

  #[define]
  #[recursive]
  #[total]
  fn nub_by<A: PartialEq + Clone>(x: fn(A, A) -> bool, y: LinkedList<A>) -> LinkedList<A> {
    match y {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(z, xs) => LinkedList::Cons(
        z.clone(),
        Box::new(nub_by(
          x.clone(),
          filter(
            |y2: A| {
              !x(z.clone(), y2)
            },
            *xs
          )
        ))
      )
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p38<A>() -> bool {
    nub_by(
      |x: A, y: A| { x == y },
      nub_by(|z: A, x2: A| { z == x2 }, xs)
    ) == nub_by(|x3: A, x4: A| { x3 == x4 }, xs)
  }
}
