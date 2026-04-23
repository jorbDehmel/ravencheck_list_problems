// ./problems/list_nat_elem_nub_l.smt2

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
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=> (elem x xs)
        (elem x (nubBy (lambda ((y a)) (lambda ((z a)) (= y z))) xs))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p31 {
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

  #[define]
  #[recursive]
  fn elem<T: PartialEq>(x: T, y: LinkedList<T>) -> bool {
    match y {
      LinkedList::<T>::Nil => false,
      LinkedList::<T>::Cons(z, xs) => z == x || elem::<T>(x, *xs)
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p31<A>(x: A) -> bool {
    implies(
      elem::<A>(x, xs),
      elem::<A>(
        x,
        nub_by::<A>(
          |y: A, z: A| {
            y == z
          },
          xs
        )
      )
    )
  }
}
