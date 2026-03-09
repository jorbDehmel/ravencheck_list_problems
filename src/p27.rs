// ./problems/list_nat_count_nub.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (succ (plus z y))))))
(define-fun-rec
  filter
  (par (a) (((q (=> a Bool)) (x (list a))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xs) (ite (@ q y) (cons y (filter q xs)) (filter q xs))))))
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
(define-fun-rec
  count
  (par (a) (((x a) (y (list a))) Nat))
  (match y
    ((nil zero)
     ((cons z ys)
      (ite (= x z) (plus (succ zero) (count x ys)) (count x ys))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=> (elem x xs)
        (= (count x (nubBy (lambda ((y a)) (lambda ((z a)) (= y z))) xs))
          (succ zero))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p27 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  pub enum Nat {
    Z,
    S(Box<Nat>)
  }

  #[define]
  #[recursive]
  fn plus(x: Nat, y: Nat) -> Nat {
    match x {
      Nat::Z => y,
      Nat::S(z) => Nat::S(Box::new(plus(*z, y)))
    }
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
  fn nub_by<A: PartialEq + Clone, F2: Fn(A) -> bool, F: Fn(A) -> F2 + Clone>(x: F, y: LinkedList<A>) -> LinkedList<A> {
    match y {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(z, xs) => LinkedList::Cons(
        z.clone(),
        Box::new(nub_by(
          x.clone(),
          filter(
            |y2: A| {
              !x(z.clone())(y2)
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

  #[define]
  #[recursive]
  fn count<A: PartialEq>(x: A, y: LinkedList<A>) -> Nat {
    match y {
      LinkedList::<A>::Nil => Nat::Z,
      LinkedList::<A>::Cons(z, ys) => if x == z {
        Nat::S(Box::new(count::<A>(x, *ys)))
      } else {
        count::<A>(x, *ys)
      }
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p27<A>(x: A) -> bool {
    implies(
      elem::<A>(x, xs),
      count::<A>(
        x,
        nub_by(
          |y: A| {
            |z: A| {
              y == z
            }
          },
          xs
        )
      )
      ==
      Nat::S(Nat::Z)
    )
  }

  /*
  (assert
    (forall ((x Nat) (y Nat) (z Nat))
      (= (plus x (plus y z)) (plus (plus x y) z))))
  */

  /*
  (assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
  */

  /*
  (assert (forall ((x Nat)) (= (plus x zero) x)))
  */

  /*
  (assert (forall ((x Nat)) (= (plus zero x) x)))
  */
}
