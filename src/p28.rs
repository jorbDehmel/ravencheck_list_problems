// ./problems/list_nat_deleteAll_count.smt2

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
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun-rec
  deleteBy
  (par (a) (((x (=> a (=> a Bool))) (y a) (z (list a))) (list a)))
  (match z
    ((nil (_ nil a))
     ((cons y2 ys)
      (ite (@ (@ x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  deleteAll
  (par (a) (((x a) (y (list a))) (list a)))
  (match y
    ((nil (_ nil a))
     ((cons z ys)
      (ite (= x z) (deleteAll x ys) (cons z (deleteAll x ys)))))))
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
      (=>
        (= (deleteAll x xs)
          (deleteBy (lambda ((y a)) (lambda ((z a)) (= y z))) x xs))
        (leq (count x xs) (succ zero))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p28 {
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
  fn leq(x: Nat, y: Nat) -> bool {
    match x {
      Nat::Z => true,
      Nat::S(z) => match y {
        Nat::Z => false,
        Nat::S(x2) => leq(*z, *x2)
      }
    }
  }

  #[define]
  #[recursive]
  fn delete_by<A: PartialEq + Clone, F: Fn(A, A) -> bool>(x: F, y: A, z: LinkedList<A>) -> LinkedList<A> {
    match z {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(y2, ys) =>
        if x(y.clone(), y2.clone()) {
          *ys
        } else {
          LinkedList::<A>::Cons(y2, Box::new(delete_by::<A, F>(x, y, *ys)))
        }
    }
  }

  #[define]
  #[recursive]
  fn delete_all<A: PartialEq>(x: A, y: LinkedList<A>) -> LinkedList<A> {
    match y {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(z, ys) =>
        if x == z {
          delete_all::<A>(x, *ys)
        } else {
          LinkedList::<A>::Cons(
            z,
            Box::new(delete_all::<A>(x, *ys))
          )
        }
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
  fn p28_1<A>(x: A) -> bool {
    implies(
      delete_all::<A>(x, xs)
      ==
      delete_by::<A>(
        |y: A| {
          |z: A| {
            y == z
          }
        },
        x,
        xs
      ),
      leq(count::<A>(x, xs), Nat::S(Nat::Z))
    )
  }

  #[annotate]
  #[inductive(x: Nat, y: Nat, z: Nat)]
  fn p28_2() -> bool {
    plus(x, plus(y, z)) == plus(plus(x, y), z)
  }

  #[annotate]
  #[inductive(x: Nat, y: Nat)]
  fn p28_3() -> bool {
    plus(x, y) == plus(y, x)
  }

  #[annotate]
  #[inductive(x: Nat)]
  fn p28_4() -> bool {
    plus(x, Nat::Z) == x
  }

  #[annotate]
  #[inductive(x: Nat)]
  fn p28_5() -> bool {
    plus(Nat::Z, x) == x
  }
}
