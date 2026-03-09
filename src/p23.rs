// ./problems/list_nat_SelectPermutations'.smt2

/*
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  select
  (par (a)
    (((x a) (y (list (pair a (list a))))) (list (pair a (list a)))))
  (match y
    ((nil (_ nil (pair a (list a))))
     ((cons z x2)
      (match z
        (((pair2 y2 ys) (cons (pair2 y2 (cons x ys)) (select x x2)))))))))
(define-fun-rec
  select2
  (par (a) (((x (list a))) (list (pair a (list a)))))
  (match x
    ((nil (_ nil (pair a (list a))))
     ((cons y xs) (cons (pair2 y xs) (select y (select2 xs)))))))
(define-fun-rec
  plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (succ (plus z y))))))
(define-fun-rec
  formula
  (par (a) (((x (list (pair a (list a))))) (list (list a))))
  (match x
    ((nil (_ nil (list a)))
     ((cons y z)
      (match y (((pair2 y2 ys) (cons (cons y2 ys) (formula z)))))))))
(define-fun-rec
  count
  (par (a) (((x a) (y (list a))) Nat))
  (match y
    ((nil zero)
     ((cons z ys)
      (ite (= x z) (plus (succ zero) (count x ys)) (count x ys))))))
(define-fun-rec
  all
  (par (a) (((q (=> a Bool)) (x (list a))) Bool))
  (match x
    ((nil true)
     ((cons y xs) (and (@ q y) (all q xs))))))
(prove
  (par (a)
    (forall ((xs (list a)) (z a))
      (all (lambda ((x (list a))) (= (count z xs) (count z x)))
        (formula (select2 xs))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p23 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum Pair<F, S> {
    Pair2(F, S)
  }

  #[define]
  pub enum Nat {
    Z,
    S(Box<Nat>)
  }

  #[define]
  #[recursive]
  fn select<T: PartialEq + Clone>(x: T, y: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match y {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(z, x2) =>
        match z {
          Pair::<T, LinkedList<T>>::Pair2(y2, ys) =>
            LinkedList::<Pair<T, LinkedList<T>>>::Cons(
              Pair::<T, LinkedList<T>>::Pair2(
                y2,
                LinkedList::<T>::Cons(x.clone(), Box::new(ys))
              ),
              Box::new(select::<T>(x, *x2))
            )
        }
    }
  }

  #[define]
  #[recursive]
  fn select2<T: PartialEq + Clone>(x: LinkedList<T>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match x {
      LinkedList::<T>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<T>::Cons(y, xs) =>
        LinkedList::<Pair<T, LinkedList<T>>>::Cons(
          Pair::<T, LinkedList<T>>::Pair2(y.clone(), *xs.clone()),
          Box::new(select::<T>(y, select2::<T>(*xs)))
        )
    }
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

  #[define]
  #[recursive]
  fn all<T>(p: fn(T) -> bool, x: LinkedList<T>) -> bool {
    match x {
      LinkedList::<T>::Nil => true,
      LinkedList::<T>::Cons(y, xs) => p(y) && all::<T>(p, *xs)
    }
  }

  //////////////////////////////////////////////////////////////

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p23_1<A>(z: A) -> bool {
    all::<A>(
      |x: LinkedList<A>| {
        count::<A>(z, xs) == count::<A>(z, x)
      },
      formula::<A>(select2::<A>(xs))
    )
  }

  #[annotate]
  #[inductive(x: Nat, y: Nat, z: Nat)]
  fn p23_2() -> bool {
    plus(x, plus(y, z)) == plus(plus(x, y), z)
  }

  #[annotate]
  #[inductive(x: Nat, y: Nat)]
  fn p23_3() -> bool {
    plus(x, y) == plus(y, x)
  }

  #[annotate]
  #[inductive(x: Nat)]
  fn p23_4() -> bool {
    plus(x, Nat::Z) == x
  }

  #[annotate]
  #[inductive(x: Nat)]
  fn p23_5() -> bool {
    plus(Nat::Z, x) == x
  }
}
