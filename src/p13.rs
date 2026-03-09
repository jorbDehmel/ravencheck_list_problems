// ./problems/list_deleteAll_count.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
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
  (par (a) (((x a) (y (list a))) Int))
  (match y
    ((nil 0)
     ((cons z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=>
        (= (deleteAll x xs)
          (deleteBy (lambda ((y a)) (lambda ((z a)) (= y z))) x xs))
        (<= (count x xs) 1)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p13 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum Nat {
    Z,
    S(Box<Nat>)
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum Int {
    Positive(Box<Nat>),
    Negative(Box<Nat>)
  }

  // Maps an integer to its successor
  #[define]
  fn int_succ(x: Int) -> Int {
    match x {
      Int::Positive(x_data) =>
        Int::Positive(Box::new(Nat::S(Box::new(*x_data)))),
      Int::Negative(x_data) =>
        match *x_data {
          Nat::Z => Int::Positive(Box::new(Nat::S(Box::new(Nat::Z)))),
          Nat::S(x_data_prev) => Int::Negative(Box::new(*x_data_prev))
        }
    }
  }

  #[define]
  #[recursive]
  fn leq_nat(x: Nat, y: Nat) -> bool {
    match x {
      Nat::Z => true,
      Nat::S(z) => match y {
        Nat::Z => false,
        Nat::S(x2) => leq_nat(*z, *x2)
      }
    }
  }

  #[define]
  fn leq(x: Int, y: Int) -> bool {
    match x {
      Int::Positive(x_data) => match y {
        Int::Positive(y_data) => leq_nat(*x_data, *y_data),
        Int::Negative(y_data) =>
          (*x_data == Nat::Z) && (*y_data == Nat::Z)
      },
      Int::Negative(x_data) => match y {
        Int::Positive(_y_data) => true,
        Int::Negative(y_data) => leq_nat(*y_data, *x_data)
      }
    }
  }

  #[define]
  #[recursive]
  fn delete_by<A: PartialEq + Clone>(x: fn(A, A) -> bool, y: A, z: LinkedList<A>) -> LinkedList<A> {
    match z {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(y2, ys) =>
        if x(y.clone(), y2.clone()) {
          *ys
        } else {
          LinkedList::<A>::Cons(y2, Box::new(delete_by::<A>(x, y, *ys)))
        }
    }
  }

  #[define]
  #[recursive]
  fn count<A: PartialEq>(x: A, y: LinkedList<A>) -> Int {
    match y {
      LinkedList::<A>::Nil => Int::Positive(Box::new(Nat::Z)),
      LinkedList::<A>::Cons(z, ys) => if x == z {
        int_succ(count::<A>(x, *ys))
      } else {
        count::<A>(x, *ys)
      }
    }
  }

  #[define]
  #[recursive]
  fn delete_all<A: PartialEq + Clone>(x: A, y: LinkedList<A>) -> LinkedList<A> {
    match y {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(z, ys) => if x == z {
        delete_all(x, *ys)
      } else {
        LinkedList::<A>::Cons(z, Box::new(delete_all(x, *ys)))
      }
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p13<A: PartialEq + Clone>(x: A) -> bool {
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
      leq(
        count::<A>(x, xs),
        Int::Positive(Box::new(Nat::S(Box::new(Nat::Z))))
      )
    )
  }
}
