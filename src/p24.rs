// ./problems/list_nat_SelectPermutations.smt2

/*
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
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
  formula
  (par (a) (((x (list (pair a (list a))))) (list (list a))))
  (match x
    ((nil (_ nil (list a)))
     ((cons y z)
      (match y (((pair2 y2 ys) (cons (cons y2 ys) (formula z)))))))))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  (par (a) (((x (=> a (=> a Bool))) (y a) (z (list a))) (list a)))
  (match z
    ((nil (_ nil a))
     ((cons y2 ys)
      (ite (@ (@ x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  (par (a) (((x (list a)) (y (list a))) Bool))
  (match x
    ((nil
      (match y
        ((nil true)
         ((cons z x2) false))))
     ((cons x3 xs)
      (and (elem x3 y)
        (isPermutation xs
          (deleteBy (lambda ((x4 a)) (lambda ((x5 a)) (= x4 x5))) x3 y)))))))
(define-fun-rec
  all
  (par (a) (((p (=> a Bool)) (x (list a))) Bool))
  (match x
    ((nil true)
     ((cons y xs) (and (@ p y) (all p xs))))))
(prove
  (par (a)
    (forall ((xs (list a)))
      (all (lambda ((x (list a))) (isPermutation x xs))
        (formula (select2 xs))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p24 {
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
  pub fn elem<T: PartialEq>(x: T, y: LinkedList<T>) -> bool {
    match y {
      LinkedList::<T>::Nil => false,
      LinkedList::<T>::Cons(z, xs) => z == x || elem::<T>(x, *xs)
    }
  }

  #[define]
  #[recursive]
  fn formula<T>(x: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<LinkedList<T>> {
    match x {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil =>
        LinkedList::<LinkedList<T>>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(y, z) =>
        match y {
          Pair::<T, LinkedList<T>>::Pair2(y2, ys) =>
            LinkedList::<LinkedList<T>>::Cons(
              LinkedList::<T>::Cons(y2, Box::new(ys)),
              Box::new(formula::<T>(*z))
            )
        }
    }
  }

  #[define]
  #[recursive]
  fn delete_by<T: PartialEq + Clone, F: Fn(T, T) -> bool>(x: F, y: T, z: LinkedList<T>) -> LinkedList<T> {
    match z {
      LinkedList::<T>::Nil => LinkedList::<T>::Nil,
      LinkedList::<T>::Cons(y2, ys) =>
        if x(y.clone(), y2.clone()) {
          *ys
        } else {
          LinkedList::<T>::Cons(y2, Box::new(delete_by::<T, F>(x, y, *ys)))
        }
    }
  }

  #[define]
  #[recursive]
  fn is_permutation<T: PartialEq + Clone>(x: LinkedList<T>, y: LinkedList<T>) -> bool {
    match x {
      LinkedList::<T>::Nil => match y {
        LinkedList::<T>::Nil => true,
        LinkedList::<T>::Cons(_y_data, _y_next) => false
      },
      LinkedList::<T>::Cons(x_data, x_next) =>
        elem::<T>(x_data.clone(), y.clone())
        &&
        is_permutation::<T>(
          *x_next,
          delete_by::<T, fn(T, T) -> bool>(
            |x4: T, x5: T| {
              x4 == x5
            },
            x_data,
            y
          )
        )
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

  /*
  (prove
    (par (a)
      (forall ((xs (list a)))
        (all (lambda ((x (list a))) (isPermutation x xs))
          (formula (select2 xs))))))
  */
  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn p24<T>() -> bool {
    all::<T>(
      |x: LinkedList<T>| {
        is_permutation::<T>(x, xs)
      },
      formula::<T>(select2::<T>(xs))
    )
  }
}
