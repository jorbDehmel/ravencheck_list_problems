/*
// ./problems/list_Select.smt2
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
  map
  (par (a b) (((f (=> a b)) (x (list a))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons y xs) (cons (@ f y) (map f xs))))))
(prove
  (par (b)
    (forall ((xs (list b)))
      (=
        (map (lambda ((x (pair b (list b)))) (match x (((pair2 y z) y))))
          (select2 xs))
        xs))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p5 {
  #[import]
  use crate::poly_list::poly_linked_list::*;

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
  fn map<T: PartialEq + Clone>(f: fn(Pair<T, LinkedList<T>>) -> T, x: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<T> {
    match x {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil => LinkedList::<T>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(y, xs) => LinkedList::<T>::Cons(f(y), Box::new(map::<T>(f, *xs)))
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  fn list_select<T: PartialEq + Clone>(xs: LinkedList<T>) -> bool {
    map::<T>(
      |x: Pair<T, LinkedList<T>>| {
        match x {
          Pair::<T, LinkedList<T>>::Pair2(y, z) => y
        }
      },
      select2::<T>(xs)
    ) == xs
  }
}
