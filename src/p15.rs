// ./problems/list_elem_map.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  map
  (par (a b) (((f (=> a b)) (x (list a))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons y xs) (cons (@ f y) (map f xs))))))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(prove
  (par (a)
    (forall ((y a) (f (=> a a)) (xs (list a)))
      (=> (elem y (map f xs))
        (exists ((x a)) (and (= (@ f x) y) (elem y xs)))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p15 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  fn map<T>(f: fn(T) -> T, x: LinkedList<T>) -> LinkedList<T> {
    match x {
      LinkedList::<T>::Nil => LinkedList::<T>::Nil,
      LinkedList::<T>::Cons(y, xs) =>
        LinkedList::<T>::Cons(
          f(y),
          Box::new(map::<T>(f, *xs))
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

  #[declare]
  #[phantom]
  fn f<T>(_: T) -> T {}

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn list_elem_map<T>(y: T) -> bool {
    implies(
      elem::<T>(y, map::<T>(f::<T>, xs)),
      exists(
        |x: T| {
          def_and_eq(f::<T>(x), y)
          &&
          elem::<T>(y, xs)
        }
      )
    )
  }
}
