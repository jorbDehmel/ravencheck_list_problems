// ./problems/list_concat_map_bind.smt2

/*
; List monad laws
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  map
  (par (a b) (((f (=> a b)) (x (list a))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons y xs) (cons (@ f y) (map f xs))))))
(define-fun-rec
  ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  >>=
  (par (a b) (((x (list a)) (y (=> a (list b)))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons z xs) (++ (@ y z) (>>= xs y))))))
(define-fun-rec
  concat
  (par (a) (((x (list (list a)))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xs) (++ y (concat xs))))))
(prove
  (par (a b)
    (forall ((f (=> a (list b))) (xs (list a)))
      (= (concat (map f xs)) (>>= xs f)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p11 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  pub fn append<T: PartialEq>(x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    match x {
      LinkedList::<T>::Nil => y,
      LinkedList::<T>::Cons(z, xs) => LinkedList::<T>::Cons(z, Box::new(append::<T>(*xs, y)))
    }
  }

  #[define]
  #[recursive]
  fn map<T: PartialEq + Copy>(f: fn(T) -> LinkedList<T>, x: LinkedList<T>) -> LinkedList<LinkedList<T>> {
    match x {
      LinkedList::<T>::Nil => LinkedList::<LinkedList<T>>::Nil,
      LinkedList::<T>::Cons(y, xs) => LinkedList::<LinkedList<T>>::Cons(f(y), Box::new(map::<T>(f, *xs)))
    }
  }

  #[define]
  #[recursive]
  fn map_concat<T: PartialEq + Copy>(x: LinkedList<T>, y: fn(T) -> LinkedList<T>) -> LinkedList<T> {
    match x {
      LinkedList::<T>::Nil => LinkedList::<T>::Nil,
      LinkedList::<T>::Cons(z, xs) => append::<T>(
        y(z),
        map_concat::<T>(*xs, y)
      )
    }
  }

  #[define]
  #[recursive]
  fn concat<T: PartialEq + Copy>(x: LinkedList<LinkedList<T>>) -> LinkedList<T> {
    match x {
      LinkedList::<LinkedList<T>>::Nil => LinkedList::<T>::Nil,
      LinkedList::<LinkedList<T>>::Cons(y, xs) => append::<T>(y, concat::<T>(*xs))
    }
  }

  #[declare]
  #[phantom]
  fn f<T: PartialEq + Copy>(_: T) -> LinkedList<T> {}

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn list_concat_map_bind<T: PartialEq + Copy>() -> bool {
    concat::<T>(map::<T>(f::<T>, xs)) == map_concat::<T>(xs, f::<T>)
  }
}
