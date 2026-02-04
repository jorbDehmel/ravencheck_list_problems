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
  #[import]
  use crate::list::linked_list::*;

  #[define]
  pub enum LinkedListOfLists {
    Nil,
    Cons(LinkedList, Box<LinkedListOfLists>),
  }

  #[define]
  #[recursive]
  fn map(f: fn(T) -> LinkedList, x: LinkedList) -> LinkedListOfLists {
    match x {
      LinkedList::Nil => LinkedListOfLists::Nil,
      LinkedList::Cons(y, xs) => LinkedListOfLists::Cons(f(y), Box::new(map(f, *xs)))
    }
  }

  #[define]
  #[recursive]
  fn right_right_equal(x: LinkedList, y: fn(T) -> LinkedList) -> LinkedList {
    match x {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(z, xs) => append(
        y(z),
        right_right_equal(*xs, y)
      )
    }
  }

  #[define]
  #[recursive]
  fn concat(x: LinkedListOfLists) -> LinkedList {
    match x {
      LinkedListOfLists::Nil => LinkedList::Nil,
      LinkedListOfLists::Cons(y, xs) => append(y, concat(*xs))
    }
  }

  #[declare]
  #[phantom]
  fn f(_: T) -> LinkedList {}

  #[annotate_multi]
  #[for_values(xs: LinkedList)]
  fn list_concat_map_bind() -> bool {
    concat(map(f, xs)) == right_right_equal(xs, f)
  }
}
