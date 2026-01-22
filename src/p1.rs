// ./problems/list_Interleave.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))

(define-fun-rec
  interleave
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (interleave y xs))))))

(define-funs-rec
  ((evens
    (par (a) (((x (list a))) (list a))))
   (odds
    (par (a) (((x (list a))) (list a)))))
  ((match x
     ((nil (_ nil a))
      ((cons y xs) (cons y (odds xs)))))
   (match x
     ((nil (_ nil a))
      ((cons y xs) (evens xs))))))

(prove
  (par (a)
    (forall ((xs (list a))) (= (interleave (evens xs) (odds xs)) xs))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p1 {
  #[import]
  use crate::list::linked_list::*;

  #[define]
  #[recursive]
  fn evens(x: LinkedList) -> LinkedList {
    match x {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(y, xs) => LinkedList::Cons(y, Box::new(odds(*xs)))
    }
  }

  #[define]
  #[recursive]
  fn odds(x: LinkedList) -> LinkedList {
    match x {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(_, xs) => evens(*xs)
    }
  }

  #[annotate_multi]
  #[for_values(xs: LinkedList)]
  #[for_call(evens(xs) => a)]
  #[for_call(odds(xs) => b)]
  #[for_call(interleave(a, b) => c)]
  fn to_prove() -> bool {
    c == xs
  }
}
