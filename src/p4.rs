/*
// ./problems/list_PairUnpair.smt2
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  unpair
  (par (a) (((x (list (pair a a)))) (list a)))
  (match x
    ((nil (_ nil a))
     ((cons y xys)
      (match y (((pair2 z y2) (cons z (cons y2 (unpair xys))))))))))
(define-fun-rec
  pairs
  (par (b) (((x (list b))) (list (pair b b))))
  (match x
    ((nil (_ nil (pair b b)))
     ((cons y z)
      (match z
        ((nil (_ nil (pair b b)))
         ((cons y2 xs) (cons (pair2 y y2) (pairs xs)))))))))
(define-fun-rec
  length
  (par (a) (((x (list a))) Int))
  (match x
    ((nil 0)
     ((cons y l) (+ 1 (length l))))))
(prove
  (par (a)
    (forall ((xs (list a)))
      (=> (= (mod (length xs) 2) 0) (= (unpair (pairs xs)) xs)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p4 {
  #[import]
  use crate::list::linked_list::*;

  #[import]
  use crate::nat::nat::*;

  #[define]
  pub enum Pair {
    Pair2(T, T)
  }

  #[define]
  pub enum LinkedListOfPairs {
    Nil,
    Cons(Pair, Box<LinkedListOfPairs>)
  }

  #[define]
  #[recursive]
  fn pairs(x: LinkedList) -> LinkedListOfPairs {
    match x {
      LinkedList::Nil => LinkedListOfPairs::Nil,
      LinkedList::Cons(y, z) => match *z {
        LinkedList::Nil => LinkedListOfPairs::Nil,
        LinkedList::Cons(y2, xs) => LinkedListOfPairs::Cons(
          Pair::Pair2(y, y2),
          Box::new(
            pairs(*xs)
          )
        )
      }
    }
  }

  #[define]
  #[recursive]
  fn unpair(x: LinkedListOfPairs) -> LinkedList {
    match x {
      LinkedListOfPairs::Nil => LinkedList::Nil,
      LinkedListOfPairs::Cons(y, xys) => match y {
        Pair::Pair2(z, y2) => LinkedList::Cons(
          z,
          Box::new(LinkedList::Cons(y2, Box::new(unpair(*xys))))
        )
      }
    }
  }

  #[annotate_multi]
  #[for_values(xs: LinkedList)]
  #[for_call(length(xs) => xs_len)]
  #[for_call(is_even(xs_len) => a)]
  #[for_call(pairs(xs) => xs_pairs)]
  #[for_call(unpair(xs_pairs) => b)]
  fn foo() -> bool {
    implies(
      a,
      b == xs
    )
  }
}
