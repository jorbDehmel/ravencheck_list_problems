/*
// ./problems/list_PairOdds.smt2
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
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
  map
  (par (a b) (((f (=> a b)) (x (list a))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons y xs) (cons (@ f y) (map f xs))))))
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
    (forall ((xs (list a)))
      (=
        (map (lambda ((x (pair a a))) (match x (((pair2 y z) z))))
          (pairs xs))
        (odds xs)))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p3 {
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
          Box::new(pairs(*xs))
        )
      }
    }
  }

  #[define]
  #[recursive]
  fn map(f: fn(Pair) -> T, x: LinkedListOfPairs) -> LinkedList {
    match x {
      LinkedListOfPairs::Nil => LinkedList::Nil,
      LinkedListOfPairs::Cons(y, xs) => LinkedList::Cons(
        f(y),
        Box::new(map(f, *xs))
      )
    }
  }

  #[define]
  #[recursive]
  fn length(x: LinkedList) -> Nat {
    match x {
      LinkedList::Nil => Nat::Z,
      LinkedList::Cons(_data, l) => Nat::S(Box::new(length(*l)))
    }
  }

  #[define]
  #[recursive]
  fn evens(x: LinkedList) -> LinkedList {
    match x {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(y, xs) => LinkedList::Cons(
        y,
        Box::new(odds(*xs))
      )
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
  #[for_call(pairs(xs) => pairs_xs)]
  #[for_call(odds(xs) => odds_xs)]
  fn pair_odds() -> bool {
    map(
      |x: Pair| {
        match x {
          Pair::Pair2(y, z) => z
        }
      },
      pairs_xs
    ) == odds_xs
  }
}
