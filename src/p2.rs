// ./problems/list_PairEvens.smt2

/*
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
(define-fun-rec
  length
  (par (a) (((x (list a))) Int))
  (match x
    ((nil 0)
     ((cons y l) (+ 1 (length l))))))
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
      (=> (= (mod (length xs) 2) 0)
        (=
          (map (lambda ((x (pair a a))) (match x (((pair2 y z) y))))
            (pairs xs))
          (evens xs))))))
*/

// NOTE: There is no definition for 'mod' built-in, so I added
// the 'is_even' fn on Nats

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p2 {
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
      LinkedList::Nil => Nil,
      LinkedList::Cons(y, z) => match z {
        LinkedList::Nil => Nil,
        LinkedList::Cons(y2, xs) => LinkedListOfPairs::Cons(
          Pair::Pair2(y, y2),
          pairs(xs)
        )
      }
    }
  }

  #[define]
  #[recursive]
  fn map<A, B>(f: Fn(A) -> B, x: List<A>) -> List<B> {
    match x {
      Nil => Nil,
      Cons(y, xs) => Cons(f(y), map(f, xs))
    }
  }

  #[define]
  #[recursive]
  fn length(x: LinkedList) -> Nat {
    match x {
      LinkedList::Nil => Nat::Z,
      LinkedList::Cons(data, l) => Nat::S(Box::new(Nat::S(l)))
    }
  }

  #[verify]
  #[for_values(xs: LinkedList)]
  fn pair_evens() -> bool {
    implies(
      is_even(length(xs)),
      map(
        |x: Pair| {
          match x {
            Pair::Pair2(y, z) => y
          }
        },
        pairs(xs)
      ) == evens(xs)
    )
  }
}
