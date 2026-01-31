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
        Box::new(
          match *xs {
            LinkedList::Nil => LinkedList::Nil,
            LinkedList::Cons(_data, xss) => evens(*xss)
          }
        )
      )
    }
  }

  #[define]
  #[recursive]
  fn odds(x: LinkedList) -> LinkedList {
    match x {
      LinkedList::Nil => LinkedList::Nil,
      LinkedList::Cons(_data, xs) => evens(*xs)
    }
  }

  #[annotate_multi]
  #[for_values(xs: LinkedList, aux_len: Nat)]
  #[for_call(length(xs) => xs_length)]
  #[for_call(is_even(aux_len) => xs_len_even)]
  #[for_call(evens(xs) => xs_evens)]
  #[for_call(pairs(xs) => xs_pairs)]
  fn pair_evens() -> bool {
    implies(
      xs_length == aux_len,
      implies(
        xs_len_even,
        map(
          |x: Pair| {
            match x {
              Pair::Pair2(y, z) => y
            }
          },
          xs_pairs
        ) == xs_evens
      )
    )
  }
}
