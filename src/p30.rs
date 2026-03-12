// ./problems/list_nat_elem_map.smt2

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
mod p30 {
  #[define]
  #[derive(PartialEq, Clone)]
  enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  // This is an instance of the more generic one defined by
  // the spec
  #[define]
  #[recursive]
  fn map<A>(f: fn(A) -> A, x: LinkedList<A>) -> LinkedList<A> {
    match x {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(y, xs) =>
        LinkedList::<A>::Cons(
          f(y),
          Box::new(map::<A>(f, *xs))
        )
    }
  }

  #[define]
  #[recursive]
  fn elem<A: PartialEq>(x: A, y: LinkedList<A>) -> bool {
    match y {
      LinkedList::<A>::Nil => false,
      LinkedList::<A>::Cons(z, xs) => z == x || elem::<A>(x, *xs)
    }
  }

  #[declare]
  #[phantom]
  fn f<A>(_: A) -> A {}

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p30<A>(y: A) -> bool {
    implies(
      elem::<A>(y, map::<A>(f::<A>, xs)),
      exists(
        |x: A| {
          def_and_eq(f::<A>(x), y)
        }
      ) && elem::<A>(y, xs)
    )
  }
}
