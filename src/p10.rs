// ./problems/list_assoc.smt2

/*
; List monad laws
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
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
(prove
  (par (a b c)
    (forall ((m (list a)) (f (=> a (list b))) (g (=> b (list c))))
      (= (>>= (>>= m f) g) (>>= m (lambda ((x a)) (>>= (@ f x) g)))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p10 {
  #[import]
  use crate::poly_list::poly_linked_list::*;

  #[define]
  #[recursive]
  fn right_right_equal<A, B: PartialEq>(x: LinkedList<A>, y: fn(A) -> LinkedList<B>) -> LinkedList<B> {
    match x {
      LinkedList::<A>::Nil => LinkedList::<B>::Nil,
      LinkedList::<A>::Cons(z, xs) => append::<B>(
        y(z),
        right_right_equal::<A, B>(*xs, y)
      )
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  fn p10<A, B, C>(m: LinkedList<A>, f: fn(A) -> LinkedList<B>, g: fn(B) -> LinkedList<C>) -> bool {
    right_right_equal::<B, C>(
      right_right_equal::<A, B>(m, f),
      g
    )
    ==
    right_right_equal::<A, C>(
      m,
      |x: A| {
        right_right_equal::<B, C>(f(x), g)
      }
    )
  }
}
