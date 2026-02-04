// /*
// ; Injectivity of append
// (declare-datatype
//   list (par (a) ((nil) (cons (head a) (tail (list a))))))
// (define-fun-rec
//   ++
//   (par (a) (((x (list a)) (y (list a))) (list a)))
//   (match x
//     ((nil y)
//      ((cons z xs) (cons z (++ xs y))))))
// (prove
//   (par (a)
//     (forall ((xs (list a)) (ys (list a)) (zs (list a)))
//       (=> (= (++ xs ys) (++ xs zs)) (= ys zs)))))
// */

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p9 {
  #[import]
  use crate::poly_list::poly_linked_list::*;

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>, ys: LinkedList<T>, zs: LinkedList<T>)]
  fn injectivity_of_append_2<T: PartialEq>() -> bool {
    implies(
      append::<T>(xs, ys) == append::<T>(xs, zs),
      ys == zs
    )
  }
}
