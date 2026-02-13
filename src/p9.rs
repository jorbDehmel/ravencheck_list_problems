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

// Lemmas: 0
// Verification time: 0.09s

#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p9 {
  #[define]
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
