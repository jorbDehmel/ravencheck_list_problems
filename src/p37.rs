// ./problems/list_nat_perm_trans.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  (par (a) (((x (=> a (=> a Bool))) (y a) (z (list a))) (list a)))
  (match z
    ((nil (_ nil a))
     ((cons y2 ys)
      (ite (@ (@ x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  (par (a) (((x (list a)) (y (list a))) Bool))
  (match x
    ((nil
      (match y
        ((nil true)
         ((cons z x2) false))))
     ((cons x3 xs)
      (and (elem x3 y)
        (isPermutation xs
          (deleteBy (lambda ((x4 a)) (lambda ((x5 a)) (= x4 x5))) x3 y)))))))
(prove
  (par (a)
    (forall ((xs (list a)) (ys (list a)) (zs (list a)))
      (=> (isPermutation xs ys)
        (=> (isPermutation ys zs) (isPermutation xs zs))))))
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p37 {
  #[derive(PartialEq, Clone)]
  #[define]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  fn elem<T: PartialEq>(x: T, y: LinkedList<T>) -> bool {
    match y {
      LinkedList::<T>::Nil => false,
      LinkedList::<T>::Cons(z, xs) => z == x || elem::<T>(x, *xs)
    }
  }

  #[define]
  #[recursive]
  fn delete_by<A: PartialEq + Clone, F: Fn(A, A) -> bool>(x: F, y: A, z: LinkedList<A>) -> LinkedList<A> {
    match z {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(y2, ys) =>
        if x(y.clone(), y2.clone()) {
          *ys
        } else {
          LinkedList::<A>::Cons(y2, Box::new(delete_by::<A, F>(x, y, *ys)))
        }
    }
  }

  #[define]
  #[recursive]
  fn is_permutation<A: PartialEq + Clone>(x: LinkedList<A>, y: LinkedList<A>) -> bool {
    match x {
      LinkedList::<A>::Nil => match y {
        LinkedList::<A>::Nil => true,
        LinkedList::<A>::Cons(_y_data, _y_next) => false
      },
      LinkedList::<A>::Cons(x_data, x_next) =>
        elem::<A>(x_data.clone(), y.clone())
        &&
        is_permutation::<A>(
          *x_next,
          delete_by::<A, fn(A, A) -> bool>(
            |x4: A, x5: A| {
              x4 == x5
            },
            x_data,
            y
          )
        )
    }
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>, ys: LinkedList<A>, zs: LinkedList<A>)]
  fn p37<A>() -> bool {
    implies(
      is_permutation::<A>(xs, ys),
      implies(
        is_permutation::<A>(ys, zs),
        is_permutation::<A>(xs, zs)
      )
    )
  }
}
