// ./problems/list_append_inj_1.smt2

/*
; Injectivity of append
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(prove
  (par (a)
    (forall ((xs (list a)) (ys (list a)) (zs (list a)))
      (=> (= (++ xs zs) (++ ys zs)) (= xs ys)))))
*/

#[ravencheck::check_module]
#[declare_types(LinkedList<_>)]
#[allow(dead_code)]
mod p8 {
  use crate::list::linked_list::LinkedList;

  // "++"
  #[declare]
  fn append_lists<T: Clone>(
    x: LinkedList<T>,
    y: LinkedList<T>) -> LinkedList<T> {
    match x {
      LinkedList::Nil => y,
      LinkedList::Cons{head, tail} => LinkedList::Cons{
        head: head,
        tail: Box::new(
          append_lists(
            (*tail).clone(),
            y.clone()
        ))
      }
    }
  }

  // "="
  #[declare]
  fn lists_are_eq<T: Clone + PartialEq>(
    x: LinkedList<T>,
    y: LinkedList<T>) -> bool {
    match x {
      // If x is empty, equal iff y is empty
      LinkedList::Nil => match y {
        LinkedList::Nil => true,
        _ => false
      },
      // Else, x is nonempty
      LinkedList::Cons{head: x_head, tail: x_tail} => match y {
        // Else, equal iff the current elements are and the
        // remainders of each list are
        LinkedList::Cons{head: x_head, tail: y_tail} =>
          lists_are_eq(*x_tail, *y_tail),
        // Else, nonequal
        _ => false,
      }
    }
  }

  // The property we want to prove (injectivity) on arbitrary
  // parameter type
  #[verify]
  fn injectivity_of_append<T: Clone + PartialEq>() -> bool {
    // For any three like-typed lists `xs, ys, zs`,
    forall(|xs: LinkedList<T>,
            ys: LinkedList<T>,
            zs: LinkedList<T>| {
      // append(xs, zs) == append(ys, zs) implies that xs == ys
      implies(
        lists_are_eq::<T>(
          append_lists::<T>(xs, zs),
          append_lists::<T>(ys, zs)
        ),
        lists_are_eq::<T>(xs, ys)
      )
    })
  }
}
