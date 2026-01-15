/*
; ./problems/list_append_inj_1.smt2
; Injectivity of append
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x ((nil y) ((cons z xs) (cons z (++ xs y))))))
(prove (par (a)
    (forall ((xs (list a)) (ys (list a)) (zs (list a)))
      (=> (= (++ xs zs) (++ ys zs)) (= xs ys)))))
*/

#[ravencheck::check_module]
#[declare_types(LinkedList<_>, u32)]
#[allow(dead_code)]
mod p8 {
  // Import the enum we are examining
  use crate::list::linked_list::LinkedList;

  // Make an UNINTERPRETED datatype
  #[declare]
  type T = u32;

  // Returned when we try to access a null node's data
  #[declare]
  const NULL: T = 0;

  //////////////////////////////////////////////////////////////
  // Relations

  // Wrapper for empty list constructor
  #[declare]
  fn empty() -> LinkedList<T> {
    LinkedList::<T>::Nil{}
  }

  // Wrapper for nonempty list constructor
  #[declare]
  fn node(head: T, tail: LinkedList<T>) -> LinkedList<T> {
    LinkedList::<T>::Cons{head: head, tail: Box::new(tail)}
  }

  // Gets the data from the given node (or null if empty)
  #[declare]
  fn data(cur: &LinkedList<T>) -> T {
    match cur {
      LinkedList::<T>::Cons{head, tail: _} => *head,
      _ => NULL
    }
  }

  // Gets the node after the given node (or the empty node)
  #[declare]
  fn next(cur: LinkedList<T>) -> LinkedList<T> {
    match cur {
      LinkedList::<T>::Cons{head: _, tail} => *tail,
      _ => empty()
    }
  }

  // Wrapper for appendation, called "++" in the problem
  // statement
  #[declare]
  fn append(x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    if x == empty() {
      y
    } else {
      node(data(&x), append(next(x), y))
    }
  }

  //////////////////////////////////////////////////////////////
  // Axioms

  #[assume]
  fn equality_meaning() -> bool {
    forall(|x: LinkedList<T>, y: LinkedList<T>| {
      implies(
        x == y,
        data(&x) == data(&y) && next(x) == next(y)
      ) && implies(
        data(&x) == data(&y) && next(x) == next(y),
        x == y
      )
    })
  }

  #[assume]
  fn appendation_meaning() -> bool {
    forall(|x: LinkedList<T>, y: LinkedList<T>, item: T| {
      implies(
        y == append(node(item, empty()), x),
        data(&y) == item && next(y) == x
      ) && implies(
        data(&y) == item && next(y) == x,
        y == append(node(item, empty()), x)
      )
    })
  }

  #[assume]
  fn empty_is_empty() -> bool {
    data(empty()) == NULL && next(empty()) == empty()
  }

  // Axiom: Appending identical items preserves equality
  #[assume]
  fn appendation_equality() -> bool {
    forall(|l: LinkedList<T>, r: LinkedList<T>, item: T| {
      implies(
        l == r,
        append(
          l, node(item, empty())
        ) == append(
          r, node(item, empty())
        )
      ) && implies(
        append(
          l, node(item, empty())
        ) == append(
          r, node(item, empty())
        ),
        l == r
      )
    })
  }

  // Axiom: appending nothing does not change a list
  #[assume]
  fn append_nil() -> bool {
    forall(|x: LinkedList<T>| {
      append(x, empty()) == x
    })
  }

  //////////////////////////////////////////////////////////////
  // The property we want to prove (injectivity)

  // This *is* proven
  #[verify]
  fn relaxed() -> bool {
    forall(|xs: LinkedList<T>,
            ys: LinkedList<T>,
            zs: LinkedList<T>| {
      implies(xs == ys, append(xs, zs) == append(ys, zs))
    })
  }

  #[verify]
  fn injectivity_of_append() -> bool {
    forall(|xs: LinkedList<T>,
            ys: LinkedList<T>,
            zs: LinkedList<T>| {
      implies(append(xs, zs) == append(ys, zs), xs == ys)
    })
  }
}
