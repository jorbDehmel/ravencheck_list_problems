// ./problems/list_append_inj_2.smt2

/*
; Injectivity of append
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x ((nil y) ((cons z xs) (cons z (++ xs y))))))
(prove (par (a)
    (forall ((xs (list a)) (ys (list a)) (zs (list a)))
      (=> (= (++ xs ys) (++ xs zs)) (= ys zs)))))
*/

#[ravencheck::check_module]
#[declare_types(LinkedList<_>, u32)]
#[allow(dead_code)]
mod p9 {
  use crate::list::linked_list::LinkedList;

  #[declare]
  type T = u32;

  #[declare]
  const NULL: T = 0;

  //////////////////////////////////////////////////////////////
  // Relations

  // Wrapper for nil list constructor
  #[declare]
  fn nil() -> LinkedList<T> {
    LinkedList::<T>::Nil{}
  }

  // Wrapper for nonempty list constructor
  #[declare]
  fn cons(head: T, tail: LinkedList<T>) -> LinkedList<T> {
    LinkedList::<T>::Cons{head: head, tail: Box::new(tail)}
  }

  // Gets the data from the given node (or null if nil)
  #[declare]
  fn data(cur: &LinkedList<T>) -> T {
    match cur {
      LinkedList::<T>::Cons{head, tail: _} => *head,
      _ => NULL
    }
  }

  // Gets the node after the given node (or the nil node)
  #[declare]
  fn next(cur: LinkedList<T>) -> LinkedList<T> {
    match cur {
      LinkedList::<T>::Cons{head: _, tail} => *tail,
      _ => nil()
    }
  }

  // Wrapper for appendation, called "++" in the problem
  // statement
  #[declare]
  fn append(x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    if x == nil() {
      y
    } else {
      cons(data(&x), append(next(x), y))
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
  fn equality_meaning_backward() -> bool {
    forall(|t: T, x: LinkedList<T>, y: LinkedList<T>| {
      implies(
        cons(t, x) == cons(t, y),
        x == y
      )
    })
  }

  #[assume]
  fn appendation_meaning() -> bool {
    forall(|x: LinkedList<T>, y: LinkedList<T>, item: T| {
      implies(
        y == append(cons(item, nil()), x),
        data(&y) == item && next(y) == x
      ) && implies(
        data(&y) == item && next(y) == x,
        y == append(cons(item, nil()), x)
      )
    })
  }

  #[assume]
  fn empty_is_empty() -> bool {
    data(nil()) == NULL && next(nil()) == nil()
  }

  // Axiom: Appending identical items preserves equality
  // (l == r) iff (l + (item, ()) == (r + (item, ())))
  #[assume]
  fn appendation_equality() -> bool {
    forall(|l: LinkedList<T>, r: LinkedList<T>, item: T| {
      implies(
        l == r,
        append(
          l, cons(item, nil())
        ) == append(
          r, cons(item, nil())
        )
      ) && implies(
        append(
          l, cons(item, nil())
        ) == append(
          r, cons(item, nil())
        ),
        l == r
      )
    })
  }

  // Axiom: appending nothing does not change a list
  #[assume]
  fn append_nil() -> bool {
    forall(|x: LinkedList<T>| {
      append(x, nil()) == x
    })
  }

  // Appending x ++ (t, y) is the same as (x ++ (t, ())) ++ y
  #[assume]
  fn append_item() -> bool {
    forall(|x: LinkedList<T>, y: LinkedList<T>, t: T| {
      append(x, cons(t, y))
      ==
      append(append(x, cons(t, nil())), y)
    })
  }

  // (x ++ y) ++ z is the same as x ++ (y ++ z)
  #[assume]
  fn associativity_of_append() -> bool {
    forall(|a: LinkedList<T>, b: LinkedList<T>, c: LinkedList<T>| {
      append(a, append(b, c)) == append(append(a, b), c)
    })
  }

  //////////////////////////////////////////////////////////////
  // The property we want to prove (injectivity)

  // #[verify]
  // fn injectivity_of_append_2() -> bool {
  //   forall(|xs: LinkedList<T>,
  //           ys: LinkedList<T>,
  //           zs: LinkedList<T>| {
  //     implies(append(xs, ys) == append(xs, zs), ys == zs)
  //   })
  // }
}
