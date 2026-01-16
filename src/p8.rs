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

  // Returned when we try to access a null cons's data
  #[declare]
  const NULL: T = 0;

  #[declare]
  const NIL: LinkedList<T> = LinkedList::<T>::Nil{};

  //////////////////////////////////////////////////////////////
  // Relations

  // Wraps equality for nodes
  #[define]
  fn eq(a: &LinkedList<T>, b: &LinkedList<T>) -> bool {
    a == b
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

  #[assume]
  fn data_eq_pres() -> bool {
    forall(|a: LinkedList<T>, b: LinkedList<T>| {
      implies(eq(a, b), data(&a) == data(&b))
    })
  }

  // Gets the node after the given node (or the nil node)
  #[declare]
  fn next(cur: LinkedList<T>) -> LinkedList<T> {
    match cur {
      LinkedList::<T>::Cons{head: _, tail} => *tail,
      _ => NIL
    }
  }

  // Wrapper for appendation, called "++" in the problem
  // statement. Note: I've done some reformatting here
  #[define]
  #[recursive]
  fn append(x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    if eq(&x, &NIL) {
      y
    } else if eq(&y, &NIL) {
      x
    } else {
      cons(data(&x), append(next(x), y))
    }
  }

  //////////////////////////////////////////////////////////////
  // Axioms
  // Note: Many of these are likely redundant. Hopefully none
  // are cheating.

  // eq is total
  #[assume]
  #[for_inst(eq(a, b))]
  fn eq_totality() -> bool {
    forall(|a: LinkedList<T>, b: LinkedList<T>| {
      eq(a, b) || !eq(a, b)
    })
  }

  // next is total
  #[assume]
  #[for_inst(next(a))]
  fn next_totality() -> bool {
    forall(|a: LinkedList<T>| {
      let _ = next(a);
      true
    })
  }

  // data is total
  #[assume]
  #[for_inst(data(a))]
  fn data_totality() -> bool {
    forall(|a: LinkedList<T>| {
      let _ = data(a);
      true
    })
  }

  #[assume]
  #[for_inst(next(append(cons(a, NIL), y)))]
  #[for_inst(data(append(cons(a, NIL), y)))]
  fn simple_append() -> bool {
    forall(|a: T, y: LinkedList<T>| {
      eq(next(append(cons(a, NIL), y)), y) &&
      data(append(cons(a, NIL), y)) == a
    })
  }

  // Cons meaning
  #[assume]
  #[for_inst(eq(&x, &y))]
  #[for_inst(eq(&cons(a, x), &cons(b, y)))]
  fn cons_meaning() -> bool {
    forall(|a: T, b: T, x: LinkedList<T>, y: LinkedList<T>| {
      implies(
        a == b && eq(&x, &y),
        eq(&cons(a, x), &cons(b, y))
      )
    })
  }

  // Data meaning
  #[assume]
  #[for_inst(data(cons(a, x)))]
  fn data_meaning() -> bool {
    forall(|a: T, x: LinkedList<T>| {
      data(cons(a, x)) == a
    })
  }

  // Next meaning
  #[assume]
  #[for_inst(eq(next(cons(a, x)), x))]
  #[for_inst(eq(cons(a, x), y))]
  #[for_inst(eq(x, next(y)))]
  #[for_inst(data(&y))]
  fn next_meaning() -> bool {
    forall(|a: T, x: LinkedList<T>| {
      eq(next(cons(a, x)), x)
    }) && forall(|a: T, x: LinkedList<T>, y: LinkedList<T>| {
      implies(
        eq(cons(a, x), y),
        a == data(&y) && eq(x, next(y))
      ) && implies(
        a == data(&y) && eq(x, next(y)),
        eq(cons(a, x), y)
      )
    })
  }

  // Axiom: (t, x) == (u, y) iff t == u and x == y
  #[assume]
  #[for_inst(data(&x))]
  #[for_inst(data(&y))]
  #[for_inst(next(x))]
  #[for_inst(next(y))]
  fn equality_meaning() -> bool {
    forall(|x: LinkedList<T>, y: LinkedList<T>| {
      implies(
        eq(x, y),
        data(&x) == data(&y) && eq(next(x), next(y))
      ) && implies(
        data(&x) == data(&y) && eq(next(x), next(y)),
        eq(x, y)
      )
    })
  }

  // Axiom: appending nothing does not change a list
  #[assume]
  #[for_inst(append(x, NIL))]
  fn append_nil() -> bool {
    forall(|x: LinkedList<T>| {
      eq(append(x, NIL), x)
    })
  }

  #[assume]
  #[for_inst(cons(a, x))]
  #[for_inst(cons(b, x))]
  fn prepend() -> bool {
    forall(|x: LinkedList<T>, a: T, b: T| {
      implies(
        eq(
          cons(a, x),
          cons(b, x)
        ),
        a == b
      )
    })
  }

  // Axiom: The special NIL object is the end of lists
  #[assume]
  #[for_inst(next(NIL))]
  fn empty_is_empty() -> bool {
    eq(next(NIL), NIL)
  }

  #[assume]
  #[for_inst(append(x, cons(t, y)))]
  #[for_inst(append(append(x, cons(t, NIL)), y))]
  fn append_item() -> bool {
    forall(|x: LinkedList<T>, y: LinkedList<T>, t: T| {
      eq(
        append(x, cons(t, y)),
        append(append(x, cons(t, NIL)), y)
      )
    })
  }

  #[assume]
  #[for_inst(eq(l, r))]
  #[for_inst(eq(append(l, z), append(r, z)))]
  fn appendation_equality() -> bool {
    forall(|l: LinkedList<T>, r: LinkedList<T>, t: T| {
      let z = cons(t, NIL);
      implies(
        eq(l, r),
        eq(append(l, z), append(r, z))
      ) && implies(
        eq(append(l, z), append(r, z)),
        eq(l, r)
      )
    })
  }

  //////////////////////////////////////////////////////////////
  // The property we want to prove (injectivity)

  #[verify]
  fn injectivity_of_append() -> bool {
    forall(|xs: LinkedList<T>,
            ys: LinkedList<T>,
            zs: LinkedList<T>| {
      implies(eq(append(xs, zs), append(ys, zs)), eq(xs, ys))
    })
  }
}
