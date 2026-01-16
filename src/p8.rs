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

  #[define]
  #[total]
  fn eq(a: &LinkedList<T>, b: &LinkedList<T>) -> bool {
    a == b
  }

  // This is safe from sort cycles
  #[declare]
  #[total]
  fn data(cur: &LinkedList<T>) -> T {
    match cur {
      LinkedList::<T>::Cons{head, tail: _} => *head,
      _ => NULL
    }
  }

  #[declare]
  #[total]
  fn is_next(cur: &LinkedList<T>,
             candidate: LinkedList<T>) -> bool {
    match cur {
      LinkedList::<T>::Cons{head: _, tail} =>
        eq(&*tail, &candidate),
      _ => eq(&NIL, &candidate)
    }
  }

  //////////////////////////////////////////////////////////////
  // Appendation

  #[declare]
  fn is_appendation(x: LinkedList<T>, y: LinkedList<T>,
                    z: LinkedList<T>) -> bool {
    if data(&x) != data(&z) {
      false
    } else {
      match x {
        LinkedList::<T>::Cons{tail: x_next, ..} => match z {
          LinkedList::<T>::Cons{tail: z_next, ..} =>
            is_appendation(
              *x_next, y, *z_next
            ),
          _ => false
        },
        _ => eq(&z, &NIL)
      }
    }
  }

  // (a ++ b == d) and (a ++ c == d) iff b == c
  #[assume]
  fn appendation_axiom() -> bool {
    forall(|a: LinkedList<T>, b: LinkedList<T>,
            c: LinkedList<T>, d: LinkedList<T>| {
      implies(
        is_appendation(a, b, d) && is_appendation(a, c, d),
        b == c
      ) && implies(
        b == c,
        is_appendation(a, b, d) && is_appendation(a, c, d)
      )
    })
  }

  //////////////////////////////////////////////////////////////
  // WTS

  #[annotate_multi]
  #[for_values(xs: LinkedList<T>, ys: LinkedList<T>,
               zs: LinkedList<T>, a: LinkedList<T>,
               b: LinkedList<T>)]
  fn injectivity_of_append() -> bool {
    implies(
      is_appendation(xs, zs, a) &&
      is_appendation(ys, zs, b) &&
      eq(a, b),
      eq(xs, ys)
    )
  }
}
