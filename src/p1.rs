// ./problems/list_Interleave.smt2

/*
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))

(define-fun-rec
  interleave
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (interleave y xs))))))

(define-funs-rec
  ((evens
    (par (a) (((x (list a))) (list a))))
   (odds
    (par (a) (((x (list a))) (list a)))))
  ((match x
     ((nil (_ nil a))
      ((cons y xs) (cons y (odds xs)))))
   (match x
     ((nil (_ nil a))
      ((cons y xs) (evens xs))))))

(prove
  (par (a)
    (forall ((xs (list a))) (= (interleave (evens xs) (odds xs)) xs))))
*/

#[ravencheck::check_module]
#[declare_types(LinkedList<_>, u32)]
#[allow(dead_code)]
mod p1 {
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

  // Gets the node after the given node (or the nil node)
  #[declare]
  fn next(cur: &LinkedList<T>) -> LinkedList<T> {
    match cur {
      LinkedList::<T>::Cons{head: _, tail} => *tail.clone(),
      _ => NIL
    }
  }

  //////////////////////////////////////////////////////////////

  #[define]
  #[recursive]
  fn interleave(x: LinkedList<T>, y: LinkedList<T>) -> LinkedList<T> {
    if eq(&x, &NIL) {
      y
    } else {
      cons(data(&x), interleave(y, next(&x)))
    }
  }

  // #[define]
  // #[recursive]
  // fn evens(x: LinkedList<T>) -> LinkedList<T> {
  //   if eq(&x, &NIL) {
  //     x
  //   } else {
  //     cons(data(&x), odds(next(&x)))
  //   }
  // }

  // #[define]
  // #[recursive]
  // fn odds(x: LinkedList<T>) -> LinkedList<T> {
  //   if eq(&x, &NIL) {
  //     x
  //   } else {
  //     evens(next(&x))
  //   }
  // }

  //////////////////////////////////////////////////////////////
  // To prove

  // #[annotate_multi]
  // #[for_values(xs: LinkedList<T>)]
  // fn to_prove() -> bool {
  //   eq(interleave(evens(xs), odds(xs)), xs)
  // }
}
