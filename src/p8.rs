// ./problems/list_append_inj_1.smt2

/*
; Injectivity of append

; Defines the list datatype
(declare-datatype
  list
  (par
    (a)
    (
      (nil)
      (cons
        (head a)
        (tail
          (list a)
        )
      )
    )
  )
)

; The appendation function for lists
(define-fun-rec
  ++
  (par
    (a)
    (
      (
        (x
          (list a)
        )
        (y
          (list a)
        )
      )
      (list a)
    )
  )
  (match x
    (
      (nil y)
      (
        (cons z xs)
        (cons z
          (++ xs y)
        )
      )
    )
  )
)

; The thing to prove
(prove
  (par
    (a)
    (forall
      (
        (xs
          (list a)
        )
        (ys
          (list a)
        )
        (zs
          (list a)
        )
      )
      (=>
        (=
          (++ xs zs)
          (++ ys zs)
        )
        (= xs ys)
      )
    )
  )
)
*/

#[ravencheck::check_module]
#[allow(dead_code)]
mod p8 {
  use crate::list::linked_list::LinkedList;

  /*
  For any generic type,
  For any three like-typed lists `xs, ys, zs`,
  `conjoin(xs, zs) == conjoin(ys, zs)` implies that `xs == ys`
  */
}
