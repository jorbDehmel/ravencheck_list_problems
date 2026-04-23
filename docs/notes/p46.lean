inductive LinkedList (a: Type u) where
  | nil : LinkedList a
  | cons (h : a) (t : LinkedList a) : LinkedList a

namespace LinkedList

def weird_concat (x : LinkedList (LinkedList a)) : LinkedList a :=
  match x with
  | nil => nil
  | cons y xss => (
    match y with
    | nil => weird_concat xss
    | cons z xs => cons z (weird_concat (cons xs xss))
  )

def append (x : LinkedList a) (y : LinkedList a) : LinkedList a :=
  match x with
  | nil => y
  | cons z xs => cons z (append xs y)

def concat (x : LinkedList (LinkedList a)) : LinkedList a :=
  match x with
  | nil => nil
  | cons y xs => append y (concat xs)

----------------------------------------------------------------

axiom lemma_1 {a : Type v}
    : (concat (@LinkedList.nil (LinkedList a))) = (weird_concat (@LinkedList.nil (LinkedList a)))

-- DOESN'T WORK IN RAVENCHECK
theorem lemma_2 (l_data : LinkedList a)
                (l_next : LinkedList (LinkedList a))
    : (concat (cons l_data l_next)) = (append l_data (concat l_next)) :=
  rfl

theorem lemma_4 (thm : concat a = weird_concat a)
    : (append d (concat a)) = (append d (weird_concat a)) := by
  exact congrArg (fun b => append d b) thm

theorem lemma_10 (n : LinkedList a) : append nil n = n
    := by
  rfl

theorem lemma_11 : (weird_concat ((@LinkedList.cons (LinkedList a)) ((@LinkedList.nil a)) n) = weird_concat n)
  := by rfl

-- DOESN'T WORK IN RAVENCHECK
theorem lemma_12 : (weird_concat n = weird_concat (cons nil n))
    :=
  Eq.symm lemma_11

-- DOESN'T WORK IN RAVENCHECK
theorem lemma_5 (n : LinkedList (LinkedList a))
    : append nil (weird_concat n) = weird_concat (cons nil n)
    := by
  exact Eq.trans
    (lemma_10 (weird_concat n))
    lemma_12

-- DOESN'T WORK IN RAVENCHECK
theorem lemma_6
    : (append (cons ldd ldn) (weird_concat ln)) = (cons ldd (append ldn (weird_concat ln)))
    := by
  rfl

theorem lemma_7 (ldd : a) (ih : append ldn (weird_concat ln) = weird_concat (cons ldn ln))
    : (cons ldd (append ldn (weird_concat ln)) = cons ldd (weird_concat (cons ldn ln)))
    := by
  exact congrArg (fun arg => cons ldd arg) ih

theorem lemma_9 (ih : append ldn (weird_concat ln) = weird_concat (cons ldn ln))
    : (cons ldd (weird_concat (cons ldn ln)) = cons ldd (append ldn (weird_concat ln)))
    := by
  grind

-- DOESN'T WORK IN RAVENCHECK
theorem lemma_8 (ldd : a) (ih : append ldn (weird_concat ln) = weird_concat (cons ldn ln))
    : ((cons ldd (weird_concat (cons ldn ln))) = (weird_concat (cons (cons ldd ldn) ln)))
    := by
  sorry

-- DOESN'T WORK IN RAVENCHECK
theorem lemma_3 (l_data : LinkedList a)
                (ln : LinkedList (LinkedList a))
    : (append l_data (weird_concat ln)) = (weird_concat (cons l_data ln))
    := by
  induction l_data with
  | nil => exact lemma_5 ln
  | cons ldd ldn ih =>
    exact Eq.trans
      lemma_6
      (Eq.trans
        (lemma_7 ldd ih)
        (lemma_8 ldd ih)
      )

-- DOESN'T WORK IN RAVENCHECK
theorem p46 (x : LinkedList (LinkedList a))
    : (concat x) = (weird_concat x)
    := by
  induction x with
  | nil => exact lemma_1
  | cons data next ih =>
    exact Eq.trans
      (lemma_2 data next)
      (Eq.trans
        (lemma_4 ih)
        (lemma_3 data next)
      )
