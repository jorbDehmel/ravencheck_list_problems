
# Problems which did not need any lemmas (5, 9, 11, 14, 22, and 44)

These problems all verified without any additional effort. The
following are their translations from SMT2 into rust.

## P5

SMT2:

```txt
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  select
  (par (a)
    (((x a) (y (list (pair a (list a))))) (list (pair a (list a)))))
  (match y
    ((nil (_ nil (pair a (list a))))
     ((cons z x2)
      (match z
        (((pair2 y2 ys) (cons (pair2 y2 (cons x ys)) (select x x2)))))))))
(define-fun-rec
  select2
  (par (a) (((x (list a))) (list (pair a (list a)))))
  (match x
    ((nil (_ nil (pair a (list a))))
     ((cons y xs) (cons (pair2 y xs) (select y (select2 xs)))))))
(define-fun-rec
  map
  (par (a b) (((f (=> a b)) (x (list a))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons y xs) (cons (@ f y) (map f xs))))))
(prove
  (par (b)
    (forall ((xs (list b)))
      (=
        (map (lambda ((x (pair b (list b)))) (match x (((pair2 y z) y))))
          (select2 xs))
        xs))))
```

Naive implementation:

```rust
#[ravencheck::check_module]
#[allow(dead_code)]
#[allow(unused_imports)]
mod p5 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum Pair<F, S> {
    Pair2(F, S)
  }

  #[define]
  #[recursive]
  fn select<T: PartialEq + Clone>(x: T, y: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match y {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(z, x2) =>
        match z {
          Pair::<T, LinkedList<T>>::Pair2(y2, ys) =>
            LinkedList::<Pair<T, LinkedList<T>>>::Cons(
              Pair::<T, LinkedList<T>>::Pair2(
                y2,
                LinkedList::<T>::Cons(x.clone(), Box::new(ys))
              ),
              Box::new(select::<T>(x, *x2))
            )
        }
    }
  }

  #[define]
  #[recursive]
  fn select2<T: PartialEq + Clone>(x: LinkedList<T>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match x {
      LinkedList::<T>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<T>::Cons(y, xs) =>
        LinkedList::<Pair<T, LinkedList<T>>>::Cons(
          Pair::<T, LinkedList<T>>::Pair2(y.clone(), *xs.clone()),
          Box::new(select::<T>(y, select2::<T>(*xs)))
        )
    }
  }

  #[define]
  #[recursive]
  fn map<T: PartialEq + Clone>(f: fn(Pair<T, LinkedList<T>>) -> T, x: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<T> {
    match x {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil => LinkedList::<T>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(y, xs) => LinkedList::<T>::Cons(f(y), Box::new(map::<T>(f, *xs)))
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn list_select<T: PartialEq + Clone>() -> bool {
    map::<T>(
      |x: Pair<T, LinkedList<T>>| {
        match x {
          Pair::<T, LinkedList<T>>::Pair2(y, z) => y
        }
      },
      select2::<T>(xs)
    ) == xs
  }
}
```

## P9

SMT2:

```txt
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
      (=> (= (++ xs ys) (++ xs zs)) (= ys zs)))))
```

Naive implementation:

```rust
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
```

## P14

SMT2:

```txt
; ./problems/list_elem.smt2
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(declare-const undefined (par (a) a))
(define-fun-rec
  elem
  (par (a) (((x a) (y (list a))) Bool))
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  at
  (par (a) (((x (list a)) (y Int)) a))
  (match x
    ((nil (_ undefined a))
     ((cons z x2)
      (ite (= y 0) z (ite (> y 0) (at x2 (- y 1)) (_ undefined a)))))))
(prove
  (par (a)
    (forall ((x a) (xs (list a)))
      (=> (elem x xs) (exists ((y Int)) (= x (at xs y)))))))
```

Naive implementation:

```rust
#[ravencheck::check_module]
#[allow(dead_code)]
mod p14 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum MyOpt<T> {
    Some(T),
    None
  }

  // Positive numbers are successors of P, negative numbers are
  // successors of N. Zero is the only number whose
  // representation is ambiguous: It can be either P or N.
  // Therefore, these two should be assumed to be equal. I was
  // going to use Z/S/P (zero, successor-of, predecessor-of),
  // but that would introduce way too much complexity for
  // equality (EG S(Z) == P(S(S(Z)))). Another way is to just
  // wrap a natural number in a positive or negative option.
  // However, this verifies so I'm not gonna worry about it.
  #[define]
  #[derive(PartialEq, Clone)]
  enum Int {
    P,
    N,
    S(Box<Int>)
  }

  #[assume]
  fn plus_minus_zero_eq() -> bool {
    Int::P == Int::N
  }

  #[define]
  #[recursive]
  fn is_positive(x: Int) -> bool {
    match x {
      Int::S(previous) => match *previous.clone() {
        Int::P => true,
        Int::N => false,
        Int::S(_prev) => is_positive(*previous)
      },
      Int::P => false,
      Int::N => false
    }
  }

  // This only takes positives herein, but generally functions
  // to reduce the magnitude by 1, with a fixed point at 0.
  #[define]
  fn previous(x: Int) -> Int {
    match x {
      Int::S(p) => *p,
      Int::N => x,
      Int::P => x
    }
  }

  #[define]
  fn is_zero(x: Int) -> bool {
    match x {
      Int::P => true,
      Int::N => true,
      Int::S(_prev) => false
    }
  }

  #[define]
  #[recursive]
  pub fn elem<T: PartialEq>(x: T, y: LinkedList<T>) -> bool {
    match y {
      LinkedList::<T>::Nil => false,
      LinkedList::<T>::Cons(z, xs) =>
        z == x || elem::<T>(x, *xs)
    }
  }

  #[define]
  #[recursive]
  fn at<T: PartialEq + Clone>(x: LinkedList<T>, y: Int) -> MyOpt<T> {
    match x {
      LinkedList::<T>::Nil => MyOpt::<T>::None,
      LinkedList::<T>::Cons(z, x2) =>
        if is_zero(y.clone()) {
          MyOpt::<T>::Some(z)
        } else {
          if is_positive(y.clone()) {
            at::<T>(*x2, previous(y))
          } else {
            MyOpt::<T>::None
          }
        }
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn p14<T: PartialEq + Clone>(x: T) -> bool {
    implies(
      elem::<T>(x, xs),
      exists(|y: Int| {
        def_and_eq(
          at::<T>(xs, y),
          MyOpt::<T>::Some(x)
        )
      })
    )
  }
}
```

## P22

SMT2:

```txt
; ./problems/list_nat_Select.smt2
(declare-datatype
  pair (par (a b) ((pair2 (proj1-pair a) (proj2-pair b)))))
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  select
  (par (a)
    (((x a) (y (list (pair a (list a))))) (list (pair a (list a)))))
  (match y
    ((nil (_ nil (pair a (list a))))
     ((cons z x2)
      (match z
        (((pair2 y2 ys) (cons (pair2 y2 (cons x ys)) (select x x2)))))))))
(define-fun-rec
  select2
  (par (a) (((x (list a))) (list (pair a (list a)))))
  (match x
    ((nil (_ nil (pair a (list a))))
     ((cons y xs) (cons (pair2 y xs) (select y (select2 xs)))))))
(define-fun-rec
  map
  (par (a b) (((f (=> a b)) (x (list a))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons y xs) (cons (@ f y) (map f xs))))))
(prove
  (par (b)
    (forall ((xs (list b)))
      (=
        (map (lambda ((x (pair b (list b)))) (match x (((pair2 y z) y))))
          (select2 xs))
        xs))))
```

Naive implementation:

```rust
#[ravencheck::check_module]
#[allow(dead_code)]
mod p22 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[derive(PartialEq, Clone)]
  enum Pair<F, S> {
    Pair2(F, S)
  }

  #[define]
  #[recursive]
  fn select<T: PartialEq + Clone>(x: T, y: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match y {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(z, x2) =>
        match z {
          Pair::<T, LinkedList<T>>::Pair2(y2, ys) =>
            LinkedList::<Pair<T, LinkedList<T>>>::Cons(
              Pair::<T, LinkedList<T>>::Pair2(
                y2,
                LinkedList::<T>::Cons(x.clone(), Box::new(ys))
              ),
              Box::new(select::<T>(x, *x2))
            )
        }
    }
  }

  #[define]
  #[recursive]
  fn select2<T: PartialEq + Clone>(x: LinkedList<T>) -> LinkedList<Pair<T, LinkedList<T>>> {
    match x {
      LinkedList::<T>::Nil =>
        LinkedList::<Pair<T, LinkedList<T>>>::Nil,
      LinkedList::<T>::Cons(y, xs) =>
        LinkedList::<Pair<T, LinkedList<T>>>::Cons(
          Pair::<T, LinkedList<T>>::Pair2(y.clone(), *xs.clone()),
          Box::new(select::<T>(y, select2::<T>(*xs)))
        )
    }
  }

  #[define]
  #[recursive]
  fn map<T: PartialEq + Clone>(f: fn(Pair<T, LinkedList<T>>) -> T, x: LinkedList<Pair<T, LinkedList<T>>>) -> LinkedList<T> {
    match x {
      LinkedList::<Pair<T, LinkedList<T>>>::Nil => LinkedList::<T>::Nil,
      LinkedList::<Pair<T, LinkedList<T>>>::Cons(y, xs) => LinkedList::<T>::Cons(f(y), Box::new(map::<T>(f, *xs)))
    }
  }

  #[annotate]
  #[for_type(LinkedList<T> => <T>)]
  #[inductive(xs: LinkedList<T>)]
  fn p22<T>() -> bool {
    map::<T>(
      |x: Pair::<T, LinkedList<T>>| {
        match x {
          Pair::<T, LinkedList<T>>::Pair2(y, z) => y
        }
      },
      select2::<T>(xs)
    ) == xs
  }
}
```

## P44

SMT2:

```txt
; ./problems/list_return_2.smt2
; List monad laws
(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun
  return
  (par (a) (((x a)) (list a))) (cons x (_ nil a)))
(define-fun-rec
  ++
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  >>=
  (par (a b) (((x (list a)) (y (=> a (list b)))) (list b)))
  (match x
    ((nil (_ nil b))
     ((cons z xs) (++ (@ y z) (>>= xs y))))))
(prove
  (par (a)
    (forall ((xs (list a)))
      (= (>>= xs (lambda ((x a)) (return x))) xs))))
```

Naive implementation:

```rust
#[ravencheck::check_module]
#[allow(dead_code)]
mod p44 {
  #[define]
  #[derive(PartialEq, Clone)]
  pub enum LinkedList<T> {
    Nil,
    Cons(T, Box<LinkedList<T>>),
  }

  #[define]
  #[recursive]
  pub fn append<A>(x: LinkedList<A>, y: LinkedList<A>) -> LinkedList<A> {
    match x {
      LinkedList::<A>::Nil => y,
      LinkedList::<A>::Cons(z, xs) => LinkedList::<A>::Cons(z, Box::new(append::<A>(*xs, y)))
    }
  }

  // Note: Due to typing issues w/ ravencheck, I had to replace
  // the generic B with its only instantiation here.
  #[define]
  #[recursive]
  fn map_concat<A: PartialEq>(x: LinkedList<A>,
      y: fn(A) -> LinkedList<A>) -> LinkedList<A> {
    match x {
      LinkedList::<A>::Nil => LinkedList::<A>::Nil,
      LinkedList::<A>::Cons(z, xs) => append::<A>(
        y(z),
        map_concat::<A>(*xs, y)
      )
    }
  }

  #[define]
  fn return_fn<A>(x: A) -> LinkedList<A> {
    LinkedList::<A>::Cons(x, Box::new(LinkedList::<A>::Nil))
  }

  #[annotate]
  #[for_type(LinkedList<A> => <A>)]
  #[inductive(xs: LinkedList<A>)]
  fn p44<A>() -> bool {
    map_concat::<A>(
      xs,
      |x: A| {
        return_fn::<A>(x)
      }
    ) == xs
  }
}
```
