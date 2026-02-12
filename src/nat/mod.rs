
/// A module exposing the natural numbers
#[ravencheck::export_module]
#[allow(dead_code)]
pub mod nat {
  #[define]
  pub enum Nat {
    Z,
    S(Box<Nat>)
  }

  #[define]
  #[recursive]
  #[total]
  fn is_even(n: Nat) -> bool {
    match n {
      Nat::Z => true,
      Nat::S(m) => !is_even(*m)
    }
  }

  #[annotate]
  fn zero_is_even() -> bool {
    is_even(Nat::Z)
  }

  #[annotate]
  fn one_is_odd() -> bool {
    !is_even(Nat::S(Nat::Z))
  }

  #[annotate]
  #[inductive(n: Nat)]
  fn odd_follows_even() -> bool {
    is_even(n) == !is_even(Nat::S(n))
  }

  #[annotate]
  #[inductive(n: Nat)]
  fn even_follows_odd() -> bool {
    !is_even(n) == is_even(Nat::S(n))
  }

  #[annotate]
  #[inductive(n: Nat)]
  fn even_odd_toggle_2_step() -> bool {
    is_even(n) == is_even(Nat::S(Nat::S(n)))
  }
}
