
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
  fn is_even(n: Nat) -> bool {
    match n {
      Nat::Z => true,
      Nat::S(m) => !is_even(*m)
    }
  }
}
