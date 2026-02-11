
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

  // Sanity checks
  // #[annotate]
  // fn a() -> bool {
  //   is_even(Nat::Z)
  // }

  // #[annotate]
  // fn b() -> bool {
  //   !is_even(Nat::S(Nat::Z))
  // }

  // #[annotate]
  // fn c() -> bool {
  //   is_even(Nat::S(Nat::S(Nat::Z)))
  // }

  // #[annotate]
  // fn d(x: Nat, y: Nat) -> bool {
  //   implies(
  //     Nat::S(x) == Nat::S(y), x == y
  //   ) && implies(
  //     x == y, Nat::S(x) == Nat::S(y)
  //   )
  // }
}
