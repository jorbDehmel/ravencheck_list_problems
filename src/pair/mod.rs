/// A module exposing an axiomitized pair
#[ravencheck::export_module]
#[allow(dead_code)]
pub mod pair {
  #[declare]
  type A = u32;

  #[declare]
  type B = u32;

  /// A generic pair
  #[define]
  pub enum Pair {
    Pair2(A, B)
  }
}
