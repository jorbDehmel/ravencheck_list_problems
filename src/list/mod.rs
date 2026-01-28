/// A module exposing an axiomitized generic linked list
#[ravencheck::export_module]
#[allow(dead_code)]
pub mod linked_list {
  // Make an UNINTERPRETED datatype
  #[declare]
  pub type T = u32;

  /// A generic linked list
  #[define]
  #[derive(PartialEq)]
  pub enum LinkedList {
    /// The end-of-list / empty-list constructor
    Nil,
    /// A non-empty constructor which points to memory on the
    /// heap
    Cons(T, Box<LinkedList>),
  }

  #[define]
  #[recursive]
  fn interleave(x: LinkedList, y: LinkedList) -> LinkedList {
    match x {
      LinkedList::Nil => y,
      LinkedList::Cons(z, xs) =>
        LinkedList::Cons(z, Box::new(interleave(y, *xs)))
    }
  }

  #[define]
  #[recursive]
  fn append(x: LinkedList, y: LinkedList) -> LinkedList {
    match x {
      LinkedList::Nil => y,
      LinkedList::Cons(z, xs) => LinkedList::Cons(z, Box::new(append(*xs, y)))
    }
  }

  #[declare]
  pub const UNDEFINED: T = 0;

  #[define]
  #[recursive]
  fn elem(x: T, y: LinkedList) -> bool {
    match y {
      LinkedList::Nil => false,
      LinkedList::Cons(z, xs) => z == x || elem(x, *xs)
    }
  }
}
