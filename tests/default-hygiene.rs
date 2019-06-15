#![allow(non_snake_case)]
#![allow(unused_variables)]
mod bar {
  use duang::duang;

  pub static NUM: i32 = 42;

  duang!(
  pub fn foo(a: i32 = $crate::bar::NUM) -> i32
  {
    a
  }
  );
}

fn main() {
  use bar::foo;
  assert_eq!(foo!(1), 1);
  assert_eq!(foo!(), 42);
  let NUM = 43;
  assert_eq!(foo!(), 42);
}
