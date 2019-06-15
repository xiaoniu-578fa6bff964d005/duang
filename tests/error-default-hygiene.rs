#![allow(non_snake_case)]
#![allow(unused_variables)]
mod bar {
  use duang::duang;

  pub static NUM: i32 = 42;

  duang!(
  pub fn foo(a: i32 = NUM) -> i32
  {
    a
  }
  );
}

fn main() {
  use bar::foo;
  foo!();
}
