use duang::duang;
use std::iter::IntoIterator;

duang!(
pub fn foo(a: impl Default+IntoIterator<Item=i32> = Default::default()) -> i32
{
  a.into_iter().sum()
}
);

fn main() {
  assert_eq!(foo!(vec![1, 2, 3, 4, 5]), 15);
  assert_eq!(foo!(Some(15)), 15);
  assert_eq!(foo!(a: Option<i32>), 0);
}
