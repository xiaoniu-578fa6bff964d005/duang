// this test check duang exist
use duang::duang;

duang!(
pub fn foo<T>(a: T,b: f64 = 13.0, c: T = a*a)
where
  T: std::ops::Mul<T, Output = T>,
  T: std::fmt::Display,
  T: Copy,
{
  println!("{}", a);
  println!("{}", b);
  println!("{}", c);
}
);

fn main() {
}
