// this test check that macro is usable.
use duang::duang;

duang!(
pub fn foo<T>(a: T,b: f64 = 13.0, c: T = a*a) -> (T,f64,T)
where
  T: std::ops::Mul<T, Output = T>,
  T: std::fmt::Display,
  T: Copy,
{
  (a,b,c)
}
);

fn main() {
  assert_eq!(foo!(1, c = 30, b = -2.0), (1, -2.0, 30));
  assert_eq!(foo!(10), (10, 13.0, 100));
  assert_eq!(foo!(a = 10), (10, 13.0, 100));
}
