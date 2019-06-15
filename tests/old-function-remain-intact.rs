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
  assert_eq!(foo(10, -2.0, 10 * 10), (10, -2.0, 100));
}
