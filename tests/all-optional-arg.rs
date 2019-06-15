use duang::duang;

duang!(
pub fn foo(a: i32 = 1, b:i32 = a) -> (i32,i32)
{
  (a,b)
}
);

fn main() {
  assert_eq!(foo!(), (1,1));
}
