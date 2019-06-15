use demo_duang::foo;

fn main() {
  // pass
  assert_eq!(foo!(1, c = 30, b = -2.0), (1, -2.0, 30));
  // pass
  assert_eq!(foo!(a = 10), (10, 13.0, 100));
  // fail
  // foo!(1,c=30,c=2);
}
