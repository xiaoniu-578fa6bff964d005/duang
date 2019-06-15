#[test]
fn tests() {
  let t = trybuild::TestCases::new();
  t.pass("tests/parse.rs");
  t.pass("tests/call.rs");
  t.pass("tests/right.rs");
  t.compile_fail("tests/error-not-captured-parameter-self.rs");
  t.compile_fail("tests/error-call-parameter-order.rs");
  t.compile_fail("tests/error-call-repeat-assign.rs");
  t.compile_fail("tests/error-call-missing-assign.rs");
  t.pass("tests/all-optional-arg.rs");
  t.pass("tests/support-impl-arg.rs");
  t.pass("tests/type-notation.rs");
  t.pass("tests/old-function-remain-intact.rs");
  t.compile_fail("tests/error-only-type-provided-for-mandatory.rs");
  t.pass("tests/default-hygiene.rs");
  t.compile_fail("tests/error-default-hygiene.rs");
  t.pass("tests/pattern-argument.rs");
  t.compile_fail("tests/error-wildchar.rs");
}
