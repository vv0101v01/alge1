///|
/// @file hits_test.mbt
/// # 高歸納類型的黑盒測試：Circle 的 base/loop 與遞推
///
/// 對應 package `axiom/axiom/hott_hits`。encode/decode（Encode-Decode 定理）在 `hott_theorems/theorems_test.mbt`。

test "hott: hits circle" {
  let base = @hott_hits.Circle::base()
  let my_loop = @hott_hits.circle_loop()
  assert_eq(my_loop.code, 1)
  let s1_rec = @hott_hits.circle_rec(0, @hott_core.refl(0))
  assert_eq(s1_rec(base), 0)
}
