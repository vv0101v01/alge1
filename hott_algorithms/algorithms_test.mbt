///|
/// @file algorithms_test.mbt
/// # 新算法 H1-H7 的黑盒測試（含 H1/H7 誠實化後的行為）
///
/// 對應 package `axiom/axiom/hott_algorithms`。真正的 Kan 填充與 cubical NBE 測試在
/// `cubical/cubical_test.mbt`。

test "hott: algorithms" {
  let p = @hott_core.refl(@hott_core.TypeTag("X"))
  assert_eq(@hott_algorithms.cubical_transport(p, 99), 99)
  assert_eq(@hott_algorithms.truncated_exists_search([1, 2, 3], fn(x) { x == 2 }), true)
  let t1 = @hott_algorithms.Term::{ code: 1001, tag: "t" }
  let t2 = @hott_algorithms.Term::{ code: 1, tag: "t" }
  // 誠實化後：`Term` 無內部結構 ⇒ `normalize` 為恒等，1001 與 1 不再被誤判為相等
  // （舊版 `code % 1000` 會回傳 true；真正的 NBE 見 cubical_test.mbt 的 K3）
  assert_eq(@hott_algorithms.judgmental_eq(t1, t2), false)
  assert_eq(@hott_algorithms.judgmental_eq(t1, t1), true)
  assert_eq(@hott_algorithms.normalize(t1), t1)
  // H1 的真正版本：Kan 填充把 1 沿 3-循環的 glue 送到 2
  assert_eq(@hott_algorithms.cubical_kan_demo(), "2")
}
