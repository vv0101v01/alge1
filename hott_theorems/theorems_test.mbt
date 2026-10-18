///|
/// @file theorems_test.mbt
/// # 新定理 N1-N6 的黑盒測試
///
/// 對應 package `axiom/axiom/hott_theorems`。

test "hott: new theorems pi1" {
  assert_eq(@hott_theorems.pi1_s1_is_int(), true)
  assert_eq(@hott_theorems.synthetic_pi(1, 1), "ℤ")
  assert_eq(@hott_theorems.blakers_massey_connectivity(2, 3), 5)
  assert_eq(@hott_theorems.whitehead_principle(true), true)
}

///|
test "N1 Encode-Decode：Ω(S¹) ≅ ℤ 的兩個方向互逆" {
  let my_loop = @hott_hits.circle_loop()
  assert_eq(@hott_theorems.encode_s1(my_loop), 1)
  assert_eq(@hott_theorems.decode_s1(5).code, 5)
  assert_eq(@hott_theorems.decode_s1(0).code, 0)
  // encode ∘ decode = id（在 code 層面）
  for n in -3..=3 {
    assert_eq(@hott_theorems.encode_s1(@hott_theorems.decode_s1(n)), n)
  }
}
