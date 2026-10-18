///|
/// @file core_test.mbt
/// # HoTT 核心的黑盒測試：Path 運算 / h-層次 / 截斷
///
/// 對應 package `axiom/axiom/hott_core`。`ua` 的定律測試在 `univalence/univalence_test.mbt`。

test "hott: path ops" {
  let p = @hott_core.refl(42)
  let q = @hott_core.sym(p)
  let r = @hott_core.trans(p, q)
  assert_eq(p.code, 0)
  assert_eq(r.code, 1)
  let f = fn(x : Int) -> Int { x + 1 }
  let ap_p = @hott_core.ap(f, p)
  assert_eq(ap_p.code, 0)
}

test "hott: hlevel" {
  let l = @hott_core.hlevel_up(@hott_core.SetLevel)
  assert_eq(l, @hott_core.GroupoidLevel)
  let c = @hott_core.trunc_make(42, @hott_core.SetLevel)
  assert_eq(@hott_core.is_truncated(c, @hott_core.SetLevel), true)
}
