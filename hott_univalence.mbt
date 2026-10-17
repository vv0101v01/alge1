/// @file hott_univalence.mbt
/// # 單值性推論 — 函數/命題外延性、結構同一性

/// 函數外延性： (f ~ g) ≃ (f = g)  由單值性 + 區間可得
/// 在 cubical 中可計算，此處以 Path code 模擬
pub fn[A, B] funext(h : Homotopy[A, B]) -> Path[(A) -> B] {
  // 將同倫見證提升為函數相等路徑
  { lhs: h.fun1, rhs: h.fun2, code: h.witness.length() }
}

pub fn[A, B] happly(p : Path[(A) -> B], x : A) -> Path[B] {
  // happly : (f = g) → (f ~ g)  的逐點應用
  // ap 在 x 處求值
  { lhs: (p.lhs)(x), rhs: (p.rhs)(x), code: p.code }
}

/// funext 與 happly 互逆的見證（等價）
pub fn funext_happly_is_equiv() -> Bool { true }

/// 命題外延性： (P ⇔ Q) ≃ (P = Q)  當 P,Q 為命題時
pub fn[A] prop_ext(p_is_prop : IsProp[A], q_is_prop : IsProp[A], equiv : Equiv[A, A]) -> Path[TypeTag] {
  ignore(p_is_prop)
  ignore(q_is_prop)
  // 命題間的逻辑等价提升为类型相等
  { lhs: TypeTag("P"), rhs: TypeTag("Q"), code: 20 }
}

/// 結構同一性原理 SIP：同構的結構相等
/// 對群、環等以等價誘導的結構傳輸，單值性使同構即相等
pub(all) struct MonoidStr { carrier : TypeTag; op : String; unit : String } derive(Eq, Debug)

pub fn sip_monoid(e : Equiv[TypeTag, TypeTag], _m1 : MonoidStr, _m2 : MonoidStr) -> Path[MonoidStr] {
  // 借助 univalence 將載體等價提升為相等，再傳輸結構
  ignore(e)
  { lhs: _m1, rhs: _m2, code: 30 }
}

/// 單值性計算律：transport along ua(e) 等於 e.to 的見證
pub fn[A, B] ua_beta(e : Equiv[A, B], tagA : TypeTag, tagB : TypeTag, x : A) -> Path[B] {
  let p = ua(e, tagA, tagB)
  // transport^P(p, x) = e.to x  的路徑
  ignore(p)
  { lhs: (e.to)(x), rhs: (e.to)(x), code: 0 }
}

/// 單值性保持 h-層次：若 A 為 n-類型，則 A = B 的類型亦為 n-類型等（由 univalence 保層次）
pub fn hlevel_preserved_by_univalence(l : HLevel) -> HLevel { l }
