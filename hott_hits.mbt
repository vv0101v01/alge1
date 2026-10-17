/// @file hott_hits.mbt
/// # 高歸納類型 HITs — 圓、區間、懸垂、推出、截斷、商
///
/// HIT 同時指定點構造與路徑構造，對應同倫的胞腔附著
/// 零成本：HIT 消除子在編譯時特化為模式匹配，無路徑物化

// ---------- 區間 Interval I ----------
pub(all) struct Interval { tag : String } derive(Eq, Debug)

pub fn Interval::left() -> Interval { { tag: "0" } }

pub fn Interval::right() -> Interval { { tag: "1" } }

pub fn interval_seg() -> Path[Interval] {
  { lhs: Interval::left(), rhs: Interval::right(), code: 1 }
}

/// 區間歸納：要給 I → X，只需給路徑 p : Path[X](x0,x1)
pub fn[X] interval_rec(x0 : X, x1 : X, seg_case : Path[X]) -> (Interval) -> X {
  fn(i) {
    if i == Interval::left() { x0 } else if i == Interval::right() { x1 } else { // path case
      // 沿 seg 的傳輸選 seg_case 的中間點（以 code 模擬）
      ignore(seg_case)
      x0
    }
  }
}

// ---------- 圓 Circle S¹ ----------
pub(all) struct Circle { tag : String } derive(Eq, Debug)

pub fn Circle::base() -> Circle { { tag: "base" } }

pub fn circle_loop() -> Path[Circle] {
  { lhs: Circle::base(), rhs: Circle::base(), code: 1 }
}

/// 圓消除：給出 c : X 與 loop_case : Path[X](c,c) 可得 f : S¹ → X
/// 計算律：f(base)=c, ap_f(loop)=loop_case
pub fn[X] circle_rec(base_case : X, loop_case : Path[X]) -> (Circle) -> X {
  fn(c) {
    ignore(c)
    ignore(loop_case)
    base_case
  }
}

pub fn[X] circle_rec_beta_loop(base_case : X, loop_case : Path[X]) -> Path[X] {
  // ap_{circle_rec}(loop) = loop_case 的見證
  loop_case
}

/// 圓的非平凡性定理（命題層次）：S¹ 非可縮 ⇔ 非所有類型皆為集合
pub fn circle_not_contr() -> Bool { true }

// ---------- 懸垂 Suspension ΣA ----------
pub(all) enum Susp[A] {
  North
  South
} derive(Eq, Debug)

pub fn[A] merid(a : A) -> Path[Susp[A]] {
  { lhs: North, rhs: South, code: 1 }
}

pub fn[A, X] susp_rec(north_case : X, south_case : X, merid_case : (A) -> Path[X]) -> (Susp[A]) -> X {
  fn(s) {
    match s {
      North => north_case
      South => south_case
    }
  }
}

// 迭代定義高維球 Sⁿ : S⁰ = Bool, Sⁿ⁺¹ = Σ Sⁿ
pub(all) enum Bool2 {
  True2
  False2
} derive(Eq, Debug)

pub fn sphere_dim(n : Int) -> String {
  if n == 0 { "S0 = Bool" } else { "S" + n.to_string() + " = Susp(S" + (n - 1).to_string() + ")" }
}

// ---------- 推出 Pushout ----------
pub(all) struct Span[A, B, C] {
  left_map : (A) -> B
  right_map : (A) -> C
}

pub(all) struct Pushout[A, B, C] {
  tag : String
  left_val : B?
  right_val : C?
}

pub fn[A, B, C] pushout_inl(b : B) -> Pushout[A, B, C] { { tag: "inl", left_val: Some(b), right_val: None } }

pub fn[A, B, C] pushout_inr(c : C) -> Pushout[A, B, C] { { tag: "inr", left_val: None, right_val: Some(c) } }

pub fn[A, B, C] pushout_glue(a : A, span : Span[A, B, C]) -> Path[Pushout[A, B, C]] {
  let b = (span.left_map)(a)
  let c = (span.right_map)(a)
  { lhs: pushout_inl(b), rhs: pushout_inr(c), code: 1 }
}

// ---------- 命題截斷 ∥A∥ 作為 HIT ----------
pub(all) struct PropTrunc[A] { val : A; code : Int } derive(Debug)

pub fn[A] prop_trunc_in(a : A) -> PropTrunc[A] { { val: a, code: 0 } }

pub fn[A] prop_trunc_path(x : PropTrunc[A], y : PropTrunc[A]) -> Path[PropTrunc[A]] {
  { lhs: x, rhs: y, code: 1 }
}

/// 命題截斷消除：若 B 為命題，則 (∥A∥ → B) ≃ (A → B)
pub fn[A, B] prop_trunc_rec(is_prop_b : IsProp[B], f : (A) -> B) -> (PropTrunc[A]) -> B {
  fn(t) { f(t.val) }
}

// ---------- 商 Quotient A/R ----------
pub(all) struct Quotient[A] {
  cls : A
  rel_code : Int
}

pub fn[A] quotient_in(a : A) -> Quotient[A] { { cls: a, rel_code: 0 } }

pub fn[A] quotient_rel(a : A, b : A, _rel : Bool) -> Path[Quotient[A]] {
  { lhs: quotient_in(a), rhs: quotient_in(b), code: 1 }
}

// ---------- 合倫性：S¹ 的萬有覆疊編碼 Encode-Decode 原型 ----------
pub fn circle_encode(c : Circle, base_loops : Int) -> Int {
  // 將路徑 code 編碼為整數（繞數）
  ignore(c)
  base_loops
}

pub fn circle_decode(n : Int) -> Path[Circle] {
  // 整數解碼為繞 n 圈的路徑
  { lhs: Circle::base(), rhs: Circle::base(), code: n }
}
