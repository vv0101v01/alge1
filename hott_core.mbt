/// @file hott_core.mbt
/// # HoTT 核心 — 路徑、傳輸、同倫、等價、單值性、h-層次、截斷
///
/// 基礎：類型即空間，相等即路徑，`Path[A](x,y)` 為從 x 到 y 的路徑類型
/// 零成本：所有路徑運算在編譯時單態化為整數 code 的加法/取反，運行時 O(1) 哈希

// ---------- 路徑類型 ----------
pub(all) struct Path[A] {
  lhs : A
  rhs : A
  code : Int // 路徑的組合編碼：0=refl, +n/-n 為合成深度
} derive(Debug)

pub fn[A] refl(a : A) -> Path[A] { { lhs: a, rhs: a, code: 0 } }

pub fn[A] sym(p : Path[A]) -> Path[A] { { lhs: p.rhs, rhs: p.lhs, code: 0 - p.code } }

pub fn[A] trans(p : Path[A], q : Path[A]) -> Path[A] {
  // 需 p.rhs == q.lhs 的前提，運行時不檢查（類型層面保證）
  { lhs: p.lhs, rhs: q.rhs, code: p.code + q.code + 1 }
}

/// ap : 路徑在函數下的像  ap_f : Path[A](x,y) → Path[B](f x, f y)
pub fn[A, B] ap(f : (A) -> B, p : Path[A]) -> Path[B] {
  { lhs: f(p.lhs), rhs: f(p.rhs), code: p.code }
}

/// transport : 沿類型族 P : A → Type 的傳輸  P x → P y
/// 以函數參數 `family : (A) -> Int` 模擬類型族的 code 變化（示例）
pub fn[A] transport(p : Path[A], family_code : (A) -> Int, val_code : Int) -> Int {
  // 真實 HoTT 中 transport^P(p, u) : P y；此處以 code 運算模擬：val_code + p.code
  val_code + p.code
}

/// 同倫：兩函數逐點相等  f ~ g ≔ Π(x:A) Path[B](f x, g x)
pub(all) struct Homotopy[A, B] {
  fun1 : (A) -> B
  fun2 : (A) -> B
  witness : Array[(A, Path[B])] // 對採樣點的路徑見證
}

pub fn[A, B] homotopy_refl(f : (A) -> B) -> Homotopy[A, B] {
  { fun1: f, fun2: f, witness: [] }
}

// ---------- 等價 ----------
/// 半伴隨等價：f : A→B 為等價 ⇔ ∃ g, η: g∘f ~ id, ε: f∘g ~ id 且相干
pub(all) struct Equiv[A, B] {
  to : (A) -> B
  from : (B) -> A
  // 左逆與右逆的同倫見證（以採樣數組模擬）
  left_inv_code : Int
  right_inv_code : Int
}

pub fn[A, B] Equiv::make(to : (A) -> B, from : (B) -> A) -> Equiv[A, B] {
  { to, from, left_inv_code: 0, right_inv_code: 0 }
}

pub fn[A, B] Equiv::is_equiv(self : Equiv[A, B]) -> Bool {
  // 簡化檢查：兩方向 code 為 0 視為等價（真實需同倫見證）
  self.left_inv_code == 0 && self.right_inv_code == 0
}

/// idToEquiv : Path[TypeTag](A,B) → Equiv[A,B]  （典範映射）
/// 單值性斷言其為等價： (A =_U B) ≃ (A ≃ B)

pub(all) struct TypeTag(String) derive(Eq, Debug)

pub fn[A, B] id_to_equiv(p : Path[TypeTag], to : (A) -> B, from : (B) -> A) -> Equiv[A, B] {
  // 沿類型相等路徑的傳輸誘導等價；code 保持
  ignore(p)
  Equiv::make(to, from)
}

/// 單值性見證：將等價提升為類型相等（HoTT 公理的計算內容）
/// `ua : Equiv[A,B] → Path[TypeTag](A,B)`  在 cubical 中可計算，此處以 code 模擬
pub fn[A, B] ua(e : Equiv[A, B], tagA : TypeTag, tagB : TypeTag) -> Path[TypeTag] {
  // cubical 實現中 ua 具有計算內容：transport along ua(e) = e.to
  { lhs: tagA, rhs: tagB, code: e.left_inv_code + e.right_inv_code + 10 }
}

/// 單值性等價：(A = B) ≃ (A ≃ B)  的見證（雙向）
pub(all) struct UnivalenceWitness[A, B] {
  to_equiv : (Path[TypeTag]) -> Equiv[A, B]
  to_path : (Equiv[A, B]) -> Path[TypeTag]
}

pub fn[A, B] univalence_witness(
  tagA : TypeTag,
  tagB : TypeTag,
  to : (A) -> B,
  from : (B) -> A
) -> UnivalenceWitness[A, B] {
  {
    to_equiv: fn(p) { id_to_equiv(p, to, from) },
    to_path: fn(e : Equiv[A, B]) -> Path[TypeTag] { ua(e, tagA, tagB) },
  }
}

// ---------- h-層次 ----------
pub(all) enum HLevel {
  Contr // -2, 單點可縮
  Prop // -1, 命題（任意兩元相等）
  SetLevel // 0, 集合（相等為命題）
  GroupoidLevel // 1, 群胚
  TwoGroupoidLevel // 2
  NType(Int) // n ≥3
} derive(Eq, Debug)

pub fn hlevel_up(l : HLevel) -> HLevel {
  match l {
    Contr => Prop
    Prop => SetLevel
    SetLevel => GroupoidLevel
    GroupoidLevel => TwoGroupoidLevel
    TwoGroupoidLevel => NType(3)
    NType(n) => NType(n + 1)
  }
}

/// isContr(A) ≔ Σ(c:A) Π(x:A) Path[A](c,x)
pub(all) struct IsContr[A] {
  center : A
  // 中心到任意點的路徑族（以函數模擬）
  path_to : (A) -> Path[A]
}

/// isProp(A) ≔ Π(x,y:A) Path[A](x,y)  —  所有路徑唯一
pub(all) struct IsProp[A] { witness : (A, A) -> Path[A] }

/// isSet(A) ≔ Π(x,y:A) isProp(Path[A](x,y))
pub fn[A] is_set_from_prop(_prop_paths : IsProp[Path[A]]) -> Bool { true }

// ---------- 截斷 ----------
/// n-截斷 ∥A∥ₙ  左伴隨於 n-類型包含
pub(all) struct Trunc[A] {
  level : HLevel
  val : A
  trunc_code : Int
}

pub fn[A] trunc_make(a : A, level : HLevel) -> Trunc[A] { { level, val: a, trunc_code: level_to_int(level) } }

fn level_to_int(l : HLevel) -> Int {
  match l {
    Contr => -2
    Prop => -1
    SetLevel => 0
    GroupoidLevel => 1
    TwoGroupoidLevel => 2
    NType(n) => n
  }
}

pub fn[A] is_truncated(t : Trunc[A], level : HLevel) -> Bool { t.level == level }

/// 命題截斷 ∥A∥₋₁  滿足：∥A∥ 為命題且 A → ∥A∥ 普遍
pub fn[A] prop_trunc(a : A) -> Trunc[A] { trunc_make(a, Prop) }

/// 集合截斷 ∥A∥₀
pub fn[A] set_trunc(a : A) -> Trunc[A] { trunc_make(a, SetLevel) }

/// 截斷消除：若 B 為 n-類型，則 (∥A∥ₙ → B) ≃ (A → B)  （普遍性）
pub fn[A, B] trunc_rec(level : HLevel, f : (A) -> B) -> (Trunc[A]) -> B {
  fn(t) {
    ignore(level)
    f(t.val)
  }
}
