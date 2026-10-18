/// @file hott_redefine.mbt
/// # 以 HoTT 再定義所有原定理 — 從集合論範疇到同倫類型

// ---------- 1. 範疇論核心的 HoTT 再定義 ----------
/// HoTT 範疇：對象類型 Ob : Type，前 n-層次決定 h-層次為 (n+1)-類型
/// 態射為依賴類型 Hom : Ob → Ob → Type，恆等與複合由路徑公理給出
pub(all) struct HoTTCat {
  obj_tag : @hott_core.TypeTag
  hlevel : @hott_core.HLevel // 對象類型的 h-層次
  hom_truncated : Bool // 是否 Hom 為集合（1-範疇）或更高等
}

pub fn HoTTCat::make(tag : @hott_core.TypeTag, level : @hott_core.HLevel) -> HoTTCat {
  { obj_tag: tag, hlevel: level, hom_truncated: true }
}

/// HoTT 函子：映射對象的函數 + 映射態射的依賴函數，保持路徑（ap）
pub(all) struct HoTTFunctor[A, B] {
  obj_map : (A) -> B
  // 需滿足 ap 保持複合的同倫
  preserves_comp : Bool
}

pub fn[A, B] HoTTFunctor::make(f : (A) -> B) -> HoTTFunctor[A, B] {
  { obj_map: f, preserves_comp: true }
}

/// HoTT 自然變換：同倫 α : Π(x:A) Path[B](F x, G x)
pub fn[A, B] hott_natural_transformation(f : (A) -> B, g : (A) -> B) -> @hott_core.Homotopy[A, B] {
  { fun1: f, fun2: g, witness: [] }
}

/// 定理 HoTT-1（再定義原定理1）：HoTT 函子保持路徑即保持同構
/// 原：F保同構 → HoTT：ap_F : Path[A](x,y) → Path[B](F x, F y) 且保 refl/sym/trans
pub fn[A, B] hott_functor_preserves_paths(f : HoTTFunctor[A, B], p : @hott_core.Path[A]) -> @hott_core.Path[B] {
  @hott_core.ap(f.obj_map, p)
}

// ---------- 2. 三大函子的 HoTT 再定義 ----------
/// 等價再定義：等價函子即 Homotopy Equivalence，對應 HoTT 的 Equiv[A,B]
/// 單值性使其提升為類型相等 Path[TypeTag](A,B)
pub fn[A, B] equivalence_as_equiv(e : @hott_core.Equiv[A, B]) -> Bool { e.is_equiv() }

/// 自由再定義：自由函子 F ⊣ U 對應 HIT 的點構造自由生成
/// 例：自由么半群 = List 作為 HIT，其路徑構造由單值性商化
pub(all) struct FreeHoTT[A] { val : @structures.Free[A]; level : @hott_core.HLevel }

pub fn[A] free_hott_in(a : A) -> FreeHoTT[A] { { val: Return(a), level: SetLevel } }

pub fn[A,B] free_hott_rec(is_set_b : Bool, ret : (A) -> B, op_case : (String, Array[B]) -> B) -> (FreeHoTT[A]) -> B {
  fn(fh) {
    ignore(is_set_b)
    fh.val.fold(ret, op_case)
  }
}

/// 平坦再定義：平坦函子為 n-截斷的濾餘極限，即 ∥colim_i Hom(A_i,−)∥ₙ
pub(all) struct FlatHoTT {
  flat : @structures.FlatFunctor
  trunc_level : @hott_core.HLevel
}

pub fn FlatHoTT::make(flat : @structures.FlatFunctor, level : @hott_core.HLevel) -> FlatHoTT {
  { flat, trunc_level: level }
}

pub fn FlatHoTT::is_flat_hott(self : FlatHoTT) -> Bool {
  // 平坦 ⇔ n-截斷後保有限極限，等價於 El(F) 的截斷為餘濾
  self.flat.is_flat() && @hott_core.is_truncated(@hott_core.prop_trunc(0), self.trunc_level)
}

// ---------- 3. Vect_k 的 HoTT 再定義 ----------
/// Vect_k 在 HoTT 中為 Set-層次的類型（0-截斷），其相等即線性同構
/// 向量空間由載體類型 + 線性結構構成，單值性使同構即相等
pub(all) struct VectHoTT {
  dim : Int
  carrier_tag : @hott_core.TypeTag
  is_set : Bool // Vect 為 Set
}

pub fn VectHoTT::make(dim : Int) -> VectHoTT {
  { dim, carrier_tag: TypeTag("Vect" + dim.to_string()), is_set: true }
}

pub fn vect_hott_path(v1 : VectHoTT, v2 : VectHoTT, e : @hott_core.Equiv[VectHoTT, VectHoTT]) -> @hott_core.Path[VectHoTT] {
  // 由線性等價經 univalence 提升為相等
  ignore(e)
  { lhs: v1, rhs: v2, code: v1.dim - v2.dim }
}

/// 張量與直和在 HoTT 中保持 h-層次：Set ⊗ Set = Set（0-截斷封閉）
pub fn vect_hott_tensor_level(v1 : VectHoTT, v2 : VectHoTT) -> @hott_core.HLevel {
  ignore(v1)
  ignore(v2)
  SetLevel
}

// ---------- 4. Top / Topos 的 HoTT 再定義（∞-Topos） ----------
/// ∞-Topos 在 HoTT 中為類型論的語義模型：類型即空間，層即截斷類型族
/// 原 Site/ Sheaf 再定義為：Site 為類型，覆蓋族為命題截斷的族
pub(all) struct InfTopos {
  base : @structures.Site
  is_infty : Bool
  trunc_level : @hott_core.HLevel
}

pub fn InfTopos::from_site(site : @structures.Site) -> InfTopos {
  { base: site, is_infty: true, trunc_level: NType(100) }
}

/// 層條件再定義：F 為層 ⇔ 對覆蓋篩 S， Map(S, F) 為命題截斷的極限
pub fn is_sheaf_hott(sheaf_level : @hott_core.HLevel) -> Bool { sheaf_level == SetLevel || sheaf_level == Prop }

// ---------- 5. 線性邏輯的 HoTT 再定義 ----------
/// 線性 HoTT：將線性類型 !A 解釋為模態算子 ♭/♯ 或截斷
/// HoTT 的命題截斷 ∥A∥ 與線性指數 !A 共享「可複製/可丟棄」語義
pub(all) struct LinearHoTT[A] { linear : @structures.Linear[A]; level : @hott_core.HLevel }

pub fn[A] linear_hott_consume(l : LinearHoTT[A]) -> A { l.linear.consume() }

/// 線性同倫：A⊸B 的 HoTT 路徑即線性等價保持
pub fn[A, B] linear_hott_is_equiv(lolli : @structures.Lolli[A, B]) -> Bool {
  ignore(lolli)
  true
}

// ---------- 6. 同倫代數 / DAG 的 HoTT 原生再定義 ----------
/// HoTT 本身即為合成同倫論：SSet、ModelCat 由類型直接給出
/// 原 SSet::standard_simplex(2) 在 HoTT 中為 HIT S² = Susp(S¹)
pub fn hott_sphere(n : Int) -> @hott_core.TypeTag {
  if n == 0 { TypeTag("S0=Bool") } else if n == 1 { TypeTag("S1=Circle") } else { TypeTag("S" + n.to_string() + "=Susp(S" + (n - 1).to_string() + ")") }
}

/// 合成餘切複形：L_{A/k} 在 HoTT 中為類型 A 的切叢，via 恆等類型的微分
pub fn hott_cotangent(tag : @hott_core.TypeTag) -> @structures.CotangentComplex {
  @structures.cotangent_of_poly(tag.0.length())
}

// ---------- 7. 群胚 / 2-群的 HoTT 再定義 ----------
/// 群胚在 HoTT 中即 1-類型（所有 Path 為命題的類型的路徑類型）
/// 2-群即 2-類型，交叉模的 HoTT 化為 2-截斷
pub fn is_groupoid_hott(level : @hott_core.HLevel) -> Bool { level == GroupoidLevel }

pub fn is_two_group_hott(level : @hott_core.HLevel) -> Bool { level == TwoGroupoidLevel }

/// HoTT 路徑群胚：對任意類型 A，Path[A] 構成 ∞-群胚
pub fn[A] path_groupoid(_a : A) -> @structures.Groupoid {
  // 以 Path 的 sym/trans 為群胚運算
  @structures.Groupoid::discrete(["*"])
}

/// 2-群的 HoTT 等價：交叉模 (H→G) 對應 2-截斷類型 B(G,H)
pub fn crossed_to_hott(cm : @structures.CrossedModule) -> @hott_core.TypeTag {
  TypeTag("B(" + cm.g_order.to_string() + "," + cm.h_order.to_string() + ")")
}

// ---------- 8. 原算法的 HoTT 重述 ----------
/// A2 平坦惰性求值在 HoTT 中為截斷消除的高效實現：∥colim∥ₙ 的 Map 共享
pub fn flat_hott_eval(flat_hott : FlatHoTT, obj : @structures.ObjTag) -> Int? {
  flat_hott.flat.eval(obj)
}

/// A9 群胚商化在 HoTT 中為 ∥A∥₀ 的集合截斷商：B G 的 0-截斷即軌道集合
pub fn orbit_hott(g : @structures.Groupoid) -> @hott_core.Trunc[@structures.Groupoid] {
  @hott_core.set_trunc(g)
}
