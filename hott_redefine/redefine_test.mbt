///|
/// @file redefine_test.mbt
/// # 「用 HoTT 重新定義原有結構」的黑盒測試
///
/// 對應 package `axiom/axiom/hott_redefine`：把 `structures/` 裡的範疇、函子、
/// `Free`、平坦函子、Vectₖ、∞-Topos、線性邏輯、單純集合、群胚、交叉模
/// 逐項加上 h-層次（`@hott_core.HLevel`），讓「集合性 / 群胚性」變成可判定的資料。

///|
test "redefine: 四種結構都帶著正確的 h-層次" {
  let cat = @hott_redefine.HoTTCat::make(@hott_core.TypeTag("Ob"), @hott_core.GroupoidLevel)
  assert_eq(cat.hlevel, @hott_core.GroupoidLevel)
  assert_true(@hott_redefine.is_groupoid_hott(cat.hlevel))

  let v = @hott_redefine.VectHoTT::make(3)
  assert_true(v.is_set)
  assert_eq(v.dim, 3)

  let site = @structures.Site::make([@structures.ObjTag("U"), @structures.ObjTag("V")])
  let t = @hott_redefine.InfTopos::from_site(site)
  assert_true(t.is_infty)
  // Grothendieck 覆蓋的 base 是集合 ⇒ 層條件落在 Set 或 Prop
  assert_true(@hott_redefine.is_sheaf_hott(@hott_core.SetLevel))
  assert_true(@hott_redefine.is_sheaf_hott(@hott_core.Prop))
  assert_true(!@hott_redefine.is_sheaf_hott(@hott_core.GroupoidLevel))

  let lin : @hott_redefine.LinearHoTT[Int] = { linear: @structures.Linear::make(10), level: @hott_core.SetLevel }
  assert_eq(@hott_redefine.linear_hott_consume(lin), 10)
}

///|
test "redefine: h-層次升降與判準" {
  // Set ↗ ∞-群胚：hlevel_up 是 h-層次的後繼
  assert_eq(@hott_core.hlevel_up(@hott_core.SetLevel), @hott_core.GroupoidLevel)
  assert_eq(@hott_core.hlevel_up(@hott_core.Prop), @hott_core.SetLevel)
  assert_true(@hott_redefine.is_two_group_hott(@hott_core.TwoGroupoidLevel))
  assert_true(!@hott_redefine.is_two_group_hott(@hott_core.GroupoidLevel))
}

///|
test "redefine: 2-群（交叉模）與路徑群胚" {
  let cm = @structures.CrossedModule::trivial(2, 4)
  assert_true(cm.check_peiffer())
  let tag = @hott_redefine.crossed_to_hott(cm)
  // 分類空間 BG 的名字由交叉模的 π0/π1 決定
  assert_true(tag.0.contains("B("))

  let g = @structures.Groupoid::pair_groupoid(["a", "b", "c"])
  let trunc = @hott_redefine.orbit_hott(g)
  // ∥G∥₀ 是 set-截斷：level = SetLevel（trunc_code = 0），值仍是原群胚
  assert_eq(trunc.level, @hott_core.SetLevel)
  assert_eq(trunc.trunc_code, 0)
  assert_eq(trunc.val.connected_components().length(), 1)
  assert_eq(@hott_redefine.path_groupoid(0).connected_components().length(), 1)
}

///|
test "redefine: 函子保存路徑、自然變換、Free 折疊" {
  let f = @hott_redefine.HoTTFunctor::make(fn(x : Int) -> Int { x * 2 })
  let p = @hott_core.refl(3)
  // 函子把 refl 映到 refl（ap 的 code 保持 0）
  assert_eq(@hott_redefine.hott_functor_preserves_paths(f, p).code, 0)

  let nat : @hott_core.Homotopy[Int, Int] = @hott_redefine.hott_natural_transformation(
    fn(x : Int) -> Int { x + 1 }, fn(x : Int) -> Int { x + 2 },
  )
  let f1 = nat.fun1 // 函數型欄位要先取出再套用（`x.f(a)` 會被當成方法呼叫）
  let f2 = nat.fun2
  assert_eq(f1(1), 2)
  assert_eq(f2(1), 3)
  assert_eq(nat.witness.length(), 0) // 尚未採樣任何見證點

  let e = @hott_core.Equiv::make(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x })
  assert_true(@hott_redefine.equivalence_as_equiv(e))

  // Free 在 HoTT 下仍是集合層級，rec 折疊結果與 structures 版一致
  let fa = @hott_redefine.free_hott_in(7)
  assert_eq(fa.level, @hott_core.SetLevel)
  let folded : (@hott_redefine.FreeHoTT[Int]) -> Int = @hott_redefine.free_hott_rec(
    true,
    fn(x : Int) -> Int { x },
    fn(_ : String, args : Array[Int]) -> Int { args[0] + args[1] },
  )
  assert_eq(folded(fa), 7)
}

///|
test "redefine: 平坦函子與單純集合/球面/餘切複形" {
  let flat = @structures.FlatFunctor::make([@structures.ObjTag("A"), @structures.ObjTag("B")])
  flat.advance(@structures.ObjTag("A"), 10)
  flat.advance(@structures.ObjTag("B"), 20)
  // 「平坦」是一條命題而非額外結構：`is_flat_hott` 內部用 `prop_trunc`（level = Prop），
  // 所以只有在 trunc_level 記為 Prop 時判準才成立；記成 SetLevel 會被拒。
  let fh = @hott_redefine.FlatHoTT::make(flat, @hott_core.Prop)
  assert_true(fh.is_flat_hott())
  let fh_set = @hott_redefine.FlatHoTT::make(flat, @hott_core.SetLevel)
  assert_true(!fh_set.is_flat_hott())
  // A2 的惰性求值語義不變：已 advance 的物件給 Some，未給的給 None
  assert_eq(@hott_redefine.flat_hott_eval(fh, @structures.ObjTag("A")), Some(10))
  assert_eq(@hott_redefine.flat_hott_eval(fh, @structures.ObjTag("B")), Some(20))
  assert_eq(@hott_redefine.flat_hott_eval(fh, @structures.ObjTag("Z")), None)
  // 空的 active 集合 ⇒ 不平坦（餘濾性失敗）
  let empty = @hott_redefine.FlatHoTT::make(@structures.FlatFunctor::make([]), @hott_core.Prop)
  assert_true(!empty.is_flat_hott())

  // 球面 S^n 的標籤帶維度；餘切複形的 Euler 數與 structures 版一致
  assert_true(@hott_redefine.hott_sphere(2).0.contains("2"))
  // 餘切複形的維度由標籤長度決定：|"abc"| = 3
  let cot = @hott_redefine.hott_cotangent(@hott_core.TypeTag("abc"))
  assert_eq(cot.euler(), @structures.cotangent_of_poly(3).euler())
  assert_eq(cot.euler(), 3)

  // Vectₖ 的張量層級：兩個 set 級向量空間的張量仍是 set
  let v1 = @hott_redefine.VectHoTT::make(2)
  let v2 = @hott_redefine.VectHoTT::make(3)
  assert_eq(@hott_redefine.vect_hott_tensor_level(v1, v2), @hott_core.SetLevel)
}
