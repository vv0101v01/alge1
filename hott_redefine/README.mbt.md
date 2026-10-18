# `hott_redefine` — 用 HoTT 重新定義原有數學結構（範疇 · 三大函子 · Vectₖ · ∞-Topos · 線性邏輯 · 同倫代數 · 群胚/2-群）

> **package** `axiom/axiom/hott_redefine` · **alias** `@hott_redefine`
> **依賴**：`@hott_core` · `@hott_hits` · `@structures`
> **檔案**：`hott_redefine.mbt`（166 行）· `redefine_test.mbt`（黑盒測試，5 個）· `moon.pkg`
> **公開 API**：31 項 = 7 個類型 + 24 個函數 · **本 package 引入的公理：0**

## 1. 呢個資料夾做乜

`structures/` 入面嘅代數結構（範疇、等價／自由／平坦三大函子、Vectₖ、Site/Sheaf、
線性邏輯 `Lolli`、單純集合 `SSet`、群胚、交叉模）係用**集合論式**嘅方式寫嘅。
呢個 package 把佢哋**逐項翻譯成 HoTT 嘅說法**：每個結構多帶一個 `@hott_core.HLevel`，
於是「呢個結構係咪集合？係咪群胚？」由**證明義務**變成**可判定嘅資料**。

八個分節，對應原庫嘅八個主題：

| 分節 | 原結構 | HoTT 再定義 |
|---|---|---|
| 1 | `Category` / `Functor` / `NaturalTransformation` | `HoTTCat`（對象類型 + h-層次）· `HoTTFunctor`（`ap` 保持路徑）· `hott_natural_transformation`（同倫） |
| 2 | `Equivalence` / `Free` / `FlatFunctor` | `equivalence_as_equiv`（`Equiv[A,B]`）· `FreeHoTT`（HIT 點構造 + Set 層次）· `FlatHoTT`（n-截斷濾餘極限） |
| 3 | `Vect` / `LinMap` / `SparseVect` | `VectHoTT`（Set 層次；相等即線性同構）· `vect_hott_path` · `vect_hott_tensor_level` |
| 4 | `Site` / `Sheaf` / `Topos` | `InfTopos`（類型即空間，層即截斷類型族）· `is_sheaf_hott` |
| 5 | `Linear` / `Lolli` | `LinearHoTT[A]`（線性指數 `!A` ↔ 截斷）· `linear_hott_consume` · `linear_hott_is_equiv` |
| 6 | `SSet` / `CotangentComplex` | `hott_sphere`（$S^n = \Sigma^n S^0$）· `hott_cotangent` |
| 7 | `Groupoid` / `CrossedModule` | `is_groupoid_hott`（1-類型）· `is_two_group_hott`（2-類型）· `path_groupoid` · `crossed_to_hott`（$B(G,H)$）· `orbit_hott`（$\Vert A\Vert_0$） |
| 8 | `algorithms` A2 / A9 | `flat_hott_eval`（截斷消除嘅惰性求值）· `orbit_hott`（0-截斷商） |

## 2. 公理

**無。** 呢個 package 冇 `axiom` 宣告。所有「再定義」都係**有計算內容嘅函數**：
h-層次由輸入決定（`HoTTCat::make(tag, level)` 記錄 `level`）、路徑由 `@hott_core.ap`
計算（`hott_functor_preserves_paths`）、截斷由 `@hott_core.set_trunc` 計算（`orbit_hott`）。

> **誠實邊界（三個佔位實作，已標明）**：以下三項係**語義佔位**，回傳常量而唔係由輸入計算，
> 用之前必須知道：
>
> | 函數 | 實作 | 應該點睇 |
> |---|---|---|
> | `vect_hott_tensor_level(v1, v2)` | `ignore` 兩個輸入，恆回 `SetLevel` | 「$\mathsf{Set} \otimes \mathsf{Set} = \mathsf{Set}$（0-截斷封閉）」呢條**陳述**係啱嘅，但實作冇真係檢查 `v1`/`v2` |
> | `linear_hott_is_equiv(lolli)` | `ignore(lolli)`，恆回 `true` | 佔位；真正嘅等價判定請用 `@hott_core.Equiv::is_equiv()`（睇兩個虧損碼） |
> | `path_groupoid(_a)` | 恆回 `Groupoid::discrete(["*"])` | 佔位；「$Path[A]$ 構成 ∞-群胚」係陳述層面嘅事實，實作只給單點離散群胚 |
>
> 另外 `InfTopos::from_site(site)` 把 `is_infty` 固定設為 `true`、`trunc_level` 固定設為
> `NType(100)`（即「∞」嘅有限替身）；`FlatHoTT::is_flat_hott()` 內部用 `prop_trunc`
> 比對，所以**只有 `trunc_level = Prop` 時判準先成立**——呢個係有意義嘅數學事實
> （平坦性係命題、唔係額外結構），`redefine_test.mbt` 兩個方向都斷言咗。
>
> 同全庫一樣：MoonBit 唔係證明助理，`Path` 嘅端點唔會被型別檢查器驗證。
> 呢度嘅「再定義」= 可執行嘅結構翻譯 + 書面數學對應（`docs/UNIVALENCE.md`）。

## 3. 定義（類型）

| 名稱 | 數學內容 | 實作（欄位） |
|---|---|---|
| `HoTTCat` | HoTT 範疇：對象類型 $Ob : \mathsf{Type}$，前 n-層次決定 h-層次為 $(n+1)$-類型；態射為依賴類型 $Hom : Ob \to Ob \to \mathsf{Type}$ | `{ obj_tag : TypeTag; hlevel : HLevel; hom_truncated : Bool }` |
| `HoTTFunctor[A, B]` | HoTT 函子：映射對象 + 映射態射（保持路徑，即 `ap`） | `{ obj_map : (A) -> B; preserves_comp : Bool }` |
| `FreeHoTT[A]` | 自由函子 $F \dashv U$ 對應 HIT 嘅點構造自由生成（自由么半群 = List 作為 HIT） | `{ val : @structures.Free[A]; level : HLevel }` |
| `FlatHoTT` | 平坦函子 = n-截斷嘅濾餘極限 $\Vert \mathsf{colim}_i\,Hom(A_i,-)\Vert_n$ | `{ flat : @structures.FlatFunctor; trunc_level : HLevel }` |
| `VectHoTT` | $\mathsf{Vect}_k$ 係 Set 層次（0-截斷）嘅類型，**相等即線性同構** | `{ dim : Int; carrier_tag : TypeTag; is_set : Bool }` |
| `InfTopos` | ∞-Topos = 類型論嘅語義模型：類型即空間、層即截斷類型族；Site 為類型、覆蓋族為命題截斷嘅族 | `{ base : @structures.Site; is_infty : Bool; trunc_level : HLevel }` |
| `LinearHoTT[A]` | 線性類型 $!A$ 解釋為模態算子 ♭/♯ 或截斷；$\Vert A\Vert$ 與 $!A$ 共享「可複製／可丟棄」語義 | `{ linear : @structures.Linear[A]; level : HLevel }` |

## 4. 再定義（函數）

| 名稱 | 對應原定理／結構 | 計算內容 |
|---|---|---|
| `HoTTCat::make(tag, level)` | `Category` | 記錄對象類型名 + h-層次，`hom_truncated = true`（1-範疇） |
| `HoTTFunctor::make(f)` | `Functor` | `{ obj_map: f, preserves_comp: true }` |
| `hott_natural_transformation(f, g)` | `NaturalTransformation` | `Homotopy { fun1: f, fun2: g, witness: [] }`（同倫 $\alpha : \Pi(x:A)\,Path_B(Fx,Gx)$） |
| `hott_functor_preserves_paths(f, p)` | **定理 HoTT-1**（再定義原定理 1）：$F$ 保同構 ⇒ $ap_F : Path_A(x,y) \to Path_B(Fx,Fy)$ 且保 refl/sym/trans | `@hott_core.ap(f.obj_map, p)` |
| `equivalence_as_equiv(e)` | `Equivalence`（三角恆等式） | `e.is_equiv()`；單值性把它提升為 $Path_{\mathsf{TypeTag}}(A,B)$ |
| `free_hott_in(a)` | `Free`／`Return` | `{ val: @structures.Return(a), level: SetLevel }` |
| `free_hott_rec(is_set_b, ret, op_case)` | `Free::fold` | 回傳 `FreeHoTT[A] -> B`，內部走 `@structures.Free::fold` |
| `FlatHoTT::make(flat, level)` | `FlatFunctor` | 記錄平坦函子 + 截斷層次 |
| `FlatHoTT::is_flat_hott()` | 平坦 ⇔ n-截斷後保有限極限 | `flat.is_flat() && is_truncated(prop_trunc(0), trunc_level)` |
| `VectHoTT::make(dim)` | `Vect` | `{ dim, carrier_tag: TypeTag("k^" + dim), is_set: true }` |
| `vect_hott_path(v1, v2, e)` | 線性同構 ⇒ 相等（由單值性） | `code = v1.dim - v2.dim`（**同維度 ⇒ 0**） |
| `vect_hott_tensor_level(v1, v2)` | 張量／直和保持 h-層次 | 佔位：恆 `SetLevel`（見 §2） |
| `InfTopos::from_site(site)` | `Site` / `Sheaf` / `Topos` | `{ base: site, is_infty: true, trunc_level: NType(100) }` |
| `is_sheaf_hott(level)` | 層條件：$F$ 為層 ⟺ 對覆蓋篩 $S$，$Map(S,F)$ 為命題截斷嘅極限 | `level == SetLevel \|\| level == Prop` |
| `linear_hott_consume(l)` | `Linear::consume`（線性消耗） | `l.linear.consume()` |
| `linear_hott_is_equiv(lolli)` | $A \multimap B$ 嘅 HoTT 路徑即線性等價保持 | 佔位：恆 `true`（見 §2） |
| `hott_sphere(n)` | `SSet::standard_simplex` → HIT $S^n = \Sigma S^{n-1}$ | `"S0=Bool"` / `"S1=Circle"` / `"S2=Susp(S1)"` … |
| `hott_cotangent(tag)` | 合成餘切複形 $L_{A/k}$ = 類型 $A$ 嘅切叢 | `@structures.cotangent_of_poly(tag.0.length())`（維度 = 標籤長度） |
| `is_groupoid_hott(level)` | 群胚 = 1-類型 | `level == GroupoidLevel` |
| `is_two_group_hott(level)` | 2-群 = 2-類型 | `level == TwoGroupoidLevel` |
| `path_groupoid(_a)` | $Path[A]$ 構成 ∞-群胚 | 佔位：`Groupoid::discrete(["*"])`（見 §2） |
| `crossed_to_hott(cm)` | 交叉模 $(H \to G)$ ↔ 2-截斷類型 $B(G,H)$ | `TypeTag("B(" + g_order + "," + h_order + ")")` |
| `flat_hott_eval(fh, obj)` | **A2** 平坦惰性求值 = 截斷消除嘅高效實現 | `fh.flat.eval(obj)` |
| `orbit_hott(g)` | **A9** 群胚商化 = $\Vert A\Vert_0$ 嘅集合截斷商（$BG$ 嘅 0-截斷即軌道集合） | `@hott_core.set_trunc(g)` |

## 5. 定理

| 名稱 | 陳述 | 驗證方式 |
|---|---|---|
| **HoTT-1** `hott_functor_preserves_paths` | HoTT 函子保持路徑即保持同構：$ap_F$ 保 refl/sym/trans | 定義即 `@hott_core.ap`；`redefine_test.mbt` 斷言 $ap_F(refl) = refl$（`code = 0`） |
| `is_sheaf_hott` | 層條件喺 HoTT 下等价於「截斷層次 ∈ {Prop, Set}」 | 可執行判準；`redefine_test.mbt` 三個層次都斷言 |
| `FlatHoTT::is_flat_hott` | 平坦性係**命題**（h-level $-1$）而非額外結構 | 兩個方向都斷言：`Prop` ⇒ true，`SetLevel` ⇒ false |
| `crossed_to_hott` | 交叉模 ↔ 2-截斷類型 $B(G,H)$ | 標籤由 $\vert G\vert, \vert H\vert$ 計算；Peiffer 恆等式由 `@structures.CrossedModule::check_peiffer()` 驗證 |
| `orbit_hott` | $\Vert G\Vert_0$ 嘅 0-截斷即軌道集合 | `redefine_test.mbt` 斷言 `trunc.level = SetLevel`、`trunc_code = 0`、連通分量數 = 1 |

> 更強嘅 SIP（結構同一性原理：同構嘅結構**相等**）喺 `hott_theorems/` 嘅 N5
> （`n5_sip_monoid_path` / `n5_sip_vect`，用呢度嘅 `VectHoTT`），其窮盡證明喺 `univalence/`。

## 6. 可運行例子

以下 ```mbt check``` 區塊由 `moon test` **真的編譯並執行**。

```mbt check
test "README §1: 範疇與函子的 HoTT 再定義" {
  // 範疇 = 對象類型 + h-層次
  let cat = @hott_redefine.HoTTCat::make(@hott_core.TypeTag("Ob"), @hott_core.GroupoidLevel)
  assert_eq(cat.hlevel, @hott_core.GroupoidLevel)
  assert_true(cat.hom_truncated)
  assert_true(@hott_redefine.is_groupoid_hott(cat.hlevel)) // 群胚 = 1-類型
  // 函子保持路徑（定理 HoTT-1）：ap_F(refl) = refl
  let f = @hott_redefine.HoTTFunctor::make(fn(x : Int) -> Int { x * 2 })
  assert_eq(@hott_redefine.hott_functor_preserves_paths(f, @hott_core.refl(3)).code, 0)
  assert_eq(@hott_redefine.hott_functor_preserves_paths(f, @hott_core.refl(3)).lhs, 6)
  // 自然變換 = 同倫
  let nat : @hott_core.Homotopy[Int, Int] = @hott_redefine.hott_natural_transformation(
    fn(x : Int) -> Int { x + 1 }, fn(x : Int) -> Int { x + 2 },
  )
  let f1 = nat.fun1 // 函數型欄位要先取出再套用
  assert_eq(f1(1), 2)
  assert_eq(nat.witness.length(), 0)
}
```

```mbt check
test "README §2: 三大函子 — 等價 / 自由 / 平坦" {
  // 等價函子 ⇒ HoTT 的 Equiv
  let e = @hott_core.Equiv::make(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x })
  assert_true(@hott_redefine.equivalence_as_equiv(e))
  // 自由 = HIT 的點構造，落在 Set 層次；fold 與 structures 版一致
  let fa = @hott_redefine.free_hott_in(7)
  assert_eq(fa.level, @hott_core.SetLevel)
  let folded : (@hott_redefine.FreeHoTT[Int]) -> Int = @hott_redefine.free_hott_rec(
    true,
    fn(x : Int) -> Int { x },
    fn(_ : String, args : Array[Int]) -> Int { args[0] + args[1] },
  )
  assert_eq(folded(fa), 7)
  // 平坦 = n-截斷的濾餘極限；平坦性是「命題」⇒ 層次要記 Prop
  let flat = @structures.FlatFunctor::make([@structures.ObjTag("A"), @structures.ObjTag("B")])
  flat.advance(@structures.ObjTag("A"), 10)
  flat.advance(@structures.ObjTag("B"), 20)
  let fh = @hott_redefine.FlatHoTT::make(flat, @hott_core.Prop)
  assert_true(fh.is_flat_hott())
  assert_true(!@hott_redefine.FlatHoTT::make(flat, @hott_core.SetLevel).is_flat_hott())
  // A2 的惰性求值語義不變
  assert_eq(@hott_redefine.flat_hott_eval(fh, @structures.ObjTag("A")), Some(10))
  assert_eq(@hott_redefine.flat_hott_eval(fh, @structures.ObjTag("Z")), None)
}
```

```mbt check
test "README §3-5: Vectₖ / ∞-Topos / 線性邏輯" {
  // Vectₖ 是 Set；相等即線性同構 ⇒ 同維度的路徑 code = 0
  let v1 = @hott_redefine.VectHoTT::make(3)
  let v2 = @hott_redefine.VectHoTT::make(3)
  assert_true(v1.is_set)
  let id_e = @hott_core.Equiv::make(fn(x : @hott_redefine.VectHoTT) -> @hott_redefine.VectHoTT { x }, fn(x : @hott_redefine.VectHoTT) -> @hott_redefine.VectHoTT { x })
  assert_eq(@hott_redefine.vect_hott_path(v1, v2, id_e).code, 0)
  assert_eq(@hott_redefine.vect_hott_path(v1, @hott_redefine.VectHoTT::make(5), id_e).code, -2)
  assert_eq(@hott_redefine.vect_hott_tensor_level(v1, v2), @hott_core.SetLevel)
  // ∞-Topos：Site 為類型，層條件落在 Set / Prop
  let t = @hott_redefine.InfTopos::from_site(@structures.Site::make([@structures.ObjTag("U"), @structures.ObjTag("V")]))
  assert_true(t.is_infty)
  assert_true(@hott_redefine.is_sheaf_hott(@hott_core.SetLevel))
  assert_true(@hott_redefine.is_sheaf_hott(@hott_core.Prop))
  assert_true(!@hott_redefine.is_sheaf_hott(@hott_core.GroupoidLevel))
  // 線性邏輯：consume 語義不變（(5+1)*2 = 12 見 structures 的 Lolli 測試）
  let lin : @hott_redefine.LinearHoTT[Int] = { linear: @structures.Linear::make(10), level: @hott_core.SetLevel }
  assert_eq(@hott_redefine.linear_hott_consume(lin), 10)
}
```

```mbt check
test "README §6: 同倫代數 — 球面迭代與餘切複形" {
  // S⁰ = Bool，Sⁿ⁺¹ = ΣSⁿ（HIT 的 Susp 在 hott_hits）
  assert_eq(@hott_redefine.hott_sphere(0), @hott_core.TypeTag("S0=Bool"))
  assert_eq(@hott_redefine.hott_sphere(1), @hott_core.TypeTag("S1=Circle"))
  assert_eq(@hott_redefine.hott_sphere(2), @hott_core.TypeTag("S2=Susp(S1)"))
  // 餘切複形 L_{A/k}：維度由標籤長度決定
  let cot = @hott_redefine.hott_cotangent(@hott_core.TypeTag("abc"))
  assert_eq(cot.euler(), 3)
  assert_eq(cot.euler(), @structures.cotangent_of_poly(3).euler())
}
```

```mbt check
test "README §7-8: 群胚 / 2-群 / 軌道商化" {
  // 交叉模 (H → G) ↔ 2-截斷類型 B(G,H)；Peiffer 恆等式先決
  let cm = @structures.CrossedModule::trivial(2, 4)
  assert_true(cm.check_peiffer())
  assert_eq(cm.pi0(), 4) // π₀ = |G|/|Im ∂|
  assert_eq(cm.pi1(), 2) // π₁ = |Ker ∂|
  let tag = @hott_redefine.crossed_to_hott(cm)
  assert_eq(tag, @hott_core.TypeTag("B(4,2)"))
  assert_true(@hott_redefine.is_two_group_hott(@hott_core.TwoGroupoidLevel))
  // A9：軌道集合 = ∥G∥₀ 的 0-截斷
  let g = @structures.Groupoid::pair_groupoid(["a", "b", "c"])
  assert_eq(g.connected_components().length(), 1)
  let trunc = @hott_redefine.orbit_hott(g)
  assert_eq(trunc.level, @hott_core.SetLevel)
  assert_eq(trunc.trunc_code, 0)
  assert_eq(trunc.val.connected_components().length(), 1)
  // 佔位實作（見 §2）：path_groupoid 恆給單點離散群胚
  assert_eq(@hott_redefine.path_groupoid(0).connected_components().length(), 1)
}
```

## 7. 測試

| 檔案 | 內容 |
|---|---|
| `redefine_test.mbt` | 5 個黑盒測試：四種結構嘅 h-層次 · h-層次升降與判準 · 2-群與路徑群胚 · 函子／自然變換／Free 折疊 · 平坦函子與球面／餘切複形 |
| 本檔 §6 | 5 個 `mbt check` 文件測試，由 `moon test` 執行 |

## 8. 去邊

- **`structures/`** — 被再定義嘅原結構（`Category`、`Free`、`FlatFunctor`、`Vect`、`Site`、`Linear`、`SSet`、`Groupoid`、`CrossedModule`）
- **`hott_core/`** — `HLevel` / `Trunc` / `Path` / `Equiv` / `ap`：再定義嘅目標語言
- **`hott_theorems/`** — N5 SIP 用呢度嘅 `VectHoTT` 證明「線性同構即相等」
- **`univalence/`** — 單值性令「同構 ⇒ 相等」呢一步合法（`sip_monoid` / `sip_is_theorem`）
- **`docs/UNIVALENCE.md`** — SIP 嘅完整推導與有限么半群分類實驗（7 個同構類 = OEIS A058129）
