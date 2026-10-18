# `hott_hits` — 高歸納類型（HITs）：區間 · 圓 · 懸垂 · 推出 · 命題截斷 · 商

> **package** `axiom/axiom/hott_hits` · **alias** `@hott_hits` · **依賴**：`@hott_core`
> **檔案**：`hott_hits.mbt`（143 行）· `hits_test.mbt`（黑盒測試）· `moon.pkg`
> **公開 API**：30 項 = 8 個類型 + 22 個函數 · **本 package 引入的公理：0**

## 1. 呢個資料夾做乜

**高歸納類型**（higher inductive type）一次過指定**點構造子**同**路徑構造子**，
對應拓撲上嘅**胞腔附著**：`Circle` 由一個點 `base` 加一條閉路 `loop` 生成，
`Susp[A]` 由兩個極點加每點一條子午線 `merid(a)` 生成，`Pushout` 由兩邊嘅點加
`glue` 路徑生成。呢度實現六個 HIT 家族：

| HIT | 點構造 | 路徑構造 | 對應空間 |
|---|---|---|---|
| `Interval` | `left()` `right()` | `interval_seg()` | $I = [0,1]$ |
| `Circle` | `base()` | `circle_loop()` | $S^1$ |
| `Susp[A]` | `North` `South` | `merid(a)` | $\Sigma A$（$S^{n+1} = \Sigma S^n$） |
| `Pushout[A,B,C]` | `inl(b)` `inr(c)` | `pushout_glue(a, span)` | $B \sqcup^A C$ |
| `PropTrunc[A]` | `prop_trunc_in(a)` | `prop_trunc_path(x,y)` | $\Vert A \Vert_{-1}$ |
| `Quotient[A]` | `quotient_in(a)` | `quotient_rel(a,b,rel)` | $A/R$ |

每個 HIT 都配有**消除子**（`interval_rec` / `circle_rec` / `susp_rec` / `prop_trunc_rec`）
同佢嘅**計算律**（β-rule），消除子在編譯時特化為模式匹配，冇路徑物化 ⇒ 零成本。

## 2. 公理

**無。** 呢個 package 冇 `axiom` 宣告。所有路徑構造子都係**有計算內容嘅函數**：
`circle_loop()` 直接給出 `{ lhs: base, rhs: base, code: 1 }`，即「繞一圈」嘅編碼；
`merid(a)` 給 `{ North, South, code: 1 }`。

> **誠實邊界**：MoonBit 唔係證明助理。`Circle` 呢度實作為一個帶 `tag` 嘅結構（得一個
> 元素 `base`），而唔係一個真正嘅同倫類型：`loop` 係一條 `code = 1` 嘅 `Path[Circle]` 資料，
> 型別檢查器**唔會**驗證佢唔等於 `refl(base)`。$S^1$ 嘅非平凡性 therefore 靠
> (a) `circle_not_contr()` 嘅命題層次陳述，(b) `hott_theorems/` 嘅 Encode-Decode
> 定理 $\Omega S^1 \simeq \mathbb{Z}$（`encode_s1` / `decode_s1` 互逆，`theorems_test.mbt` 窮盡 $n=-3..3$），
> 同 (c) `docs/UNIVALENCE.md` 嘅書面推導。**唔係**機器檢查嘅形式證明。

## 3. 定義（類型）

| 名稱 | 數學內容 | 實作 |
|---|---|---|
| `Interval` | 區間 $I$（兩端點 + 一條 seg） | `struct { tag : String }`，`"0"` / `"1"` |
| `Circle` | 圓 $S^1$（`base` + `loop`） | `struct { tag : String }`，只有 `"base"` |
| `Susp[A]` | 懸垂 $\Sigma A$ | `enum { North, South }` |
| `Bool2` | $S^0$（迭代定義 $S^{n+1} = \Sigma S^n$ 嘅起點） | `enum { True2, False2 }` |
| `Span[A, B, C]` | 推出嘅輸入圖 $A \to B$, $A \to C$ | `struct { left_map, right_map }` |
| `Pushout[A, B, C]` | 推出 $B \sqcup^A C$ | `struct { tag; left_val : B?; right_val : C? }` |
| `PropTrunc[A]` | 命題截斷 $\Vert A \Vert_{-1}$ **作為 HIT** | `struct { val : A; code : Int }` |
| `Quotient[A]` | 商 $A/R$ **作為 HIT** | `struct { cls : A; rel_code : Int }` |

> `Trunc[A]`（一般 n-截斷，含層次資訊）喺 `hott_core`；呢度嘅 `PropTrunc[A]` 係
> 佢嘅 **HIT 版本**（帶 `prop_trunc_path` 路徑構造子），兩者並存。

## 4. 定義（構造子與消除子）

| 名稱 | 型別／語義 | 計算內容 |
|---|---|---|
| `Interval::left()` / `right()` | $0, 1 : I$ | `tag = "0"` / `"1"` |
| `interval_seg()` | $seg : Path_I(0,1)$ | `code = 1` |
| `interval_rec(x0, x1, seg_case)` | 區間歸納：給 $Path_X(x_0,x_1)$ 即得 $I \to X$ | 端點分派；path case 以 `code` 模擬傳輸 |
| `Circle::base()` | $base : S^1$ | `tag = "base"` |
| `circle_loop()` | $loop : Path_{S^1}(base, base)$ | `code = 1`（繞一圈） |
| `circle_rec(c, loop_case)` | 圓消除：$S^1 \to X$ | 恆定回 `c`；計算律 $f(base) = c$ |
| `circle_rec_beta_loop(c, loop_case)` | **β-律** $ap_f(loop) = loop\_case$ 嘅見證 | 直接回傳 `loop_case` |
| `merid(a)` | 子午線 $merid_a : Path_{\Sigma A}(N, S)$ | `code = 1` |
| `susp_rec(n, s, merid_case)` | 懸垂消除 $\Sigma A \to X$ | `match North/South` |
| `sphere_dim(n)` | $S^0 = \mathsf{Bool}$，$S^{n+1} = \Sigma S^n$ 嘅字串描述 | `"S2 = Susp(S1)"` |
| `pushout_inl(b)` / `pushout_inr(c)` | 推出嘅兩個點構造 | `tag = "inl"` / `"inr"` |
| `pushout_glue(a, span)` | $glue_a : inl(f\,a) = inr(g\,a)$ | 端點由 `span` 嘅兩個映射算出，`code = 1` |
| `prop_trunc_in(a)` | $\vert a \vert : \Vert A \Vert$ | `code = 0` |
| `prop_trunc_path(x, y)` | 命題性：$\Vert A\Vert$ 任意兩點相等 | `code = 1` |
| `prop_trunc_rec(is_prop_b, f)` | **萬有性**：若 $B$ 為命題則 $(\Vert A\Vert \to B) \simeq (A \to B)$ | `fn(t) { f(t.val) }` |
| `quotient_in(a)` | $[a] : A/R$ | `rel_code = 0` |
| `quotient_rel(a, b, rel)` | 關係路徑 $[a] = [b]$ | `code = 1` |
| `circle_encode(c, base_loops)` | Encode-Decode **原型**：路徑 → 繞數 | 回傳 `base_loops` |
| `circle_decode(n)` | Decode：繞數 → 路徑 | `code = n` |

## 5. 定理

| 名稱 | 陳述 | 驗證方式 |
|---|---|---|
| `circle_not_contr()` | $S^1$ **非可縮** $\iff$ 並非所有類型皆為集合（命題層次） | 命題陳述；可計算內容由 `hott_theorems/pi1_s1_is_int()` 與 Encode-Decode 互逆給出 |
| `circle_rec_beta_loop(c, loop_case)` | 圓消除子嘅 **β-律**：$ap_{\mathsf{circle\_rec}}(loop) \equiv loop\_case$ | 結構相等（回傳見證本身）；`hits_test.mbt` 覆蓋 |
| `prop_trunc_rec(is_prop_b, f)` | 命題截斷嘅**萬有性** $(\Vert A\Vert \to B) \simeq (A \to B)$（$B$ 命題時） | 消除子嘅定義即萬有性嘅一半；書面推導見 `docs/UNIVALENCE.md` §3 |
| $\Omega S^1 \simeq \mathbb{Z}$（Encode-Decode） | **不在本 package**：`@hott_theorems.encode_s1` / `decode_s1` | `hott_theorems/theorems_test.mbt` 對 $n = -3..3$ 驗證 $encode \circ decode = id$ |

## 6. 可運行例子

以下 ```mbt check``` 區塊由 `moon test` **真的編譯並執行**。

```mbt check
test "README: 區間 I 的兩個端點與 seg" {
  assert_eq(@hott_hits.Interval::left(), @hott_hits.Interval::left())
  assert_true(@hott_hits.Interval::left() != @hott_hits.Interval::right())
  let seg = @hott_hits.interval_seg()
  assert_eq(seg.lhs, @hott_hits.Interval::left())
  assert_eq(seg.rhs, @hott_hits.Interval::right())
  assert_eq(seg.code, 1)
  // 區間歸納：給一條 Path[X](x0,x1) 就得到 I → X
  let f = @hott_hits.interval_rec(10, 20, @hott_core.refl(10))
  assert_eq(f(@hott_hits.Interval::left()), 10)
  assert_eq(f(@hott_hits.Interval::right()), 20)
}
```

```mbt check
test "README: 圓 S¹ 的 base/loop 與消除子的 β-律" {
  let base = @hott_hits.Circle::base()
  let my_loop = @hott_hits.circle_loop()
  assert_eq(my_loop.lhs, base)
  assert_eq(my_loop.rhs, base)
  assert_eq(my_loop.code, 1) // 繞一圈；注意它結構上不是 refl（code 0）
  assert_true(my_loop.code != @hott_core.refl(base).code)
  // circle_rec 的點計算律：f(base) = c
  let f = @hott_hits.circle_rec(0, @hott_core.refl(0))
  assert_eq(f(base), 0)
  // β-律：ap_f(loop) = loop_case
  let lc = @hott_core.refl(7)
  assert_eq(@hott_hits.circle_rec_beta_loop(7, lc).code, lc.code)
  // Decode：整數 n ↦ 繞 n 圈的路徑（Encode-Decode 的完整定理在 hott_theorems）
  assert_eq(@hott_hits.circle_decode(5).code, 5)
  assert_eq(@hott_hits.circle_encode(base, 3), 3)
}
```

```mbt check
test "README: 懸垂 ΣA 與迭代球面 Sⁿ⁺¹ = ΣSⁿ" {
  // S¹ = Susp(S⁰) = Susp(Bool)
  assert_eq(@hott_hits.sphere_dim(0), "S0 = Bool")
  assert_eq(@hott_hits.sphere_dim(1), "S1 = Susp(S0)")
  assert_eq(@hott_hits.sphere_dim(3), "S3 = Susp(S2)")
  // 子午線：North 到 South 的一條路徑
  let m : @hott_core.Path[@hott_hits.Susp[@hott_hits.Bool2]] = @hott_hits.merid(@hott_hits.True2)
  assert_eq(m.lhs, @hott_hits.North)
  assert_eq(m.rhs, @hott_hits.South)
  assert_eq(m.code, 1)
  // 懸垂消除子
  let f = @hott_hits.susp_rec(1, -1, fn(_ : @hott_hits.Bool2) -> @hott_core.Path[Int] { @hott_core.refl(0) })
  assert_eq(f(@hott_hits.North), 1)
  assert_eq(f(@hott_hits.South), -1)
}
```

```mbt check
test "README: 推出 B ⊔^A C 的 glue 路徑" {
  // span: A = Int → B = String（偶/奇）, A → C = Int（平方）
  let span : @hott_hits.Span[Int, String, Int] = {
    left_map: fn(a : Int) -> String { if a % 2 == 0 { "even" } else { "odd" } },
    right_map: fn(a : Int) -> Int { a * a },
  }
  let g = @hott_hits.pushout_glue(3, span)
  // Pushout 沒有 derive(Eq)（欄位含 B?/C? 泛型），所以逐欄位比較
  assert_eq(g.lhs.tag, "inl")
  assert_eq(g.lhs.left_val, Some("odd"))
  assert_eq(g.lhs.right_val, None)
  assert_eq(g.rhs.tag, "inr")
  assert_eq(g.rhs.left_val, None)
  assert_eq(g.rhs.right_val, Some(9))
  assert_eq(g.code, 1) // glue 是一條路徑，不是相等判定
  // S¹ 也可寫成推出：two points ⊔^two points（此處只演示 glue 的計算）
}
```

```mbt check
test "README: 命題截斷 ∥A∥ 的命題性與萬有性" {
  let x = @hott_hits.prop_trunc_in(1)
  let y = @hott_hits.prop_trunc_in(2)
  // 命題性：任意兩個元素之間有一條路徑（∥A∥ 是 -1 類型）
  let p = @hott_hits.prop_trunc_path(x, y)
  assert_eq(p.lhs.val, 1)
  assert_eq(p.rhs.val, 2)
  assert_eq(p.code, 1)
  // 萬有性：對命題目標 B，∥A∥ → B 就是 A → B
  // isProp(Bool) 的見證：任意兩個布林值之間給一條路徑
  let is_prop_b : @hott_core.IsProp[Bool] = {
    witness: fn(_a : Bool, _b : Bool) -> @hott_core.Path[Bool] { @hott_core.refl(true) },
  }
  let f = @hott_hits.prop_trunc_rec(is_prop_b, fn(a : Int) -> Bool { a > 0 })
  assert_true(f(x))
  assert_true(!f(@hott_hits.prop_trunc_in(-5)))
}
```

```mbt check
test "README: 商 A/R 的點與關係路徑" {
  let a = @hott_hits.quotient_in(4)
  let b = @hott_hits.quotient_in(6)
  assert_eq(a.cls, 4)
  assert_eq(a.rel_code, 0)
  assert_eq(b.cls, 6)
  // 關係路徑 [4] = [6]（例如 mod 2 的商）
  let r = @hott_hits.quotient_rel(4, 6, 4 % 2 == 6 % 2)
  assert_eq(r.lhs.cls, 4)
  assert_eq(r.rhs.cls, 6)
  assert_eq(r.code, 1)
}
```

## 7. 測試

| 檔案 | 內容 |
|---|---|
| `hits_test.mbt` | 黑盒測試：`Circle::base` / `circle_loop` / `circle_rec` |
| 本檔 §6 | 6 個 `mbt check` 文件測試，由 `moon test` 執行 |

## 8. 去邊

- **`hott_core/`** — `Path` / `ap` / `transport` / `Trunc` 嘅定義
- **`hott_theorems/`** — $\pi_1(S^1) = \mathbb{Z}$ 嘅完整 Encode-Decode 定理（`encode_s1` / `decode_s1` / `pi1_s1_is_int`）
- **`hott_redefine/`** — `hott_sphere(n)` 把 `SSet::standard_simplex` 重述為 $S^n = \Sigma^n S^0$
- **`docs/UNIVALENCE.md`** — HIT 與單值性嘅關係（區間 $I$ 如何給出 `funext`）
