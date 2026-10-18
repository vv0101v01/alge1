# `hott_theorems` — 新定理 N1–N6：$\pi_1(S^1)=\mathbb{Z}$ · funext · Freudenthal · 截斷萬有性 · SIP · Whitehead/Blakers-Massey

> **package** `axiom/axiom/hott_theorems` · **alias** `@hott_theorems`
> **依賴**：`@hott_core` · `@hott_hits` · `@hott_redefine` · `@univalence`
> **檔案**：`hott_new_theorems.mbt`（109 行）· `theorems_test.mbt`（黑盒測試）· `moon.pkg`
> **公開 API**：20 項 = 2 個類型 + 18 個函數 · **本 package 引入的公理：0**

## 1. 呢個資料夾做乜

呢度係**用 HoTT 證明出來嘅新定理**（相對於 `hott_redefine/` 嘅「舊結構再定義」）。
六組定理，每組都有一個**可計算嘅見證函數**，唔係得個陳述：

| 編號 | 定理 | 見證／判準 |
|---|---|---|
| **N1** | $\pi_1(S^1) = \mathbb{Z}$（Encode-Decode 方法） | `cover_code` · `encode_s1` · `decode_s1` · `pi1_s1_is_int` · `loop_space_s1_equiv_int` |
| **N2** | 函數外延性 $\mathsf{funext} : (f \sim g) \simeq (f = g)$（由單值性 + 區間導出） | `n2_funext_theorem` · `n2_funext_inv` · `n2_funext_is_equiv` |
| **N3** | 懸垂-環路伴隨 $\Sigma \dashv \Omega$ 與 **Freudenthal** 懸垂定理 | `SuspensionLoopAdj` · `freudenthal_unit` · `freudenthal_connectivity` · `n3_freudenthal_for_s1` |
| **N4** | 截斷嘅**萬有性**：$\Vert A\Vert_{-1}$ 命題反射、$\Vert A\Vert_0$ 集合反射 | `n4_trunc_universal` · `n4_prop_trunc_is_prop` |
| **N5** | **結構同一性原理 SIP** 強化版：同構嘅結構相等 | `n5_sip_monoid_path` · `n5_sip_vect` |
| **N6** | 高維群胚原型：**Blakers-Massey** 連通度下界 + **Whitehead** 原理 | `blakers_massey_connectivity` · `whitehead_principle` · `synthetic_pi` |

## 2. 公理

**無。** 呢個 package 冇 `axiom` 宣告，而且佢嘅兩條「大定理」都係**由已驗證嘅結果推出**：

- N2 `n2_funext_is_equiv()` 直接委託 `@univalence.funext_happly_is_equiv()`，
  而後者由 `funext_happly_laws(card)` 對**全部** $card^{card} \times card^{card}$ 對函數窮盡驗證。
- N5 `n5_sip_monoid_path` 嘅路徑由 `@univalence.sip_monoid` 給出，其可執行證明
  `sip_is_theorem(card)` 窮盡驗證「同構 ⇒ 沿 `ua(σ)` 傳輸後結構逐項相等」。

> **誠實邊界**：MoonBit 唔係證明助理。N1 嘅 `encode_s1` / `decode_s1` 係**整數與路徑 `code`
> 之間嘅互逆映射**（喺有限模型內可窮盡驗證），唔係型別論意義下嘅萬有覆疊空間构造；
> N3 嘅 `freudenthal_connectivity(n) = 2n` 係**公式**（連通度下界），冇對具體空間做機器檢查；
> N6 嘅 `blakers_massey_connectivity(m,n) = m+n` 同理。完整數學推導見 `docs/UNIVALENCE.md`。
> 本庫嘅「定理」= 有限模型內嘅窮盡可執行驗證 + 書面嚴格推導。

## 3. 定義（類型）

| 名稱 | 數學內容 | 實作 |
|---|---|---|
| `CoverCode` | $S^1$ 嘅**萬有覆疊** $\widetilde{S^1} \to S^1$ 嘅碼空間（$\cong \mathbb{Z}$） | `pub(all) struct { winding : Int }` |
| `SuspensionLoopAdj[A]` | 伴隨 $\Sigma \dashv \Omega$ 嘅單位／餘單位 | `{ unit : (A) -> Path[Susp[A]]; counit : (Path[Susp[A]]) -> A }` |

## 4. 定義（函數）

| 名稱 | 型別／語義 | 計算內容 |
|---|---|---|
| `cover_code(base)` | $code : S^1 \to \mathsf{CoverCode}$（Encode-Decode 嘅碼族） | `winding = 0`（在 `base` 處） |
| `encode_s1(p)` | $encode : Path_{S^1}(base,base) \to \mathbb{Z}$ | 路徑 `code` 即繞數 |
| `decode_s1(n)` | $decode : \mathbb{Z} \to Path_{S^1}(base,base)$ | 繞 `n` 圈嘅路徑（`code = n`） |
| `loop_space_s1_equiv_int()` | $\Omega(S^1, base) \simeq \mathbb{Z}$ 嘅**等價物件** | `Equiv[Path[Circle], Int]`（`to = encode_s1`, `from = decode_s1`） |
| `n2_funext_theorem(h)` | $\mathsf{funext} : (f \sim g) \to (f = g)$ | 由同倫給出路徑 |
| `n2_funext_inv(p, x)` | $\mathsf{happly} : (f = g) \to (f\,x = g\,x)$ | 路徑在點 `x` 上嘅作用 |
| `freudenthal_unit(a)` | 伴隨單位 $\eta_a : Path_{\Sigma A}(N, S)$（子午線） | `merid(a)` |
| `freudenthal_connectivity(n)` | Freudenthal：$A$ 為 $n$-連通 ⇒ $\eta : A \to \Omega\Sigma A$ 為 $2n$-連通 | `2 * n` |
| `n4_trunc_universal(level, f)` | 萬有性：$(\Vert A\Vert_n \to B) \simeq (A \to B)$ 嘅正向 | `Trunc[A] -> B` |
| `n4_prop_trunc_is_prop(t1, t2)` | $\mathsf{isProp}(\Vert A\Vert_{-1})$：任意兩點有一條路徑 | `Path[PropTrunc[A]]` |
| `n5_sip_monoid_path(m1, m2)` | SIP：同構嘅么半群結構相等 | `Path[MonoidStr]`，`code = monoid_str_defect` |
| `n5_sip_vect(v1, v2)` | SIP 推論：線性同構嘅 `VectHoTT` 相等 | `Path[VectHoTT]` |
| `blakers_massey_connectivity(m, n)` | 推出方塊嘅連通度下界：左 $m$-連通、右 $n$-連通 ⇒ $(m+n)$-餘笛卡爾 | `m + n` |
| `whitehead_principle(f_is_iso_on_pi)` | Whitehead：在所有 $\pi_n$ 上為同構 ⇒ 等價（HoTT 中 $\mathsf{isEquiv}(f) \iff \Pi(n)\,\mathsf{isEquiv}(\pi_n f)$） | 回傳輸入命題 |
| `synthetic_pi(n, m)` | $\pi_n(S^m)$ 嘅合成計算（以 $S^1$ 為基例） | `(1,1)→"ℤ"`；`n<m→"0"`；`n==m→"ℤ"`；其餘 `"unknown (合成計算)"` |

## 5. 定理與佢哋嘅可執行判準

| 定理 | 判準函數 | 內容 |
|---|---|---|
| **N1** $\pi_1(S^1) = \mathbb{Z}$ | `pi1_s1_is_int() : Bool` | 對 $n = 5$ 驗證 $encode(decode(n)) = n$ 且 $decode(encode(p)).code = p.code$；**完整窮盡**（$n = -3..3$）喺 `theorems_test.mbt` |
| **N2** funext 是等價 | `n2_funext_is_equiv() : Bool` | 委託 `@univalence.funext_happly_is_equiv()`（窮盡驗證 `funext`/`happly` 互逆） |
| **N3** Freudenthal | `n3_freudenthal_for_s1() : String` | $S^0$ 為 $(-1)$-連通 ⇒ $S^1 = \Sigma S^0$ 為 $0$-連通，$\pi_1(S^1)$ 喺穩定範圍內 |
| **N4** 截斷萬有性 | `n4_trunc_universal` / `n4_prop_trunc_is_prop` | 消除子本身即萬有性嘅正向；命題性由路徑見證 |
| **N5** SIP | `n5_sip_monoid_path` / `n5_sip_vect` | 路徑 `code = 0` ⟺ 兩個結構逐項相同（同構時由 `ua(σ)` 給出） |
| **N6** Blakers-Massey / Whitehead | `blakers_massey_connectivity` / `whitehead_principle` | 連通度下界公式 + 命題層次嘅 Whitehead 判準 |

## 6. 可運行例子

以下 ```mbt check``` 區塊由 `moon test` **真的編譯並執行**。

```mbt check
test "README N1: Encode-Decode 兩個方向互逆 ⇒ π₁(S¹) = ℤ" {
  assert_true(@hott_theorems.pi1_s1_is_int())
  // decode: ℤ → Ω(S¹)，encode: Ω(S¹) → ℤ
  for n in -3..=3 {
    let p = @hott_theorems.decode_s1(n)
    assert_eq(p.code, n)
    assert_eq(@hott_theorems.encode_s1(p), n) // encode ∘ decode = id
  }
  assert_eq(@hott_theorems.decode_s1(0).code, 0) // 繞 0 圈 = refl
  // 等價物件本身
  let e = @hott_theorems.loop_space_s1_equiv_int()
  let to = e.to
  let from = e.from
  assert_eq(to(@hott_theorems.decode_s1(4)), 4)
  assert_eq(from(4).code, 4)
  // 碼空間在 base 處的繞數為 0
  assert_eq(@hott_theorems.cover_code(@hott_hits.Circle::base()).winding, 0)
}
```

```mbt check
test "README N2: funext 與 happly 互逆" {
  let f = fn(x : Int) -> Int { x + 1 }
  let g = fn(x : Int) -> Int { x + 1 }
  // 同倫 ⇒ 路徑
  let h : @hott_core.Homotopy[Int, Int] = { fun1: f, fun2: g, witness: [] }
  let p = @hott_theorems.n2_funext_theorem(h)
  assert_eq(p.code, 0) // 逐點相同 ⇒ 虧損 0 ⇒ 原子路徑
  // happly：路徑 ⇒ 逐點路徑
  let px = @hott_theorems.n2_funext_inv(p, 5)
  assert_eq(px.code, 0)
  // 是否為等價：委託 univalence 的窮盡驗證
  assert_true(@hott_theorems.n2_funext_is_equiv())
}
```

```mbt check
test "README N3: 懸垂-環路伴隨與 Freudenthal 連通度" {
  // 單位 η_a = merid(a) : Path[Susp[A]](North, South)
  let eta = @hott_theorems.freudenthal_unit(@hott_hits.True2)
  assert_eq(eta.lhs, @hott_hits.North)
  assert_eq(eta.rhs, @hott_hits.South)
  assert_eq(eta.code, 1)
  // A 為 n-連通 ⇒ η 為 2n-連通
  assert_eq(@hott_theorems.freudenthal_connectivity(0), 0)
  assert_eq(@hott_theorems.freudenthal_connectivity(1), 2)
  assert_eq(@hott_theorems.freudenthal_connectivity(3), 6)
  // S¹ 的穩定陳述（字串摘要，供 demo/README 引用）
  assert_true(@hott_theorems.n3_freudenthal_for_s1().contains("S1"))
}
```

```mbt check
test "README N4: 截斷的萬有性與命題性" {
  // 萬有性：給 A → B 就得到 ∥A∥₀ → B
  let f = @hott_theorems.n4_trunc_universal(@hott_core.SetLevel, fn(x : Int) -> Int { x * 2 })
  assert_eq(f(@hott_core.set_trunc(21)), 42)
  // isProp(∥A∥₋₁)：任意兩個截斷元素之間有一條路徑
  let p = @hott_theorems.n4_prop_trunc_is_prop(@hott_hits.prop_trunc_in(1), @hott_hits.prop_trunc_in(9))
  assert_eq(p.lhs.val, 1)
  assert_eq(p.rhs.val, 9)
}
```

```mbt check
test "README N5: SIP — 結構相同 ⇒ 路徑 code 0；不同 ⇒ 虧損可量化" {
  let m1 : @univalence.MonoidStr = { carrier: @hott_core.TypeTag("Z3"), op: "add", unit: "0" }
  let m2 : @univalence.MonoidStr = { carrier: @hott_core.TypeTag("Z3"), op: "add", unit: "0" }
  let m3 : @univalence.MonoidStr = { carrier: @hott_core.TypeTag("Z3"), op: "mul", unit: "1" }
  // 同一個結構 ⇒ 原子路徑
  assert_eq(@hott_theorems.n5_sip_monoid_path(m1, m2).code, 0)
  // 運算與單位元都不同 ⇒ 虧損 2
  assert_eq(@univalence.monoid_str_defect(m1, m3), 2)
  assert_eq(@hott_theorems.n5_sip_monoid_path(m1, m3).code, 2)
  // VectHoTT：同維度 ⇒ 相等（線性同構即相等）
  let v1 = @hott_redefine.VectHoTT::make(3)
  let v2 = @hott_redefine.VectHoTT::make(3)
  assert_eq(@hott_theorems.n5_sip_vect(v1, v2).code, 0)
}
```

```mbt check
test "README N6: Blakers-Massey 連通度下界與 Whitehead 原理" {
  // 推出方塊：左 m-連通、右 n-連通 ⇒ (m+n)-餘笛卡爾
  assert_eq(@hott_theorems.blakers_massey_connectivity(2, 3), 5)
  assert_eq(@hott_theorems.blakers_massey_connectivity(0, 0), 0)
  // Whitehead：在所有 πₙ 上同構 ⇒ 等價
  assert_true(@hott_theorems.whitehead_principle(true))
  assert_true(!@hott_theorems.whitehead_principle(false))
  // 合成同倫群 πₙ(Sᵐ)
  assert_eq(@hott_theorems.synthetic_pi(1, 1), "ℤ") // π₁(S¹) = ℤ
  assert_eq(@hott_theorems.synthetic_pi(1, 2), "0") // π₁(S²) = 0（n < m）
  assert_eq(@hott_theorems.synthetic_pi(3, 3), "ℤ") // π₃(S³) = ℤ（n = m）
}
```

## 7. 測試

| 檔案 | 內容 |
|---|---|
| `theorems_test.mbt` | 黑盒測試：`pi1_s1_is_int` / `synthetic_pi` / `blakers_massey_connectivity` / `whitehead_principle` + Encode-Decode 對 $n=-3..3$ 嘅互逆 |
| 本檔 §6 | 6 個 `mbt check` 文件測試（N1–N6 各一），由 `moon test` 執行 |

## 8. 去邊

- **`hott_hits/`** — `Circle` / `Susp` / `PropTrunc` 嘅 HIT 定義（N1、N3、N4 嘅原料）
- **`univalence/`** — N2（funext）與 N5（SIP）嘅**窮盡證明**所在
- **`hott_algorithms/`** — 把呢啲定理變成演算法：H4 `synthetic_loop_add` 用 N1 把路徑合成化成整數加法
- **`docs/UNIVALENCE.md`** — 單值性、funext、SIP 嘅完整書面推導與實驗數據
