# `hott_core` — HoTT 核心：路徑 · 傳輸 · 同倫 · 等價 · 單值性 · h-層次 · 截斷

> **package** `axiom/axiom/hott_core` · **alias** `@hott_core` · **依賴**：無（只用 MoonBit 核心庫，是全庫的根）
> **檔案**：`hott_core.mbt`（192 行）· `core_test.mbt`（黑盒測試）· `moon.pkg`
> **公開 API**：29 項 = 9 個類型 + 20 個函數 · **本 package 引入的公理：0**

## 1. 呢個資料夾做乜

呢度係成個庫嘅**同倫類型論地基**：把「相等」由布爾判斷換成**路徑類型** `Path[A]`，
然後喺上面建起群胚結構（`refl` / `sym` / `trans`）、函數作用（`ap`）、沿類型族嘅
**傳輸**（`transport`）、**同倫**（`Homotopy`）、**半伴隨等價**（`Equiv`）、
**單值性映射**（`ua`）、**h-層次**（`HLevel`）同 **n-截斷**（`Trunc`）。

上面所有 package（`hott_hits`、`univalence`、`cubical`、`hott_redefine`、`hott_theorems`、
`hott_algorithms`）都只依賴呢一個 package 嘅定義，所以佢**唔可以依賴任何人**——
`moon.pkg` 嘅 `import` 係空嘅，依賴圖嘅根。

零成本設計：`Path[A]` 只係 `{ lhs, rhs, code }` 三個欄位，所有路徑運算單態化成
整數 `code` 嘅加法／取反，運行時 O(1)；`TypeTag(String)`、`IsProp` 呢類見證型別
喺具體化之後會被常量傳播消除。

## 2. 公理

**無。** 呢個 package 冇任何 `axiom` 宣告，`ua` 喺呢度係一個**有計算內容嘅函數**
（`code = equiv_defect(e)`），唔係憑空假定：

| 項目 | 狀態 |
|---|---|
| 單值性 `ua : Equiv[A,B] → Path[TypeTag](A,B)` | **定義**（可計算），定律喺 `univalence/` 窮盡驗證 |
| 路徑群胚定律（refl/sym/trans 嘅單位、逆、結合） | 由 `code` 算術直接計算；窮盡驗證見 `univalence/` 與 `core_test.mbt` |
| `transport` / `ap` 嘅計算律 | 定義即計算律（`ap` 保持 `code`，`transport` 把 `code` 加上去） |

> **誠實邊界**：MoonBit 唔係證明助理。`Path[A]` 嘅兩個端點 `lhs`/`rhs` **唔會被型別檢查器驗證**
> （`trans(p,q)` 喺運行時唔檢查 `p.rhs == q.lhs`）。所以本庫嘅「定理」= **有限模型內嘅窮盡可執行驗證**
> ＋ **書面嚴格推導**（見 `docs/UNIVALENCE.md`、`docs/CUBICAL.md`），唔係機器檢查嘅形式證明。
> 呢個限制喺每一個 README 都會重申。

## 3. 定義（類型）

| 名稱 | 數學內容 | 實作 |
|---|---|---|
| `Path[A]` | 路徑類型 $Path_A(x,y)$：相等即路徑 | `pub(all) struct { lhs : A; rhs : A; code : Int }`；`code` = 組合編碼（`0` = refl，±n = 合成深度） |
| `Homotopy[A, B]` | 同倫 $f \sim g \coloneqq \Pi(x:A)\,Path_B(fx,gx)$ | `{ fun1, fun2, witness : Array[(A, Path[B])] }`（採樣點見證） |
| `Equiv[A, B]` | 半伴隨等價 $A \simeq B$：$\exists g,\ \eta : g\circ f \sim id,\ \varepsilon : f\circ g \sim id$ | `{ to, from, left_inv_code, right_inv_code }` |
| `TypeTag` | 類型嘅**名稱**（宇宙 $U$ 嘅有限替身） | `pub(all) struct TypeTag(String)` |
| `UnivalenceWitness[A, B]` | 單值性等價 $(A = B) \simeq (A \simeq B)$ 嘅雙向見證 | 由 `univalence_witness` 構造 |
| `HLevel` | h-層次：$-2$ 可縮 / $-1$ 命題 / $0$ 集合 / $1$ 群胚 / $2$ 2-群胚 / $n\ge3$ | `enum { Contr, Prop, SetLevel, GroupoidLevel, TwoGroupoidLevel, NType(Int) }` |
| `IsContr[A]` | $\mathsf{isContr}(A) \coloneqq \Sigma(c:A)\,\Pi(x:A)\,Path_A(c,x)$ | 見證結構 |
| `IsProp[A]` | $\mathsf{isProp}(A) \coloneqq \Pi(x,y:A)\,Path_A(x,y)$（所有路徑唯一） | 見證結構 |
| `Trunc[A]` | n-截斷 $\Vert A \Vert_n$，左伴隨於 n-類型嘅包含 | `{ level : HLevel; val : A; trunc_code : Int }` |

## 4. 定義（運算與構造子）

| 名稱 | 型別／語義 | 計算內容 |
|---|---|---|
| `refl(a)` | $refl : Path_A(a,a)$ | `code = 0` |
| `sym(p)` | $p^{-1} : Path_A(y,x)$ | 端點對調，`code = -p.code` |
| `trans(p, q)` | $p \cdot q : Path_A(x,z)$ | `code = p.code + q.code + 1`（合成深度 +1；**端點銜接唔做運行時檢查**） |
| `ap(f, p)` | $ap_f : Path_A(x,y) \to Path_B(fx,fy)$ | 端點過 `f`，`code` 不變 |
| `transport(p, family_code, val_code)` | $transport^P(p,u) : P\,y$ | 以 `val_code + p.code` 模擬類型族嘅 code 變化 |
| `homotopy_refl(f)` | $f \sim f$ | `witness = []`（逐點皆 refl） |
| `Equiv::make(to, from)` | 由兩個方向構造等價 | 兩個逆見證碼設為 `0`（**待驗證**，見 `is_equiv`） |
| `Equiv::is_equiv()` | 判定是否真等價 | 兩個虧損碼皆為 `0` |
| `equiv_defect(e)` | 等價嘅**虧損碼** $= \vert\eta\vert + \vert\varepsilon\vert$ | `left_inv_code + right_inv_code` 嘅絕對值和 |
| `id_to_equiv(p, to, from)` | $\mathsf{idToEquiv} : (A = B) \to (A \simeq B)$ | 由路徑 + 兩個方向組成等價 |
| `ua(e, tagA, tagB)` | 單值性 $\mathsf{ua} : (A \simeq B) \to (A =_{U} B)$ | `code = equiv_defect(e)`：**已驗證等價 ⇒ 0（原子路徑）**；假等價會留下非零 code 可被偵測 |
| `hlevel_up(l)` | h-層次嘅後繼 $n \mapsto n+1$ | `Contr→Prop→SetLevel→GroupoidLevel→TwoGroupoidLevel→NType(3)` |
| `trunc_make(a, level)` | $\Vert a \Vert_n$ | `trunc_code = level_to_int(level)` |
| `is_truncated(t, level)` | 判定截斷層次 | `t.level == level` |
| `prop_trunc(a)` | 命題截斷 $\Vert A \Vert_{-1}$ | `level = Prop` |
| `set_trunc(a)` | 集合截斷 $\Vert A \Vert_0$ | `level = SetLevel` |
| `trunc_rec(level, f)` | 截斷消除：若 $B$ 為 n-類型則 $(\Vert A\Vert_n \to B) \simeq (A \to B)$ | 回傳 `Trunc[A] -> B` 嘅函數 |
| `univalence_witness(tagA, tagB, to, from)` | 構造 $(A=B) \simeq (A \simeq B)$ 嘅雙向見證 | 見 §5 |

## 5. 定理

| 名稱 | 陳述 | 驗證方式 |
|---|---|---|
| `ua_eta_legacy(to, from, tag)` | **uaη**：$\mathsf{ua}(\mathsf{idToEquiv}(refl_A)) = refl_A$（結構相等） | 直接斷言兩邊 `code` 皆 0；`core_test.mbt` 覆蓋 |
| `is_set_from_prop(_prop_paths)` | $\mathsf{isProp}(Path_A(x,y)) \Rightarrow \mathsf{isSet}(A)$ | 命題層次嘅推論（回傳 `true`；書面推導見 `docs/UNIVALENCE.md` §3） |
| `univalence_witness(...)` | 單值性等價 $(A=B) \simeq (A \simeq B)$ 有可計算嘅雙向見證 | **完整窮盡證明在 `univalence/`**：`univalence_proof(card)` 對 `Fin card` 驗證十條定律，`univalence_axiom_count() = 0` |

> `ua` 本身喺呢度只係**定義**；「佢係等價」呢條定理（`isEquiv(idToEquiv)`）
> 由 `univalence/hott_univalence_theorem.mbt` 對 $n = 0..6$ 窮盡驗證
> （$n=6$：1,571,761 次檢查，2.5 秒）。

## 6. 可運行例子

以下每個 ```mbt check``` 區塊都會被 `moon test` **真的編譯並執行**（唔係只係展示）。

```mbt check
test "README: 路徑群胚運算 code 語義" {
  let p = @hott_core.refl(42) // refl ⇒ code 0
  assert_eq(p.lhs, 42)
  assert_eq(p.rhs, 42)
  assert_eq(p.code, 0)
  // sym 把 code 取反、端點對調
  let s = @hott_core.sym(p)
  assert_eq(s.code, 0)
  // trans 每次合成 +1（所以 refl·refl⁻¹ 的深度是 1，不是 0）
  let t = @hott_core.trans(p, s)
  assert_eq(t.code, 1)
  assert_eq(@hott_core.trans(t, p).code, 2)
}
```

```mbt check
test "README: ap 保持 code，transport 把 code 加上去" {
  let p = @hott_core.refl(3)
  let doubled = @hott_core.ap(fn(x : Int) -> Int { x * 2 }, p)
  assert_eq(doubled.lhs, 6)
  assert_eq(doubled.code, 0) // ap 不改變組合深度
  // transport^P(p, u) 以 code 運算模擬：u + p.code
  let q : @hott_core.Path[Int] = { lhs: 0, rhs: 1, code: 5 }
  assert_eq(@hott_core.transport(q, fn(_ : Int) -> Int { 0 }, 7), 12)
}
```

```mbt check
test "README: 等價的虧損碼決定 ua 是否给出原子路徑" {
  let tagA = @hott_core.TypeTag("A")
  let tagB = @hott_core.TypeTag("B")
  let good = @hott_core.Equiv::make(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x })
  assert_true(good.is_equiv()) // 兩個逆見證碼皆 0
  assert_eq(@hott_core.equiv_defect(good), 0)
  assert_eq(@hott_core.ua(good, tagA, tagB).code, 0) // 已驗證等價 ⇒ 原子路徑
  // 「假等價」：逆見證碼非 0 ⇒ ua 的 code 非 0，可被偵測出來
  let bad : @hott_core.Equiv[Int, Int] = { to: fn(x) { x }, from: fn(x) { x }, left_inv_code: 3, right_inv_code: 4 }
  assert_true(!bad.is_equiv())
  assert_eq(@hott_core.equiv_defect(bad), 7)
  assert_eq(@hott_core.ua(bad, tagA, tagB).code, 7)
  // uaη：ua(idToEquiv(refl A)) 結構上就是 refl A
  assert_true(@hott_core.ua_eta_legacy(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x }, tagA))
}
```

```mbt check
test "README: h-層次與截斷" {
  assert_eq(@hott_core.hlevel_up(@hott_core.Prop), @hott_core.SetLevel)
  assert_eq(@hott_core.hlevel_up(@hott_core.SetLevel), @hott_core.GroupoidLevel)
  assert_eq(@hott_core.hlevel_up(@hott_core.TwoGroupoidLevel), @hott_core.NType(3))
  // ∥42∥₀ 是集合截斷；∥42∥₋₁ 是命題截斷
  let s = @hott_core.set_trunc(42)
  assert_eq(s.level, @hott_core.SetLevel)
  assert_eq(s.trunc_code, 0)
  assert_true(@hott_core.is_truncated(s, @hott_core.SetLevel))
  assert_true(!@hott_core.is_truncated(@hott_core.prop_trunc(42), @hott_core.SetLevel))
  // 截斷消除：對集合層級的目標，∥A∥₀ → B 就是 A → B
  let f = @hott_core.trunc_rec(@hott_core.SetLevel, fn(x : Int) -> Int { x + 1 })
  assert_eq(f(s), 43)
}
```

## 7. 測試

| 檔案 | 內容 |
|---|---|
| `core_test.mbt` | 黑盒測試：路徑運算（refl/sym/trans/ap 嘅 code 語義）、h-層次升降、截斷 |
| 本檔 §6 | 4 個 `mbt check` 文件測試，由 `moon test` 執行 |

```bash
moon test hott_core   # 或 moon test（全庫）
```

## 8. 去邊

- **`univalence/`** — 用 `Fin` / `Bij` / 帶 glue 嘅 `UPath` 把 `ua` 由定義升級成**已窮盡驗證嘅定理**
- **`hott_hits/`** — 用呢度嘅 `Path` 建高歸納類型（`Interval`、`Circle`、`Susp`、`Pushout`、`PropTrunc`、`Quotient`）
- **`hott_redefine/`** — 用 `HLevel` / `Trunc` 把 `structures/` 嘅代數結構逐項 HoTT 化
- **`docs/UNIVALENCE.md`** — 單值性定理化嘅完整書面推導與實驗數據
