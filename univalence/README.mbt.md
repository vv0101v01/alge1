# `univalence` — 單值性：由**公理**降級為**定理**（窮盡可執行證明）+ 三大推論 funext / prop-ext / SIP

> **package** `axiom/axiom/univalence` · **alias** `@univalence` · **依賴**：`@hott_core`
> **檔案**：`hott_univalence_theorem.mbt`（1023 行，主證明）· `hott_univalence.mbt`（106 行，推論）· `univalence_test.mbt`（黑盒測試 14 個）· `moon.pkg`
> **公開 API**：68 項 = 6 個類型 + 62 個函數 · **本 package 引入的公理：0**（`univalence_axiom_count() = 0`）

## 1. 呢個資料夾做乜

原庫把**單值性**（univalence，`ua : (A ≃ B) → (A =_U B)`）當成**公理**：舊實作憑空
加咗一個常數 `10` 做路徑 code，即係「假定佢成立」。呢個 package 做三件事：

1. **重建宇宙**：`Fin`（有限類型，帶基數）· `Bij`（已驗證嘅等價 $A \simeq B$，兩個三角
   恆等式逐點檢查）· `UPath`（宇宙路徑 $A =_U B$，**帶計算內容 `glue`**，唔再係空殼）。
2. **把 `ua` 變成定義**：`ua_fin(e, a, b)` 由已驗證嘅 `Bij` 直接構造 `UPath`；
   `id_to_equiv_fin(p)` 由 `glue` 還原等價。兩者都係可計算函數。
3. **窮盡驗證定理**：`univalence_proof(card)` 對 `Fin card` 嘅**全部** $n!$ 個等價同
   **全部**路徑逐條驗證 12 條定律（基數律、uaη、uaε、uaβ、單射、滿射、refl/sym/trans
   律、三角恆等式、相等可判定、影子單射），回傳一個 `UnivalenceProof` 物件——
   **每個欄位都係計算出嚟嘅，冇一個 `true` 字面值**。

然後用呢條定理推出三個經典推論：**函數外延性 funext**、**命題外延性 prop-ext**、
**結構同一性原理 SIP**（同構嘅結構相等），同樣用窮盡計算驗證。

完整書面推導、實驗數據同參考文獻見 **`docs/UNIVALENCE.md`**。

## 2. 公理

**無。** 呢個 package 嘅公理審計函數就係證據：

```mbt check
test "README: 單值性部分的公理數恆為 0" {
  assert_eq(@univalence.univalence_axiom_count(), 0)
}
```

| 項目 | 舊狀態（上游 `ca01d32`） | 現狀態 |
|---|---|---|
| `ua : (A ≃ B) → (A =_U B)` | **公理**：路徑 code 憑空 `+10` | **定義** `ua_fin`：由已驗證 `Bij` 構造，`upath_make` 會檢查基數相符 |
| `idToEquiv : (A =_U B) → (A ≃ B)` | 無 | **定義** `id_to_equiv_fin`：由 `glue` 還原 |
| `isEquiv(idToEquiv)` | 假定 | **定理** `is_equiv_id_to_equiv(card)`：擬逆 = `ua_fin` + 兩個三角恆等式，窮盡驗證 |
| uaβ（`transport (ua e) x = e x`） | 無 | **定理** `upath_transport_beta(card)` / `ua_beta_is_theorem(card)` |

> **誠實邊界**：MoonBit 唔係證明助理。`UPath` 嘅兩個端點 `lhs`/`rhs`（`Fin` 值）**唔會**被
> 型別檢查器驗證同 `glue` 嘅定義域一致——呢層一致性由 `upath_make` 喺**運行時**檢查
> （基數不符就回傳 `None`）。所以我哋嘅「定理」= **有限宇宙內嘅窮盡可執行驗證**
> （$n \le 6$，共 1,571,761 次原子比較）+ `docs/UNIVALENCE.md` 嘅書面嚴格推導，
> **唔係**機器檢查嘅形式證明。要真正嘅形式證明請用 Agda/CubicalTT（`--cubical`）、
> Coq（HoTT 庫）、Lean（`lean-lang` 嘅 univalence 需 cubical 基礎）。

## 3. 定義（類型）

| 名稱 | 數學內容 | 實作（欄位） |
|---|---|---|
| `Fin` | 宇宙 $U_{fin}$ 中嘅有限類型；`card` 係完整結構碼（基數） | `{ tag : @hott_core.TypeTag; card : Int32 }` |
| `Bij` | 等價 $A \simeq B$（card 相同時即 $Fin\ n \simeq Fin\ n$ 嘅自等價 = 對稱群 $S_n$） | `{ card : Int32; fwd : Array[Int32]; bwd : Array[Int32] }`，兩個方向嘅三角恆等式在構造時逐點驗證 |
| `UPath` | 宇宙路徑 $A =_U B$。**帶計算內容（`glue`）**，同舊嘅空殼 `Path[TypeTag]` 唔同 | `{ lhs : Fin; rhs : Fin; glue : Bij }` |
| `UnivalenceProof` | 定理嘅**證明物件**：12 條定律 + 3 個計數 + 檢查次數 | 見 §5 表格；`checks` = 執行過嘅原子比較次數（窮盡程度嘅見證） |
| `MonoidStr` | SIP 用嘅么半群**結構**（符號版） | `{ carrier : TypeTag; op : String; unit : String }` |
| `MonoidFin` | SIP 用嘅**有限**么半群：載體 `Fin n` + 單位元 + $n^2$ 乘法表 | `{ carrier : Fin; unit : Int32; table : Array[Int32] }`（`table[i*n+j]`） |

## 4. 定義（函數）

### 4.1 宇宙與等價（`Fin` / `Bij`）

| 名稱 | 語義 | 計算內容 |
|---|---|---|
| `fin(name, card)` | 構造 $Fin\ card$ | `{ tag: TypeTag(name), card }` |
| `factorial(n)` | $n!$ | 迭代乘法（`Int32`） |
| `bij_make_with_inv(card, fwd, bwd)` | 由前向表 + 逆向表構造等價 | **兩個三角恆等式都逐點驗證**，失敗回 `None` |
| `bij_make(card, fwd)` | 只給前向表 | 先檢查單射與值域 → 算逆 → 再驗證兩個三角恆等式 |
| `bij_id(card)` | 恆等等價 $id : Fin\ n \simeq Fin\ n$ | `fwd = bwd = [0..n-1]` |
| `bij_apply(b, i)` / `bij_inv(b, i)` | $\sigma(i)$ / $\sigma^{-1}(i)$ | 查表 |
| `bij_compose(g, f)` | $g \circ f$（先 f 後 g） | 結果再經 `bij_make_with_inv` 驗證一次 |
| `bij_eq(a, b)` | 外延相等（`Array` 冇 `Eq`，故手寫） | 逐點比較；同時係「等價類型係集合」嘅判定程序 |
| `bij_is_id(b)` | 是否恆等 | 逐點比對 |
| `lehmer_code(b)` | Lehmer 碼 $= \Sigma_i L_i \cdot (n-1-i)!$，$L_i = \#\{j>i \mid \sigma_j < \sigma_i\}$ | $S_n \to \{0..n!-1\}$ 嘅雙射（影子忠實性用） |
| `bij_all(card)` | **窮盡枚舉** $Fin\ card \simeq Fin\ card$ 全部元素（即 $S_{card}$） | 全排列 + 逐個驗證 |

### 4.2 宇宙路徑（`UPath`）

| 名稱 | 語義 | 計算內容 |
|---|---|---|
| `upath_make(a, b, glue)` | 構造 $a =_U b$ | **運行時檢查** `a.card == glue.card == b.card`，否則 `None` |
| `upath_refl(a)` | $refl_a$ | `glue = bij_id` |
| `upath_sym(p)` | $p^{-1}$ | `glue` 換成逆向表 |
| `upath_trans(p, q)` | $p \cdot q$ | `glue` 複合（再驗證一次） |
| `upath_eq(p, q)` | 路徑相等**可判定** | 比對端點 + `bij_eq(glue)`；⇒ `Fin` 宇宙係 1-類型（$\pi_2 = 0$） |
| `upath_transport(p, i)` | **transport**：沿宇宙路徑搬元素 | `bij_apply(glue, i)` |
| `upath_transport_table(p, table)` | 傳輸一張 $n$ 元運算表 | $(\sigma\cdot m)(i,j) = \sigma(m(\sigma^{-1}i, \sigma^{-1}j))$ |
| `upath_all(a, b)` | **窮盡枚舉** $a =_U b$ 全部路徑 | card 唔同則為空——呢個正係「不等價即不相等」 |
| `upath_to_legacy(p)` | **零成本影子**：投影回舊 API 嘅 `Path[TypeTag]` | `code = lehmer_code(glue)` |

### 4.3 單值性映射與定理

| 名稱 | 語義 |
|---|---|
| `id_to_equiv_fin(p)` | $\mathsf{idToEquiv} : (A =_U B) \to (A \simeq B)$ — **定義**（取 `glue`） |
| `ua_fin(e, a, b)` | $\mathsf{ua} : (A \simeq B) \to (A =_U B)$ — **定義**（原公理） |
| `upath_transport_beta(card)` | **uaβ** 嘅窮盡證明：$transport\ (ua\ e)\ x \equiv e\ x$ 對全部 `e`、全部 `x` |
| `univalence_proof(card)` | 對 `Fin card` 窮盡驗證**每一條**定律，回傳 `UnivalenceProof` |
| `is_equiv_id_to_equiv(card)` | 定理嘅**正式陳述**：`isEquiv(idToEquiv)`（擬逆 `ua` + 兩個三角恆等式） |
| `univalence_holds(card)` | 定理成立 ⟺ 全部定律都被窮盡計算驗證 |
| `univalence_axiom_count()` | **公理審計**：恆為 `0` |
| `univalence_line(pf)` / `univalence_summary(max_card)` | 給 demo / README / docs 用嘅一行／多行摘要 |

### 4.4 推論 API（`hott_univalence.mbt`）

| 名稱 | 語義 | 計算內容 |
|---|---|---|
| `funext(h)` | 函數外延性 $(f \sim g) \to (f = g)$（由單值性 + 區間可得） | 路徑 `code = homotopy_defect(h)` |
| `homotopy_defect(h)` | 同倫嘅虧損碼：`0` ⟺ 所有逐點見證都係 refl | 累加見證 `code` |
| `happly(p, x)` | $(f = g) \to (f\,x = g\,x)$ | 路徑在點 `x` 上作用 |
| `funext_happly_is_equiv()` | `funext` 與 `happly` 互逆嘅見證 | 委託 `funext_happly_laws` |
| `prop_ext(p_is_prop, q_is_prop, equiv)` | 命題外延性 $(P \Leftrightarrow Q) \to (P = Q)$（$P,Q$ 命題時） | `Path[TypeTag]("P","Q")`，`code = equiv_defect(equiv)`；**兩個 `IsProp` 見證被 `ignore`**（命題性由 `is_prop_fin` 另行判定） |
| `prop_ext_is_theorem()` | 命題外延性嘅可執行證明 | 有限宇宙中 Prop 就係基數 ≤1 嘅類型（空型／單點型） |
| `MonoidStr` 三件套 | `monoid_str_defect(m1,m2)`（載體／運算／單位元三項中不符嘅個數）· `sip_monoid(e,m1,m2)`（路徑 `code = 載體等價虧損 + 結構表虧損`）· `sip_is_theorem(card)` | SIP 嘅符號版 |
| `ua_beta(e, tagA, tagB, x)` | 單值性計算律 uaβ 嘅見證 | `transport along ua(e)` 等於 `e.to x` |
| `transport_via_ua(p, e, x)` | **glue 消除規則** $transport^{\lambda\_.B}(ua\ e, x) \coloneqq e.to\ x$ | 直接套用 `e.to` |
| `ua_beta_is_theorem(card)` | uaβ 嘅可執行證明 | 對全部 `e : Fin n ≃ Fin n`、全部 `x` 窮盡驗證 |
| `hlevel_preserved_by_univalence(l)` | 單值性保持 h-層次（h-level 係命題値不變量） | 恆等 `l`（呢條陳述嘅內容就係「不變」） |
| `fin_universe_hlevel(card)` | 有限宇宙嘅 h-層次 | **佔位**：`ignore(card)`，恆回 `GroupoidLevel`（結論由 `univalence_proof` 嘅 `decidable_eq` + `ua_injective` 支持，但呢個函數本身唔按 card 計算） |

### 4.5 推論嘅窮盡驗證器

| 名稱 | 內容 |
|---|---|
| `pi1_universe_is_symmetric_group(card)` | $\pi_1(U_{fin}, Fin\ n) \cong S_n$：單射 + 滿射 + 基數 $n!$ + 複合相容 |
| `inequivalent_types_are_unequal(n, m)` | 不等價嘅有限類型不相等（$Fin\ n = Fin\ m$ 為空當 $n \ne m$） |
| `all_functions(card)` | 窮盡枚舉 $Fin\ card \to Fin\ card$ 全部函數表（$card^{card}$ 個） |
| `funext_defect(f, g)` | 逐點虧損：`0` ⟺ 兩函數表逐點相等 |
| `funext_fin(f, g)` | 有限函數外延性：逐點相等嘅驗證**就係**路徑 |
| `happly_fin(p, x)` | `happly` 嘅有限版 |
| `funext_happly_laws(card)` | 窮盡驗證 `funext`/`happly` 互逆（全部 $card^{card} \times card^{card}$ 對函數） |
| `is_prop_fin(a)` | 有限宇宙中嘅命題 = 基數 ≤1 嘅類型 |
| `fin_map_exists(p, q)` | $P \to Q$ 有映射 ⟺（$P$ 為空 或 $Q$ 非空） |
| `prop_ext_fin_exhaustive()` | 窮盡驗證：對全部命題對 $(P,Q)$，$(P \Leftrightarrow Q) \Leftrightarrow (P = Q)$ |
| `monoid_table_at(m, i, j)` | 讀乘法表 |
| `monoid_check(m)` | 驗證么半群公理：單位元（$2n$ 條）+ 結合律（$n^3$ 條），全部窮盡 |
| `monoid_all(card)` | 窮盡枚舉 $Fin\ card$ 上全部**已驗證**嘅么半群結構（從 $card^{card^2}$ 張表篩出） |
| `monoid_isomorphism(m1, m2)` | 搜索同構 $\sigma$：$\sigma(m_1(i,j)) = m_2(\sigma i, \sigma j)$ 且 $\sigma(u_1) = u_2$（窮盡 $n!\cdot n^2$） |
| `sip_monoid_fin(m1, m2)` | **SIP 定理（有限版）**：同構嘅么半群喺單值宇宙中相等，路徑由 `ua` 給出 |
| `sip_transport_check(m1, m2)` | SIP 嘅**計算內容**：把 $m_1$ 嘅乘法表沿 $ua(\sigma)$ 傳輸後**逐項等於** $m_2$ 嘅表 |
| `monoid_classes(card)` | 用 SIP 路徑把全部有限么半群分成同構類，回傳類數 |
| `monoid_partition_check(card)` | 驗證「同構 ⟺ 同一類」（雙向：同類必同構、同構必同類） |

## 5. 定理

### 5.1 主定理：單值性等價 $(A =_U B) \simeq (A \simeq B)$

`univalence_proof(card)` 回傳嘅 `UnivalenceProof` 有 12 條定律欄位，**全部由計算得出**：

| 欄位 | 定律 |
|---|---|
| `count_law` | **基數律**：$\vert Fin\ n = Fin\ n\vert = n! = \vert Fin\ n \simeq Fin\ n\vert$（`path_count` / `equiv_count` / `expected`） |
| `eta` | **uaη**：$\Pi(p : A = B),\ ua(\mathsf{idToEquiv}\ p) = p$ |
| `eps` | **uaε**：$\Pi(e : A \simeq B),\ \mathsf{idToEquiv}(ua\ e) = e$ |
| `beta` | **uaβ**：$\Pi(e)(x),\ transport\ (ua\ e)\ x = e\ x$ |
| `ua_injective` | $ua$ 單射：唔同等價 ⇒ 唔同路徑 |
| `ua_surjective` | $ua$ 滿射：每條路徑都係某個等價嘅 $ua$ |
| `refl_law` | 群胚函子性：$ua(id_{Equiv}) = refl$ |
| `sym_law` | $ua(e^{-1}) = sym(ua\ e)$ |
| `trans_law` | $ua(g \circ f) = trans\ (ua\ f)\ (ua\ g)$ |
| `triangle` | 三角恆等式（半伴隨等價嘅相干性）⇒ `isEquiv(idToEquiv)` |
| `decidable_eq` | 路徑相等可判定且反身完備 ⇒ `Fin` 宇宙係 **1-類型**（$\pi_2 = 0$） |
| `shadow_injective` | 影子投影 `upath_to_legacy` 喺有限宇宙上單射（Lehmer 碼忠實） |

### 5.2 推論

| 推論 | 判準 | 內容 |
|---|---|---|
| $\pi_1(U_{fin}, Fin\ n) \cong S_n$ | `pi1_universe_is_symmetric_group(card)` | 單射 + 滿射 + 基數 $n!$ + 複合相容 |
| 不等價 ⇒ 不相等 | `inequivalent_types_are_unequal(n, m)` | $Fin\ n = Fin\ m$ 為空當 $n \ne m$（$n = m$ 時短路回 `true`，只驗證 $n \ne m$ 嘅情形） |
| $U_{fin}$ 嘅 h-層次 | `fin_universe_hlevel(card)` | $card \ge 2$ ⇒ 1-類型（群胚層次） |
| **funext** | `funext_happly_laws(card)` · `funext_happly_is_equiv()` | $(f \sim g) \simeq (f = g)$ |
| **prop-ext** | `prop_ext_fin_exhaustive()` · `prop_ext_is_theorem()` | $(P \Leftrightarrow Q) \Leftrightarrow (P = Q)$ |
| **SIP** | `sip_is_theorem(card)` · `sip_transport_check` · `monoid_partition_check(card)` | 同構嘅結構相等（沿 $ua(\sigma)$ 傳輸後逐項相等） |
| **uaβ** | `ua_beta_is_theorem(card)` · `upath_transport_beta(card)` | glue 消除規則 |
| h-層次不變量 | `hlevel_preserved_by_univalence(l)` | 沿等價傳輸不變 |

## 6. 可運行例子

以下 ```mbt check``` 區塊由 `moon test` **真的編譯並執行**（成本已控制：`card ≤ 4`）。

```mbt check
test "README §4.1: 有限宇宙與已驗證等價 Bij" {
  let a = @univalence.fin("A", 3)
  assert_eq(a.card, 3)
  assert_eq(@univalence.factorial(3), 6)
  // 3-循環 (0 1 2)：bij_make 會檢查單射、值域，再算逆、再驗證兩個三角恆等式
  let sigma = @univalence.bij_make(3, [1, 2, 0])
  assert_true(sigma is Some(_))
  let s = sigma.unwrap()
  assert_eq(@univalence.bij_apply(s, 0), 1)
  assert_eq(@univalence.bij_apply(s, 1), 2)
  assert_eq(@univalence.bij_apply(s, 2), 0)
  // bij_inv 回傳的是「逆向等價」本身（一個 Bij），不是元素
  let si = @univalence.bij_inv(s)
  assert_eq(@univalence.bij_apply(si, 0), 2) // σ⁻¹(0) = 2
  assert_true(@univalence.bij_eq(@univalence.bij_compose(s, si), @univalence.bij_id(3)))
  assert_true(!@univalence.bij_is_id(s))
  // 非法表（不是雙射）⇒ None，不會被當成等價
  assert_true(@univalence.bij_make(3, [0, 0, 0]) is None) // 常數表不是雙射
  // 窮盡枚舉 S₃：6 個元素，Lehmer 碼是 [0,6) 的双射
  let all = @univalence.bij_all(3)
  assert_eq(all.length(), 6)
  let codes : Array[Int] = []
  for b in all { codes.push(@univalence.lehmer_code(b)) }
  assert_eq(codes.length(), 6)
  // 複合與外延相等
  let id3 = @univalence.bij_id(3)
  assert_true(@univalence.bij_eq(@univalence.bij_compose(id3, s), s))
}
```

```mbt check
test "README §4.2: UPath 帶 glue — transport 就是查 glue 表" {
  let a = @univalence.fin("A", 3)
  let b = @univalence.fin("B", 3)
  let s = @univalence.bij_make(3, [1, 2, 0]).unwrap()
  let p = @univalence.ua_fin(s, a, b).unwrap() // ua：等價 ⇒ 宇宙路徑
  assert_eq(p.lhs.card, 3)
  assert_eq(p.rhs.tag, @hott_core.TypeTag("B"))
  // transport 沿 p 把元素搬過去：1 ↦ σ(1) = 2
  assert_eq(@univalence.upath_transport(p, 1), 2)
  assert_eq(@univalence.upath_transport(p, 2), 0)
  // 群胚運算
  let r = @univalence.upath_refl(a)
  assert_true(@univalence.upath_eq(@univalence.upath_trans(r, r).unwrap(), r))
  // p · p⁻¹ = refl_a（glue 複合成恆等）
  assert_true(@univalence.upath_eq(@univalence.upath_trans(p, @univalence.upath_sym(p)).unwrap(), r))
  // 端點基數不同 ⇒ 沒有路徑（「不等價即不相等」）
  assert_eq(@univalence.upath_all(a, @univalence.fin("C", 4)).length(), 0)
  // 窮盡枚舉 a =_U b：|UPath| = 3! = 6
  assert_eq(@univalence.upath_all(a, b).length(), 6)
  // idToEquiv 還原 glue（roundtrip）
  assert_true(@univalence.bij_eq(@univalence.id_to_equiv_fin(p), s))
  // 零成本影子：投影回舊 API 的 Path[TypeTag]，code = Lehmer 碼
  let shadow = @univalence.upath_to_legacy(p)
  assert_eq(shadow.code, @univalence.lehmer_code(s))
  assert_eq(shadow.lhs, @hott_core.TypeTag("A"))
}
```

```mbt check
test "README §5.1: 主定理 — 12 條定律全部由窮盡計算驗證" {
  let pf = @univalence.univalence_proof(3)
  assert_eq(pf.card, 3)
  // 基數律：|Fin 3 = Fin 3| = 3! = 6 = |Fin 3 ≃ Fin 3|
  assert_eq(pf.path_count, 6)
  assert_eq(pf.equiv_count, 6)
  assert_eq(pf.expected, 6)
  assert_true(pf.count_law)
  assert_true(pf.eta)
  assert_true(pf.eps)
  assert_true(pf.beta)
  assert_true(pf.ua_injective)
  assert_true(pf.ua_surjective)
  assert_true(pf.refl_law)
  assert_true(pf.sym_law)
  assert_true(pf.trans_law)
  assert_true(pf.triangle) // ⇒ isEquiv(idToEquiv)
  assert_true(pf.decidable_eq) // ⇒ Fin 宇宙是 1-類型
  assert_true(pf.shadow_injective)
  assert_true(pf.checks > 0) // 窮盡程度的見證
  // 定理的正式陳述與總結判準
  assert_true(@univalence.is_equiv_id_to_equiv(3))
  assert_true(@univalence.univalence_holds(3))
  assert_true(@univalence.univalence_summary(3).contains("n=3 paths=6=6 equivs=6"))
}
```

```mbt check
test "README §5.2: 推論 π₁(U_fin) ≅ S_n 與「不等價即不相等」" {
  assert_true(@univalence.pi1_universe_is_symmetric_group(3))
  assert_true(@univalence.pi1_universe_is_symmetric_group(4))
  // n ≠ m ⇒ Fin n =_U Fin m 為空（upath_all 回傳空陣列）
  assert_true(@univalence.inequivalent_types_are_unequal(2, 3))
  assert_true(@univalence.inequivalent_types_are_unequal(0, 5))
  // 注意實作細節：n = m 時直接回 true（同基數時路徑存在，此函數只驗證 n≠m 的情形）
  assert_true(@univalence.inequivalent_types_are_unequal(3, 3))
  // 「等價 ⇒ 有路徑」的真正證據是 |a =_U b| = n!
  assert_eq(@univalence.upath_all(@univalence.fin("X", 3), @univalence.fin("Y", 3)).length(), 6)
  // 有限宇宙的 h-層次：card ≥ 2 ⇒ 1-類型（群胚）
  assert_eq(@univalence.fin_universe_hlevel(3), @hott_core.GroupoidLevel)
  assert_eq(@univalence.hlevel_preserved_by_univalence(@hott_core.GroupoidLevel), @hott_core.GroupoidLevel)
}
```

```mbt check
test "README: 推論 funext — 函數外延性" {
  assert_true(@univalence.funext_happly_is_equiv())
  assert_true(@univalence.funext_happly_laws(3)) // 窮盡 3³ × 3³ 對函數
  // funext：同倫 ⇒ 路徑；happly：路徑 ⇒ 逐點路徑
  let f = fn(x : Int) -> Int { x + 1 }
  let h : @hott_core.Homotopy[Int, Int] = { fun1: f, fun2: f, witness: [] }
  assert_eq(@univalence.homotopy_defect(h), 0) // 逐點皆 refl
  let p = @univalence.funext(h)
  assert_eq(p.code, 0)
  assert_eq(@univalence.happly(p, 5).code, 0)
  // 虧損非 0 的同倫 ⇒ 不是路徑
  let w : @hott_core.Path[Int] = { lhs: 2, rhs: 3, code: 4 } // 一個「非 refl」的見證
  let bad : @hott_core.Homotopy[Int, Int] = { fun1: f, fun2: f, witness: [(1, w)] }
  // homotopy_defect 數的是「見證碼非 0 的採樣點個數」，不是碼的總和
  assert_eq(@univalence.homotopy_defect(bad), 1)
  assert_eq(@univalence.funext(bad).code, 1)
}
```

```mbt check
test "README: 推論 prop-ext — 命題外延性" {
  assert_true(@univalence.prop_ext_is_theorem())
  assert_true(@univalence.prop_ext_fin_exhaustive()) // 對全部命題對 (P,Q) 窮盡
  // 有限宇宙中的命題 = 基數 ≤ 1 的類型
  assert_true(@univalence.is_prop_fin(@univalence.fin("Empty", 0)))
  assert_true(@univalence.is_prop_fin(@univalence.fin("Unit", 1)))
  assert_true(!@univalence.is_prop_fin(@univalence.fin("Bool", 2)))
  // P → Q 有映射 ⟺ (P 為空 或 Q 非空)
  assert_true(@univalence.fin_map_exists(@univalence.fin("Empty", 0), @univalence.fin("Unit", 1)))
  assert_true(!@univalence.fin_map_exists(@univalence.fin("Unit", 1), @univalence.fin("Empty", 0)))
}
```

```mbt check
test "README: 推論 SIP — 同構的么半群相等（結構同一性原理）" {
  assert_true(@univalence.sip_is_theorem(3))
  // 窮盡枚舉 Fin 3 上全部已驗證的么半群結構
  let ms = @univalence.monoid_all(3)
  assert_true(ms.length() > 0)
  for m in ms { assert_true(@univalence.monoid_check(m)) } // 單位元 + 結合律
  // 單位元律：m(unit, i) = i
  for i in 0..=2 {
    assert_eq(@univalence.monoid_table_at(ms[0], ms[0].unit, i), i)
  }
  // 帶標籤的 3 元么半群共 33 個（OEIS A058153: 1, 4, 33）
  assert_eq(ms.length(), 33)
  // 同一結構 ⇒ SIP 路徑就是 refl
  let p = @univalence.sip_monoid_fin(ms[0], ms[0]).unwrap()
  assert_true(@univalence.upath_eq(p, @univalence.upath_refl(p.lhs)))
  // SIP 的計算內容：沿 ua(σ) 傳輸乘法表後逐項相等
  assert_true(@univalence.sip_transport_check(ms[0], ms[0]))
  // 分類：3 元載體上的么半群同構類 = 7（OEIS A058129: 1, 2, 7）
  assert_eq(@univalence.monoid_classes(3), 7)
  assert_true(@univalence.monoid_partition_check(3)) // 同構 ⟺ 同一類（雙向）
}
```

```mbt check
test "README: uaβ — glue 消除規則 transport (ua e) x = e x" {
  let tagA = @hott_core.TypeTag("A")
  let tagB = @hott_core.TypeTag("B")
  let e = @hott_core.Equiv::make(fn(x : Int) -> Int { x + 1 }, fn(x : Int) -> Int { x - 1 })
  // uaβ 的見證：lhs = transport along ua(e)，rhs = e.to x
  let beta = @univalence.ua_beta(e, tagA, tagB, 7)
  assert_eq(beta.lhs, 8)
  assert_eq(beta.rhs, 8)
  assert_eq(beta.code, 0)
  // glue 消除規則本身
  let p = @hott_core.ua(e, tagA, tagB)
  assert_eq(@univalence.transport_via_ua(p, e, 7), 8)
  // 窮盡驗證（有限宇宙版）
  assert_true(@univalence.ua_beta_is_theorem(3))
  assert_true(@univalence.upath_transport_beta(3))
  // 假等價（虧損 7）不會被當成合法路徑：code > 0 可被偵測
  let bad : @hott_core.Equiv[Int, Int] = { to: fn(x) { x }, from: fn(x) { x }, left_inv_code: 3, right_inv_code: 4 }
  assert_eq(@univalence.ua_beta(bad, tagA, tagB, 1).code, 7)
}
```

## 7. 實驗數據（$n = 0..6$，由 `univalence_summary(6)` 產生）

| $n$ | $\vert Fin\ n = Fin\ n\vert$ | $n!$ | $\vert Fin\ n \simeq Fin\ n\vert$ | 12 條定律 | 原子比較次數 |
|---|---|---|---|---|---|
| 0 | 1 | 1 | 1 | 全 true | 9 |
| 1 | 1 | 1 | 1 | 全 true | 12 |
| 2 | 2 | 2 | 2 | 全 true | 35 |
| 3 | 6 | 6 | 6 | 全 true | 193 |
| 4 | 24 | 24 | 24 | 全 true | 2,137 |
| 5 | 120 | 120 | 120 | 全 true | 45,601 |
| 6 | 720 | 720 | 720 | 全 true | 1,571,761（約 2.5 秒） |

其他已驗證數值：`pi1_universe_is_symmetric_group(0..5)` 全 true；$S_3$ 嘅 Lehmer 碼
（按 `bij_all(3)` 順序）= `[5,3,2,4,1,0]`；`funext_happly_laws(1..4)` 全 true；
么半群同構類數 `[1,2,7]` = **OEIS A058129**，帶標籤結構數 `[1,4,33]` = **OEIS A058153**；
`fin_universe_hlevel(3) = GroupoidLevel`。完整數據同推導見 `docs/UNIVALENCE.md`。

## 8. 測試

| 檔案 | 內容 |
|---|---|
| `univalence_test.mbt` | 14 個黑盒測試（U1–U6 + ua 定律）：`Fin`/`Bij` 驗證、`UPath` 群胚、`univalence_proof` 12 條定律、三大推論、uaβ |
| 本檔 §2 + §6 | 9 個 `mbt check` 文件測試，由 `moon test` 執行 |
| root `axiom_test.mbt` | U7：`univalence_theorem_demo()` 嘅輸出契約 |

```bash
moon test univalence   # 單 package
moon test              # 全庫
```

## 9. 去邊

- **`hott_core/`** — `Equiv` / `Path` / `TypeTag` / `ua`（舊 API）/ `HLevel`：呢度嘅定義基礎
- **`cubical/`** — K2 用 `UPath` 嘅 `glue` 做 Kan 填充；K3 用 `Bij` 嘅 Lehmer 碼做 `CTerm` 嘅 $\sigma$ 項
- **`hott_redefine/`** · **`hott_theorems/`** — SIP（N5）用 `univalence` 嘅路徑把「同構」升級成「相等」
- **`hott_algorithms/`** — H1 `cubical_transport_kan` / H6 `transport_structure` 直接用 `UPath`
- **`docs/UNIVALENCE.md`** — 公理 → 定理嘅完整故事：書面推導、成本分析、OEIS 交叉驗證、參考文獻
