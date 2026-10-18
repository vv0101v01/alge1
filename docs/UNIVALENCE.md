# 單值性：從公理降級為定理 —— 完整證明報告

> 對應 commit：`HoTT重構` 之後的本次改動
> 程式碼：`hott_univalence_theorem.mbt`（新增）、`hott_core.mbt`、`hott_univalence.mbt`（改造）
> 機器檢查：`univalence_theorem_test.mbt`（13 個新測試）
> 工具鏈：`moon 0.1.20261012` / `moonc v0.10.15`（與 `docs/toolchain.txt` 一致）
> 結果：**`moon test` → Total tests: 39, passed: 39, failed: 0**（原 26 + 新 13）

---

## 0. 結論摘要

| 項目 | 結果 |
|---|---|
| repo 裡有沒有「單值性公理」？ | **有**。全庫唯一被標為公理的就是單值性（univalence）：`README.mbt.md` §5 寫「**公理**：idToEquiv … 為等價；ua … 為其逆」，`hott_core.mbt::ua` 的註解寫「HoTT **公理**的計算內容」 |
| 有沒有別的公理？ | 沒有被標為公理的陳述。`hott_redefine.mbt` 提到「路徑公理」（refl/sym/trans），那是類型論的推斷規則，本庫已用 `Path` 實作，不是額外假設 |
| 已降級為定理？ | **是**。`ua` 不再是宣告：它由等價自身的資料**構造**（glue），公理數 = 0（`univalence_axiom_count() = 0`） |
| 定理成立嗎？ | **成立**，三種獨立意義下（見 §3、§4、§5）：一般 cubical 定理、本庫模型內的構造性證明、`n = 0..6` 的窮盡機器驗證（n=6 做了 1,571,761 次原子比較） |
| 附帶修好的 bug | 舊 `ua` 連自己的定律都不滿足：`ua(idEquiv) ≠ refl`（違反 uaη）、`transport (ua e) ≠ e.to`（違反 uaβ，`transport_structure` 會憑空 +10） |

---

## 1. 診斷：它憑什麼是「公理」

舊實作（`hott_core.mbt`）：

```moonbit
/// 單值性見證：將等價提升為類型相等（HoTT 公理的計算內容）
pub fn[A, B] ua(e : Equiv[A, B], tagA : TypeTag, tagB : TypeTag) -> Path[TypeTag] {
  { lhs: tagA, rhs: tagB, code: e.left_inv_code + e.right_inv_code + 10 }
}
```

三個問題，每個都足以讓它只能當公理：

1. **常數 `10` 沒有來源。** 路徑的 `code` 是「合成深度」（`refl = 0`、`trans` 加 1、`sym` 取反）。`ua(e)` 憑空得到 10，等於宣告了一條無法由任何規則導出的路徑 —— 這就是公理的定義。
2. **它違反自己的定律。**
   * uaη 要求 `ua(idEquiv_A) = refl_A`。舊碼給出 `code = 0 + 0 + 10 = 10 ≠ 0`，所以 `ua(idEquiv) ≠ refl`。
   * uaβ 要求 `transport (ua e) x = e.to x`。經 `cubical_transport`（code 加法）得 `x + 10`，多了一個虛構的位移；`transport_structure(idEquiv, A, A, 5)` 回傳 **15**，正確答案應是 **5**。
3. **前提本身未被驗證。** `Equiv::make(to, from)` 一律把 `left_inv_code`/`right_inv_code` 設成 0，`is_equiv()` 因此恆真：從來沒檢查過 `from ∘ to = id`。在一條未驗證的「等價」上宣告單值性，等於公理疊在壞前提上。

---

## 2. 定理陳述

**單值性（Univalence）。** 設 `U` 為宇宙。典範映射

```
idToEquiv : (A =_U B) → (A ≃ B)
```

是**等價**；其擬逆記為 `ua : (A ≃ B) → (A =_U B)`。等價地：`isEquiv(idToEquiv)`，
見證資料為 `(ua, η, ε, coherence)`：

```
uaη  : Π(p : A =_U B),  ua (idToEquiv p) = p
uaε  : Π(e : A ≃ B),    idToEquiv (ua e) = e
uaβ  : Π(e : A ≃ B)(x), transport (ua e) x ≡ e x        （計算律）
tri  : 兩個三角恆等式（半伴隨等價的相干性）
```

本庫證明的是它在**有限宇宙**上的實例（`U_fin` = 所有 `Fin n`）：

> **定理 A（主定理）。** 對每個 `n ≥ 0`，`idToEquiv : (Fin n =_U Fin m) → (Fin n ≃ Fin m)`
> 是等價，擬逆為 `ua`；且 `Fin n =_U Fin m` 非空 ⟺ `n = m`。
>
> **定理 A′（推論）。** `π₁(U_fin, Fin n) ≅ S_n`，故 `|Fin n =_U Fin n| = n! = |Fin n ≃ Fin n|`。
>
> **定理 B（三條推論，同樣由計算證明，不再是 `-> Bool { true }`）。**
> (B1) 有限函數外延性 `funext`/`happly` 互逆；
> (B2) 命題外延性 `(P ⇔ Q) ⟺ (P = Q)`；
> (B3) SIP 結構同一性：同構的有限么半群在單值宇宙中相等（沿 `ua(σ)` 傳輸後結構逐項相符）。

---

## 3. 證明 (A)：一般情形 —— 為什麼單值性在 cubical 類型論中是定理

書式 HoTT（HoTT Book, 2013）把 `ua` 當公理，因為基於 J/refl 的同一性類型對宇宙**沒有計算內容**：`transport` 沿一條「宇宙路徑」作用時無法歸約，只能假設。

一旦把同一性類型改成**原始路徑**（區間 `I` 的函數）並給宇宙一個 **glue/fill** 構造，`ua` 就變成可定義的，而且 uaβ 成為**定義性等價**：

* **CCHM 2016**（Cohen–Coquand–Huber–Mörtberg, *Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom*）：以 Kan 填充實現 `transport`，`Glue` 型別讓 `transport (ua e) x ≡ e x` 定義性成立；`isEquiv(idToEquiv)` 由方塊填充（box filling）證明。
* **Orton–Pitts 2016**：在 cubical sets 的建構性 topos 中給出模型，單值性在該模型內是**定理**。
* **Angiuli 2019**（cartesian cubical TT）：對 Kan 型別的宇宙證明單值性。

共同要點只有三條，也是本庫 L2 層照搬的結構：
1. 路徑是有計算內容的物件（不是不透明 token）；
2. `transport` 是消除規則，沿 glue 路徑作用時**直接歸約**成被 glue 的等價；
3. `ua` 只是「把已驗證的等價裝回路徑的 glue 欄位」——一個**定義**，不需要新假設。

於是 uaβ 是定義性的，uaη/uaε 退化為「拆開再裝回去」的同一性，三角恆等式隨之成立。

---

## 4. 證明 (B)：本庫模型內的構造性證明（逐步對應程式碼）

### 4.1 模型

| 數學物件 | 程式碼 | 說明 |
|---|---|---|
| 有限類型 `Fin n` | `Fin { tag : TypeTag, card : Int }` | `card` 是它在宇宙中的完整結構碼 |
| 元素 | `i ∈ [0, n)` | `Int` |
| 等價 `Fin n ≃ Fin m` | `Bij { card, fwd, bwd }` | **只有通過驗證才能構造**（見 4.2 引理 0） |
| 宇宙路徑 `A =_U B` | `UPath { lhs, rhs, glue }` | 帶 glue ⇒ 有計算內容 |
| `transport` | `upath_transport p i = p.glue.fwd[i]` | glue 消除規則（定義） |
| `refl / sym / trans` | `upath_refl / upath_sym / upath_trans` | 恆等 / 逆 / 複合置換 |
| 路徑相等 | `upath_eq` | 可判定（tag、card、置換逐點） |
| `idToEquiv` | `id_to_equiv_fin` | 由 **transport** 定義，非讀欄位 |
| `ua` | `ua_fin` | 把已驗證等價裝回 glue |

**引理 0（等價的驗證 = 可判定檢查）。** `bij_make(card, fwd)` 依序檢查：長度 = `card`、值域 ⊆ `[0,card)`、單射（逆表無撞車）、滿射（逆表無 `-1`），最後由 `bij_make_with_inv` 逐點驗證 `bwd ∘ fwd = id` 與 `fwd ∘ bwd = id`。任一項失敗即回傳 `None`。
⇒ **每個 `Bij` 都是已被證明為雙射的映射**；`ua` 的定義域不含未驗證物件。∎
（測試 `U5` 驗證 `[0,0,1]`（非單射）與 `[0,1,3]`（越界）都被拒絕。）

**引理 1（`Bij` 成群 = `S_n`）。** 封閉性：`bij_compose(g,f)` 複合後**重新驗證**兩個三角恆等式；單位元 `bij_id`（由 `bij_make` 驗證）；逆元 `bij_inv`（對稱地滿足同樣的恆等式）；結合律來自函數複合。∎

**引理 2（`UPath` 成群胚，且路徑類型是集合）。** `refl/sym/trans` 用引理 1 的群運算，端點條件由 `upath_make`/`upath_trans` 檢查（`p.rhs ≠ q.lhs` 時回傳 `None`）。`upath_eq` 是可判定相等 ⇒ 每條路徑類型是集合（0-類型）⇒ `U_fin` 是 **1-類型**，`π₂(U_fin) = 0`，沒有高階結構需要额外相干性。∎（`decidable_eq`、`fin_universe_hlevel`）

**引理 3（`idToEquiv` 良定且落在已驗證等價上）。**
`id_to_equiv_fin p` 的前向表由 `fwd[i] ≔ transport p i` 定義，逆向表由 `bwd[j] ≔ transport (sym p) j` 定義，再交給 `bij_make_with_inv` 驗證。
因為 `transport p = p.glue.fwd`、`transport (sym p) = p.glue.bwd`（定義），驗證恰好通過 ⇒ 結果是合法 `Bij`。∎
**注意**：「結果等於 glue」在此是**推論**，不是假設 —— 程式碼走的是 transport，不是欄位讀取。

**引理 4（`ua` 良定）。** 給定已驗證的 `e : Fin n ≃ Fin m`，雙射存在 ⇒ `n = m`（有限集合基數不變量）；`upath_make` 據此檢查 `card` 一致，不一致回傳 `None`。一致時 `ua e ≔ UPath{a, b, e}` 滿足不變量，故是合法路徑。∎
（推論：`n ≠ m` 時 `Fin n =_U Fin m` 為空 —— `upath_all(Fin2, Fin3).length() = 0`，測試 `U6`。）

**引理 5（uaη）。** `ua (idToEquiv p) = p`。
證：由引理 3，`idToEquiv p` 的 `fwd/bwd` 逐點等於 `p.glue.fwd/bwd`，故 `bij_eq` 成立；`ua` 保留端點 `p.lhs/p.rhs`；`upath_eq` 逐欄位相等 ⇒ 相等。∎（`pf.eta`）

**引理 6（uaε）。** `idToEquiv (ua e) = e`。
證：`transport (ua e) i = e.fwd[i]`（定義），`transport (sym (ua e)) j = e.bwd[j]`；再驗證 ⇒ 恰為 `e`。∎（`pf.eps`）

**引理 7（uaβ，計算律）。** `transport (ua e) x ≡ e x`，且是**定義性**的：`upath_transport` 就是 `bij_apply(p.glue, ·)`，而 `ua e` 的 glue 就是 `e`。∎（`pf.beta`、`upath_transport_beta(card)`）

**引理 8（群胚函子性）。** `ua(idEquiv) = refl`；`ua(e⁻¹) = sym(ua e)`；`ua(g ∘ f) = trans (ua f) (ua g)`。
證：三式兩邊都是同一個 `UPath`（glue 分別為 `id`、`e⁻¹`、`g∘f`），由引理 1 的群運算定義直接相等。∎（`refl_law`/`sym_law`/`trans_law`）

**引理 9（`ua` 是雙射）。**
單射：`ua e₁ = ua e₂` ⇒ glue 相同 ⇒ `e₁ = e₂`（`upath_eq` 逐點比較置換）。
滿射：給任意路徑 `p`，取 `e = idToEquiv p`，則 `ua e = p`（引理 5）。∎（`ua_injective`/`ua_surjective`）

**引理 10（三角恆等式 / 相干性）。**
`idToEquiv (ua (idToEquiv p)) = idToEquiv p`（引理 6 代入 `e = idToEquiv p`）；
`ua (idToEquiv (ua e)) = ua e`（引理 5 代入 `p = ua e`）。
因為路徑類型是集合（引理 2），半伴隨等價所需的相干性自動成立。∎（`pf.triangle`）

### 4.2 定理 A 的證明

由引理 3、4，`idToEquiv` 與 `ua` 是互為定義域/値域的良定映射；由引理 5、6 它們互逆；由引理 10 滿足三角恆等式。故 `isEquiv(idToEquiv)`，即

```
(Fin n =_U Fin m)  ≃  (Fin n ≃ Fin m)                                    ∎
```

程式碼入口：`is_equiv_id_to_equiv(card)` / `univalence_holds(card)`。

### 4.3 定理 A′ 的證明

引理 8 說明 `ua` 保 `refl/sym/trans`，引理 9 說明它是雙射，故它是群同構
`π₁(U_fin, Fin n) ≅ Aut(Fin n) = S_n`；兩邊基數皆為 `n!`（`count_law`：`path_count = equiv_count = factorial(n)`）。∎
程式碼入口：`pi1_universe_is_symmetric_group(card)`。

### 4.4 定理 B 的證明

**B1 函數外延性。** 有限函數就是函數表 `Array[Int]`。`funext_defect(f,g)` = 逐點不同的個數，`funext_fin` 的路徑 `code` = 該虧損。
(1) 健全性+完備性：`code = 0 ⟺ f,g 逐點相等`；
(2) `happly ∘ funext = id`：對真路徑逐點 `happly` 再重組，得到同一條路徑；
(3) `funext ∘ happly = id`。
三條在**全部** `(nⁿ)²` 對函數上窮盡驗證：`n=1:1`、`n=2:16`、`n=3:729`、`n=4:65536` 對（`funext_happly_laws`）。
∎ ⇒ `funext_happly_is_equiv()` 不再回傳寫死的 `true`，而是這四組窮盡檢查的合取。

**B2 命題外延性。** 有限宇宙中命題就是基數 ≤ 1 的類型（空型 `0`、單點型 `1`）。映射存在性：`P → Q` 有映射 ⟺ (`P = 0` 或 `Q ≥ 1`)。逐一檢查 4 種 `(P,Q)` 組合得 `(P ⇔ Q) ⟺ (card P = card Q)`，即 `(P ⇔ Q) ⟺ (P = Q)`（`prop_ext_fin_exhaustive`）。∎

**B3 SIP（結構同一性）。** 設 `m₁, m₂` 為 `Fin n` 上的么半群（乘法表 + 單位元，且已通過 `monoid_check` 的 `2n + n³` 條公理窮盡驗證）。若存在 `σ ∈ S_n` 使 `σ(m₁(i,j)) = m₂(σi, σj)`（全 `n²` 對）且 `σ(u₁) = u₂`（`monoid_isomorphism` 窮盡搜索），則：
1. 由定理 A，`ua(σ) : Fin n =_U Fin n`，載體相等；
2. 沿 `ua(σ)` 傳輸 `m₁` 的結構：`(σ·m₁)(i,j) = σ(m₁(σ⁻¹i, σ⁻¹j))`（`upath_transport_table`），由同構條件**逐項等於** `m₂(i,j)`，單位元映到 `u₂`；
3. 故 `m₁` 與 `m₂` 在單值宇宙中是**同一個**么半群結構（`sip_transport_check`）。∎

**外部交叉驗證（獨立於本庫的已知結果）：** 用 SIP 分類器算出的數字與公開文獻完全吻合 ——

| n | 已標號么半群數（本庫計算） | OEIS A058153 | 同構類數（本庫計算） | OEIS A058129 |
|---|---|---|---|---|
| 1 | 1 | 1 | 1 | 1 |
| 2 | 4 | 4 | 2 | 2 |
| 3 | 33 | 33 | **7** | **7** |

（`monoid_all(n).length()`、`monoid_classes(n)`；測試 `C3` 把這些數字寫成斷言。）

---

## 5. 證明 (C)：可執行窮盡驗證（機器檢查）

`univalence_proof(card)` 對給定基數**窮盡**枚舉全部路徑與全部等價，逐條計算十項定律；
沒有任何欄位是寫死的 `true`，全部由比較得出。實測輸出（`moon run cmd/main`）：

```
--- 單值性：公理 → 定理（零公理，窮盡驗證）---
univalence_thm: axioms=0 n3(paths=6/6 checks=193) n4(paths=24/24 checks=2137) holds=true
                pi1_S3=true ua_beta=true funext=true prop_ext=true sip_classes=7
摘要（每行一個基數；holds=true 即定理成立）:
n=0 paths=1=1   equivs=1   ηεβ=true inj/surj=true grp=true tri=true checks=9       holds=true
n=1 paths=1=1   equivs=1   ηεβ=true inj/surj=true grp=true tri=true checks=12      holds=true
n=2 paths=2=2   equivs=2   ηεβ=true inj/surj=true grp=true tri=true checks=35      holds=true
n=3 paths=6=6   equivs=6   ηεβ=true inj/surj=true grp=true tri=true checks=193     holds=true
n=4 paths=24=24 equivs=24  ηεβ=true inj/surj=true grp=true tri=true checks=2137    holds=true
n=5 paths=120=120 equivs=120 ηεβ=true inj/surj=true grp=true tri=true checks=45601 holds=true
n=6 paths=720=720 equivs=720 …                                              checks=1571761 holds=true
```

十項被窮盡驗證的定律（`UnivalenceProof` 的欄位）：

| # | 欄位 | 內容 | 對應引理 |
|---|---|---|---|
| T1 | `count_law` | `|Fin n = Fin n| = n! = |Fin n ≃ Fin n|` | A′ |
| T2 | `eta` | uaη：`ua(idToEquiv p) = p` | 引理 5 |
| T3 | `eps` | uaε：`idToEquiv(ua e) = e` | 引理 6 |
| T4 | `beta` | uaβ：`transport (ua e) x = e x` | 引理 7 |
| T5 | `ua_injective` | 不同等價 ⇒ 不同路徑 | 引理 9 |
| T6 | `ua_surjective` | 每條路徑都是某等價的 `ua`（顯式搜索） | 引理 9 |
| T7 | `refl_law`/`sym_law`/`trans_law` | 群胚函子性 | 引理 8 |
| T8 | `triangle` | 兩個三角恆等式（相干性） | 引理 10 |
| T9 | `decidable_eq` | 路徑相等可判定 + 反身完備 ⇒ 1-類型 | 引理 2 |
| T10 | `shadow_injective` | Lehmer 影子投影單射（`S_n → [0,n!)` 雙射） | §6 |

### 5.1 測試清單（`univalence_theorem_test.mbt`，13 個）

| 測試 | 內容 |
|---|---|
| `U0` | 公理審計：`univalence_axiom_count() = 0` |
| `U1` | 主定理：`n = 0..5` 十項定律全部窮盡成立 + `is_equiv_id_to_equiv(n)` |
| `U2` | `n = 6`：720 條路徑、`checks > 1,500,000`、`holds` |
| `U3` | `π₁(U_fin, Fin n) ≅ S_n`（`n = 0..5`） |
| `U4` | Lehmer 影子：`S_n → [0,n!)` 為雙射（`n = 1..4` 逐值檢查）、`refl ↦ code 0` |
| `U5` | 具體置換 `σ=(0 1 2)` 上的 uaβ/η/ε/sym/trans；非雙射輸入被 `bij_make` 拒絕 |
| `U6` | 不等價 ⇒ 不相等（`|Fin2 = Fin3| = 0`）；同基數不同名 ⇒ 仍有路徑（單值性要點） |
| `C1` | 函數外延性：`n = 1..4` 窮盡 `(nⁿ)²` 對（含 65536 對）+ 虧損碼語義 |
| `C2` | 命題外延性：4 種組合窮盡 |
| `C3` | SIP：么半群計數 1/4/33 與同構類 1/2/7（對照 OEIS）+ 分類正確性 |
| `C4` | uaβ 窮盡（`n=4,5`）+ 舊 API 的 uaη；假等價的虧損碼可被檢測 |
| `C5` | 有限宇宙是 1-類型（`fin_universe_hlevel = GroupoidLevel`） |
| `U7` | demo 字串：`axioms=0`、`holds=true`、`sip_classes=7`、摘要行可讀 |

另外 `axiom_test.mbt` 的 `hott: equiv and ua` 已從「斷言魔術數字 10」改為「斷言定律」
（`code = equiv_defect(e) = 0`、uaη、uaβ、假等價虧損 = 7）。

### 5.2 重現步驟

```bash
curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
export PATH="$HOME/.moon/bin:$PATH"
moon version --all     # moon 0.1.20261012 / moonc v0.10.15
moon check             # 0 errors
moon test              # Total tests: 39, passed: 39, failed: 0   （約 4.2 秒）
moon run cmd/main      # 印出上面的定理摘要
```

---

## 6. 舊 API 的接軌（零成本影子投影）

舊的 `Path[TypeTag]` 只有一個 `Int` code，裝不下置換，所以：

* `ua(e, tagA, tagB)`（舊簽名保留）現在回傳 `code = equiv_defect(e) = left_inv_code + right_inv_code`：
  已驗證等價 ⇒ `0` ⇒ 原子路徑，且 `ua(idEquiv)` 結構上就是 `refl`（uaη 成立，`ua_eta_legacy` 可斷言）。
* 帶完整內容的版本是 `ua_fin : Bij → UPath?`；`upath_to_legacy : UPath → Path[TypeTag]`
  用 **Lehmer 碼** `code = Σᵢ Lᵢ·(n−1−i)!`（`Lᵢ = #{ j>i | σⱼ < σᵢ }`）把置換單射地編進 `[0, n!)`，
  因此影子投影在有限宇宙上是**單射**且 `refl ↦ 0`（T10 窮盡驗證）。

### 行為變更（API 相容，數值語義修正）

| 呼叫 | 舊值 | 新值 | 原因 |
|---|---|---|---|
| `ua(Equiv::make(id,id), A, B).code` | `10` | `0` | 常數 10 是憑空宣告；0 才能滿足 uaη |
| `transport_structure(idEquiv, A, A, 5)` | `15` | `5` | uaβ：傳輸應等於 `e.to` |
| `funext(h).code` | `h.witness.length()` | `homotopy_defect(h)` | code 應是「未驗證虧損」，不是見證條數 |
| `sip_monoid(e, m1, m2).code` | `30` | `equiv_defect(e) + monoid_str_defect(m1,m2)` | 30 是捏造的；不同結構不該拿到合法相等見證 |
| `prop_ext(...).code` | `20` | `equiv_defect(equiv)` | 同上 |
| demo `hott:` 行 | `ua_code=10` | `ua_code=0` | 反映上述修正 |
| demo `new_thms:` 行 | `sip_code=30` | `sip_code=1` | demo 的兩個 `MonoidStr` 載體名不同 ⇒ 虧損 1（可檢測，非 0 即非合法見證） |

新增公開 API（約 35 項，全在 `hott_univalence_theorem.mbt`）：
`Fin`/`fin`、`Bij`/`bij_make`/`bij_make_with_inv`/`bij_id`/`bij_apply`/`bij_inv`/`bij_compose`/`bij_eq`/`bij_is_id`/`bij_all`/`lehmer_code`、
`UPath`/`upath_make`/`upath_refl`/`upath_sym`/`upath_trans`/`upath_eq`/`upath_transport`/`upath_transport_table`/`upath_all`/`upath_to_legacy`、
`id_to_equiv_fin`/`ua_fin`/`upath_transport_beta`、`UnivalenceProof`/`univalence_proof`/`univalence_holds`/`is_equiv_id_to_equiv`/`pi1_universe_is_symmetric_group`/`inequivalent_types_are_unequal`/`univalence_axiom_count`/`univalence_line`/`univalence_summary`、
`all_functions`/`funext_defect`/`funext_fin`/`happly_fin`/`funext_happly_laws`、`is_prop_fin`/`fin_map_exists`/`prop_ext_fin_exhaustive`、
`MonoidFin`/`monoid_table_at`/`monoid_check`/`monoid_all`/`monoid_isomorphism`/`sip_monoid_fin`/`sip_transport_check`/`monoid_classes`/`monoid_partition_check`；
`hott_core.mbt` 新增 `equiv_defect`、`ua_eta_legacy`；`hott_univalence.mbt` 新增 `homotopy_defect`、`monoid_str_defect`、`transport_via_ua`、`prop_ext_is_theorem`、`sip_is_theorem`、`ua_beta_is_theorem`、`fin_universe_hlevel`；`axiom.mbt` 新增 `univalence_theorem_demo`。

---

## 7. 誠實聲明：這個「證明」的邊界

1. **MoonBit 不是證明助手。** `Path[A]` 的端點在型別層面不受檢查，定律不會被編譯器強制。
   所以 §5 的機器檢查是**模型內的窮盡驗證**（對有限模型的 decision procedure），不是 type-theoretic derivation。
   它證明的是：「在這個語義明確、相等可判定的有限宇宙模型裡，定理的每一條定律對全部輸入成立」。
2. **範圍是有限宇宙實例。** 全宇宙的單值性在 cubical 類型論中是定理（§3 的文獻），
   但要在本庫機械化需要一個真正的 cubical 檢查器（區間 + Kan 填充），這超出 MoonBit 的型別系統。
   本庫做到的是：把「宣告」換成「構造 + 可判定驗證」，並讓舊 API 至少不再違反 uaη/uaβ。
   **後續進展**：有限立方體演算法已實作（`hott_cubical.mbt`、報告 `docs/CUBICAL.md`）——
   K1 立方體範疇 □（∂/σ、三組恆等式、計數律、生成律，dim ≤ 4）、
   K2 **Kan 填充**（在本文的 `El` 纖維上解開放盒，七條定律含 uaβ，card ≤ 5）、
   K3 **cubical NBE**（`CTerm` + 重寫 R1–R12 + 勢函數終止性）。
   它仍是**有限模型**上的檢查器（不是型別層的 cubical 檢查器），但 §4 的 glue 構造
   現在有了對應的填充演算法與重寫系統，uaβ 由「布林檢查」升級為「可執行的化簡」。
3. **複雜度。** 窮盡驗證是 `O((n!)²·n)`：`n=5` 約 4.6 萬次比較，`n=6` 約 157 萬次（整套測試約 4.2 秒）。
   `n=7`（5040）不建議放進 CI。SIP 的窮盡分類受 `n^(n²)` 張表限制，只跑到 `n = 3`（19683 張表）。
4. **`Equiv[A,B]` 的舊 `is_equiv()` 仍然是弱檢查**（只看兩個 code）。真正的等價驗證在 `Bij`/`bij_make`。
   若要徹底肅清，下一步是把 `Equiv` 的見證欄位換成 `Homotopy` 並強制檢查 —— 已列入 §8 待辦。

---

## 8. 後續可做（不影響本次結論）

* 把 `Equiv[A,B]` 的 `left_inv_code/right_inv_code : Int` 升級為真正的同倫見證並強制驗證，讓舊 API 的 `is_equiv()` 不再恆真。
* 用 `UPath` 取代 `hott_redefine.mbt::vect_hott_path` 的 `code: v1.dim - v2.dim`（目前 `VectHoTT` 的相等見證同樣是捏造的）。
* 把 SIP 分類推到 `n = 4`（35 類）：需要剪枝（先固定單位元、先篩冪等元）而非枚舉 `4^16` 張表。
* ~~做一個 cubical 檢查器（區間 + Kan 填充）~~ —— **已完成**：`hott_cubical.mbt` 的 K1（立方體範疇 □）、
  K2（Kan 填充 = transport，含 uaβ 作為化簡結果）、K3（cubical NBE + 強正規化），報告見 `docs/CUBICAL.md`。
  仍待做的是它的高維推廣：多方向 `hcomp`、依賴路徑 `PathP`、`Glue` 型別形成子、connections（見該文 §8）。
* 若要真正的型別層證明，把本庫的 `UPath`/`Bij` 移植到 Agda/Lean 4（cubical 或 `Equiv` + `univalence`），本文的引理 0–10 可逐條對應。

---

## 附錄：術語對照

| 中文 | 英文 | 程式碼 |
|---|---|---|
| 單值性（公理 → 定理） | univalence | `ua_fin` / `univalence_proof` |
| 宇宙 | universe | `Fin` / `U_fin` |
| 等價 | equivalence | `Bij`（已驗證雙射） |
| 路徑 / 傳輸 | path / transport | `UPath` / `upath_transport` |
| glue 構造 | Glue (cubical) | `UPath.glue` |
| 計算律 uaβ | computation rule | `upath_transport_beta` |
| 三角恆等式 | triangle identities | `UnivalenceProof.triangle` |
| 結構同一性原理 | SIP (structure identity principle) | `sip_monoid_fin` / `sip_transport_check` |
| 函數外延性 | function extensionality | `funext_fin` / `happly_fin` |
| 命題外延性 | propositional extensionality | `prop_ext_fin_exhaustive` |
| h-層次 | h-level | `HLevel` / `fin_universe_hlevel` |

**參考文獻**
1. The HoTT Book (2013), Ch. 2.5 / Ch. 4 — 單值性作為公理的原始表述。
2. Cohen, Coquand, Huber, Mörtberg, *Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom* (2016) — glue/Kan 填充使 `ua` 可計算。
3. Orton, Pitts, *Univalence Axiom in Constructive Set Theory / Cubical Sets model* (2016)。
4. Angiuli, *Constructive Homotopy Type Theory* (2019) — cartesian cubical 中對 Kan 型別宇宙證明單值性。
5. Sterling, Angiuli, Gratzer, *Cubical Syntax for Reflection-Free Extensional Equality* (2019)。
6. OEIS A058129（同構類數 1, 2, 7, 35, 228, …）、A058153（已標號數 1, 4, 33, 624, …）— §4.4 的交叉驗證。
