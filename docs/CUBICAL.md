# 有限立方體演算法 —— 設計、推導與可執行驗證報告

> **對應程式碼**：`cubical/hott_cubical.mbt`（K1 立方體範疇 / K2 Kan 填充 / K3 cubical NBE）、
> `hott_algorithms/hott_algorithms.mbt`（H1、H7 的誠實化）、`cubical/cubical_test.mbt`（12 個測試）
> **命令**：`moon test cubical`（18 passed：12 黑盒 + 6 個 README 文件測試）· `moon test`（全庫 112 passed）· `moon run cmd/main`（`cubical:` 行）
> **本文寫成時**（commit `d28105a`）全庫係 51 passed / 101 warnings；之後做咗 **package 重構**
> （一個資料夾 = 一個 MoonBit package，每個 package 有自己的 `README.mbt.md` + 可運行例子），
> 程式碼與數學內容**完全冇變**，只係路徑由 `hott_cubical.mbt` 變成 `cubical/hott_cubical.mbt`。
> **公理數：0** —— 每一條布林值都由窮盡計算得出，沒有一欄寫死 `true`
> **前置閱讀**：`docs/UNIVALENCE.md`（單值性：公理 → 定理）。本文的 K2 就是該文 §8
> 「後續可做」第一項（cubical 檢查器：區間 + Kan 填充）的完成報告。

---

## 0. 結論摘要

| 部分 | 內容 | 驗證範圍 | 原子比較數 | 結果 |
|---|---|---|---|---|
| **K1** | 有限立方體範疇 □：態射=座標函數，生成元 ∂/σ，複合=代入 | dim ≤ 4（恆等式 dim ≤ 4、結合律 dim ≤ 2） | dim≤2: **11,367**；dim≤3: **93,767**；dim≤4: **4,172,976** | 9 條定律全 `true` |
| **K2** | Kan 填充 = transport：在單值性纖維 `El` 上解開放盒 | card ≤ 5（路徑數 = card! ≤ 120） | card=3: **198**；card=4: **2,880**；card=5: **76,200** | 7 條定律全 `true`（含 **uaβ**） |
| **K3** | cubical NBE：`CTerm` 項代數 + 重寫系統 R1–R12 + eval-then-reify | 7,615 個項（card ≤ 4, depth ≤ 2） | **30,732** + 3,158 + 2,995 | 11 條定律全 `true`（含**強正規化**） |

三句話版本：

1. **K1**：把「立方體」從口號變成物件 —— 一個有限的範疇，其態射是可枚舉的座標函數，
   三組 cubical 恆等式 C1/C2/C3、結合律/單位律、忠实性、**計數律**
   `|Hom([m],[n])| = Σ_k C(n,k)·C(m,k)·2^(n−k)`、**生成律**（每個態射都是 ∂/σ 的複合）
   全部窮盡驗證；順便算出 n-立方體的面格、`χ(Q^n)=1`、Gray 碼 Hamiltonian 圈。
2. **K2**：`transport` 在 cubical TT 中**就是 Kan 填充**。這裡真的去解開放盒：
   填充體存在、唯一（盒條件）、泛性質成立、傳輸是函子性的、round-trip 與 refl 律成立，
   而 **uaβ（`transport (ua e) x = e x`）是填充的計算結果，不是假設**。
3. **K3**：舊版 `normalize` 的 `code % 1000` 被換成真正的 NBE：項代數、求値、具體化、
   12 條重寫規則（帶**良型守衛**）、勢函數終止性證明，以及「判斷相等 = 範式相等」的
   健全性與完備性（相對有限模型）。

---

## 1. 診斷：舊版 H1 / H7 憑什麼不算 cubical

### 1.1 H1 `cubical_transport`

```moonbit
pub fn[A] cubical_transport(p : Path[A], val_code : Int) -> Int {
  // 真實 cubical 中為 Kan 填充，此處以 code 加法模擬 O(1)
  val_code + p.code
}
```

問題不在「加法很快」，而在 `Path[A]` **沒有計算內容**：它只有 `(lhs, rhs, code)`，
`code` 是合成深度計數器（`trans` 甚至寫成 `p.code + q.code + 1`）。沿著這種路徑
「傳輸」不可能算出任何東西 —— `v + p.code` 只是把深度加到數值上，與 `v` 的型別結構無關。
真正的 Kan 填充需要路徑**帶著 glue**（見 `UPath`），填充體由 glue 的消除規則給出。

### 1.2 H7 `normalize` / `judgmental_eq`

```moonbit
pub fn normalize(term : Term) -> Term {
  { code: term.code % 1000, tag: term.tag + "_nf" }   // 舊版
}
```

`Term` 只有 `(code : Int, tag : String)`，**沒有 λ、Π、ua、transport 等結構**，
因此根本沒有可歸一化的東西；而 `% 1000` 不只是「無意義」，它製造**假陽性**：

```
judgmental_eq(Term{1001,"t"}, Term{1,"t"})  舊版 = true   ← 1001 ≡ 1 (mod 1000)
                                            現在 = false
```

一個把不相等的項判成相等的「判定相等演算法」是負資產。修正方式有兩層：
(a) 誠實化 —— `normalize` 改為恒等、`judgmental_eq` 改為精確比對；
(b) 補上真正的演算法 —— K3 的 `CTerm`/`cnorm`/`judgmental_eq_ct`。

---

## 2. K1：有限立方體範疇 □

### 2.1 表示與約定

立方體範疇 □ 的物件是 `[n] = {0,1,…,n−1}`（`n` 個「區間方向」），態射由**座標函數**表示：

```moonbit
enum Coord { CZero; COne; CVar(Int) }              // 常數 0、常數 1、第 i 個投影
struct CubeMap { dom : Int; cod : Int; coords : Array[Coord] }   // coords.length() = cod
```

一個態射 `f : [dom] → [cod]` 就是 `cod` 個座標函數，每個是 `dom` 個輸入座標的投影或常數。
**複合 = 代入**（`cubemap_comp(g,f) = g ∘ f`，要求 `g.dom == f.cod`）：

```
(g ∘ f).coords[j] = subst(g.coords[j], f.coords)      // CVar(i) ↦ f.coords[i]
```

生成元（本庫的**索引約定**，見 §2.2 的說明）：

| 程式碼 | 數學記號 | 型別 | 座標 |
|---|---|---|---|
| `face_map(n,i,ε)` | `∂_{i,ε}` | `[n] → [n+1]` | `j<i: Var(j)`；`j=i: Const(ε)`；`j>i: Var(j−1)` |
| `degen_map(n,i)` | `σ_i` | `[n+1] → [n]` | `j<i: Var(j)`；`j≥i: Var(j+1)`（**忘掉**輸入座標 `i`） |
| `swap_map(n,i)` | `s_i` | `[n+1] → [n+1]` | 交換 `Var(i)`、`Var(i+1)`（cartesian 版本才有） |

即：`∂_{i,ε}` 在**輸出**的第 `i` 個位置插入常數 `ε`；`σ_i` 沿方向 `i` 把立方體拉成常數
（= 忽略那個輸入座標）。

**三層 cube 範疇**（`cubemap_is_ordered` / `cubemap_is_var_injective` 判別）：

| 層 | 條件 | 生成元 | 對應文獻 |
|---|---|---|---|
| 標準 □ | 出現的變數**嚴格遞增** | ∂, σ | Kan 的 cube category；CCHM 2016 的 coarse 版本 |
| cartesian □ | 變數**互不重複**（順序任意） | ∂, σ, s | Angiuli 2019 的 cartesian cubical |
| 最大 □ | 無限制（全部自然變換） | ∂, σ, s, connections | `(m+2)^n` 個態射 |

### 2.2 三組恆等式（含推導）

在本庫約定下（`∂_{i,ε}` 在輸出位置 `i` 插入常數），三組 cubical 關係是：

**(C1) coface–coface**：對 `0 ≤ i ≤ j ≤ d`、`ε,δ ∈ {0,1}`

```
∂_{j+1,δ} ∘ ∂_{i,ε}  =  ∂_{i,ε} ∘ ∂_{j,δ}          （兩者都是 [d] → [d+2]）
```

*推導*：`∂_{i,ε}` 把常數 `ε` 放在輸出位置 `i`；隨後 `∂_{j+1,δ}` 在位置 `j+1` 插入 `δ`，
因為 `j+1 > i`，第一個常數仍留在位置 `i`，第二個在 `j+1`。反向先插 `δ` 在位置 `j`
（`j ≥ i`，所以 `ε` 之後被推到 `i`，`δ` 落在 `j+1`）。兩邊都是「位置 `i` 放 `ε`、
位置 `j+1` 放 `δ`、其餘按序放變數」。

*手算例*（`d=1, i=0, j=1`）：兩邊都得 `[Const ε, Var0, Const δ] : [1] → [3]`。✔

> **約定警告**：教科書常寫成 `i<j` 時的 `∂_{j,δ}∂_{i,ε} = ∂_{i+1,ε}∂_{j,δ}`，那是
> 「`∂_{i,ε} : [n−1] → [n]` 且以** face 的維度**索引」的另一套約定。用錯約定會讓
> 恆等式在具體計算中直接失敗（本项目在實作時踩過：`d=1,i=0,j=1` 時兩邊分別是
> `[Var0,Const,Const]` 與 `[Const,Var0,Const]`）。**這裡的 C1 由窮盡計算背書**。

**(C2) codegeneracy–codegeneracy**：對 `0 ≤ i < j ≤ d+1`

```
σ_i ∘ σ_j  =  σ_{j−1} ∘ σ_i                        （兩者都是 [d+2] → [d]）
```

*推導*：`σ_j` 忘掉輸入座標 `j`，`σ_i`（`i<j`）忘掉座標 `i`；先忘大的再忘小的，
與先忘小的（此時大的索引往下挪一格 ⇒ `j−1`）再忘大的，結果都是「同時忘掉 `i` 與 `j`」。

*手算例*（`d=1, i=0, j=1`）：兩邊都得 `[Var2] : [3] → [1]`。✔

**(C3) codegeneracy–coface**：對 `0 ≤ i,j ≤ d`

```
             ⎧ ∂_{i,ε}   ∘ σ_{j−1}    若 i < j
σ_j ∘ ∂_{i,ε} = ⎨ id_[d]               若 i = j      （退化與面互相抵消）
             ⎩ ∂_{i−1,ε} ∘ σ_j        若 i > j
```

*推導*：`∂_{i,ε}` 在位置 `i` 放了常數；`σ_j` 要忘掉位置 `j`。
`i<j`：被忘掉的是常數之後的座標 ⇒ 常數仍在 `i`，但輸出維度少一 ⇒ 先 `σ_{j−1}` 再 `∂_{i,ε}`。
`i=j`：忘掉的正是那個常數 ⇒ 得到恒等。`i>j`：常數被往前推一格 ⇒ `∂_{i−1,ε}`。

*手算例*：`(d=1,i=0,j=0)` → `id`；`(d=1,i=1,j=0)` → `[Const ε]`；`(d=2,i=1,j=0)` → `[CZero, Var1]`。✔

程式碼：`cubical_proof(n)` 對 `d ≤ n` 的全部 `i,j,ε,δ` 組合逐一手算比對
（`cubemap_eq` 為結構比對，另有 `cubemap_eq_points` 的外延比對交叉驗證）。

### 2.3 忠实性與外延相等

`cubemap_apply(f, pt)` 把態射作用在頂點 `pt ∈ {0,1}^dom` 上。兩件事被窮盡驗證：

* **忠实性**：`(g∘f)(pt) = g(f(pt))` —— 結構複合（代入）與逐點複合一致 ⇒ 表示是忠实函子。
* **表示合法**：`cubemap_eq(f,g) ⟺ cubemap_eq_points(f,g)` —— 座標函數由其在
  `2^dom` 個頂點上的値完全決定（因為每個座標要嘛是常數、要嘛是某個投影）。

### 2.4 計數律（推導）

**定理**：`|Hom_□([m],[n])| = Σ_{k=0}^{min(m,n)} C(n,k)·C(m,k)·2^{n−k}`。

*證明*：一個標準態射由以下資料決定：
1. 選 `k` 個**輸出座標**放變數（其餘 `n−k` 個放常數）：`C(n,k)` 種；
2. 選 `k` 個**輸入變數**：`C(m,k)` 種；
3. 順序被「嚴格遞增」強制 ⇒ 只有 1 種排列方式；
4. 剩下 `n−k` 個常數座標各 2 種（0 或 1）：`2^{n−k}`。∎

同樣的推導在另外兩層給出：

| 層 | 公式 | 差別 |
|---|---|---|
| 標準 □ | `Σ_k C(n,k)·C(m,k)·2^{n−k}` | 變數嚴格遞增 ⇒ 排列數 1 |
| cartesian □ | `Σ_k C(n,k)·(m)_k·2^{n−k}` | 變數互異、順序任意 ⇒ 降階乘 `(m)_k` |
| 最大 □ | `(m+2)^n` | 每個輸出座標獨立選 `m` 個變數或 2 個常數 |

實測値（`cube_hom_count_*` 與 `cubemap_all_*` 的枚舉長度逐一比對）：

| `m\n` | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| **0** | 1/1/1 | 2/2/2 | 4/4/4 | 8/8/8 |
| **1** | 1/1/1 | 3/3/3 | 8/8/**9** | 20/20/**27** |
| **2** | 1/1/1 | 4/4/4 | 13/**14**/**16** | 38/**44**/**64** |
| **3** | 1/1/1 | 5/5/5 | 19/**22**/**25** | 63/**86**/**125** |

（每格為 `標準/cartesian/最大`。可見 `m ≤ 1` 時三層重合 —— 沒有足夠變數可交換；
從 `m=n=2` 起才分離：13 ⊂ 14 ⊂ 16。）

### 2.5 生成律：□ 由 ∂/σ 呈現

`cubemap_generated(dom,cod)` 從 `id_[dom]` 出發做 BFS：反覆**後複合**全部
`∂_{i,ε} : [c]→[c+1]` 與 `σ_i : [c+1]→[c]`，直到閉包收斂，再取出 `cod` 相符者。

**結果**：對 `dom, cod ≤ 4`，閉包恰好等於 `cubemap_all_standard`（例如 `(3,2)` 得 19 個、
`(2,2)` 得 13 個）。這就是「□ 由 face/degeneracy 生成」的可執行版本，也說明
`cubemap_all_with_swaps` 裡多出來的那一個態射（`(2,2)` 的第 14 個）確實需要 swap 生成元。

### 2.6 面格、Euler 特徵數、Gray 碼

* **k 維面數**：`cube_face_count(n,k) = C(n,k)·2^{n−k}`（固定 `n−k` 個座標、其餘自由）。
  `cube_faces_enum` **不套公式**地枚舉全部面（簽名陣列，`-1` = 自由座標），
  並驗證枚舉無重複且長度等於公式値：

  | n | k=0 | k=1 | k=2 | k=3 | k=4 | χ |
  |---|---|---|---|---|---|---|
  | 2 | 4 | 4 | 1 | – | – | 4−4+1 = **1** |
  | 3 | 8 | 12 | 6 | 1 | – | 8−12+6−1 = **1** |
  | 4 | 16 | 32 | 24 | 8 | 1 | 16−32+24−8+1 = **1** |

* **Euler 特徵數**：`χ(Q^n) = Σ_k (−1)^k C(n,k)2^{n−k} = (2−1)^n = 1`（二項式定理），
  即 n-立方體**可縮**（與 K2 的填充性質一致：可縮 ⇔ 每個盒都能填）。
* **Gray 碼 Hamiltonian 圈**：`g(k) = k ⊕ (k ≫ 1)`，`cube_points_gray(n)` 給出
  `2^n` 個互異頂點，相鄰（含首尾）恰差一位 ⇒ n-立方體圖的 Hamiltonian 圈
  （`gray_hamiltonian_check`，n ≤ 5 窮盡）。這是「立方體」作為**圖**的組合性質，
  與 §2.4 的「立方體」作為**範疇**的性質互為交叉驗證。

---

## 3. K2：Kan 填充（= transport）

### 3.1 模型

沿用 `docs/UNIVALENCE.md` 的有限宇宙：`Fin`（`tag` + `card`）、`Bij`（**已驗證**的雙射）、
`UPath{lhs, rhs, glue}`（帶計算內容的宇宙路徑）。類型族取單值性纖維

```
El : U_fin → Type        El(Fin n) = [0,n)
```

**開放盒**（open box）：

```moonbit
struct ElBox { path : UPath; bottom : Int; top : Int? }
//             ↑ 側面方向的路徑（glue）  ↑ 下邊 ∈ El(lhs)   ↑ 上邊（None = 缺失）
```

### 3.2 填充演算法與盒條件

```moonbit
pub fn kan_fill_el(box : ElBox) -> KanFill? {
  if box.bottom 越界 { return None }              // 盒不成立
  let filled = upath_transport(box.path, box.bottom)   // = bij_apply(glue, bottom)
  match box.top {
    Some(y) => if y == filled { Some({top: filled, compatible: true}) } else { None }
    None    => Some({top: filled, compatible: true})
  }
}
```

* 上邊**缺失** ⇒ 填充體由 glue 的消除規則給出，這就是 `transport`；
* 上邊**給定** ⇒ 只有 `top = transport path bottom` 時可填（**盒條件**），否則回傳 `None`
  （沒有填充體）。回傳 `None` 而不是「隨便填一個」是這個演算法的誠實之處。

### 3.3 七條定律（`kan_proof(card)`，全部窮盡）

| 定律 | 陳述 | 為什麼成立 |
|---|---|---|
| `exists` | 上邊缺失的盒恆有填充體 | glue 是**已驗證雙射** ⇒ 對每個 `x` 都有 `glue(x)` |
| `unique_iff` | 可填 `⟺ top = transport path bottom` | 填充體由 glue 唯一決定（函數是單値的） |
| `universal` | 填充體 = `upath_transport` = `bij_apply(glue, ·)` | 定義 unfolding（glue 消除規則） |
| `functorial` | `transport (q∘p) x = transport q (transport p x)`，且等於逐段填充 | 雙射複合的結合性：`(g∘f)(x) = g(f(x))` |
| `roundtrip` | `transport (sym p) (transport p x) = x` | `glue⁻¹(glue(x)) = x`（已驗證的左逆） |
| `refl_law` | `transport refl x = x` | `glue = id` |
| **`ua_beta`** | `transport (ua e) x = e x` | `ua e` 的 glue 就是 `e` 本身 ⇒ 填充即施用 |

`kan_compose(p,q,x)` 是「二維填充」的具體實作：先沿 `p` 填一次、再沿 `q` 填一次，
與直接沿 `q∘p` 填充比對 ⇒ 這就是 `functorial` 那一列的計算內容。

### 3.4 與單值性定理的接軌

`docs/UNIVALENCE.md` §4 用 glue 構造 `ua` 並驗證 uaβ；K2 把同一件事重新表述為
**Kan 填充**，並補上「盒條件」（唯一性）與「二維複合」（函子性）這兩條以前沒驗的性質。
換句話說：單值性定理的計算內容 = Kan 填充的存在唯一性。這正是 CCHM 2016 的說法
（「glue + filling 讓 `ua` 可計算」）在有限模型上的可執行版本。

### 3.5 驗證範圍

| card | 路徑數 `|Fin c = Fin c|` | checks |
|---|---|---|
| 0 | 1 | 0（沒有元素可檢查） |
| 1 | 1 | 4 |
| 2 | 2 | 24 |
| 3 | 6 | 198 |
| 4 | 24 | 2,880 |
| 5 | 120 | 76,200 |

七條定律在 card ≤ 5 全部 `true`（`cubical/cubical_test.mbt` 的 K2a）；K2b 另外驗證
**不相容的盒沒有填充體**（回傳 `None`）與越界元素被拒；K2c 驗證 Lehmer 排名/反排名
是 `S_n ≅ [0,n!)` 的顯式雙射（K3 用它把等價編成項）。

---

## 4. K3：cubical NBE（Normalization by Evaluation）

### 4.1 項代數與語義

```moonbit
enum CTerm {
  CElem(Int)                    // 元素：El(Fin card) 的索引
  CSigma(Int)                   // 等價：Lehmer 秩為 k 的置換（= 已驗證雙射）
  CRefl                         // refl
  CSym(CTerm)                   // 路徑反向
  CTrans(CTerm, CTerm)          // 路徑複合
  CUa(CTerm)                    // ua：等價 → 路徑（glue）
  CTransport(CTerm, CTerm)      // transport：路徑 × 元素 → 元素（Kan 填充）
}
enum CValue { VPath(Bij); VElem(Int) }
```

`CTerm` 是**遞歸**的（`CSym(CTerm)` 等），所以 `CTrans(CUa(CSigma(k)), CElem(x))`
這種真正的巢狀項可以被表示 —— 這是舊 `Term{code,tag}` 做不到的事。

### 4.2 求値 / 具體化 / NBE

* `ceval(t, card) : CValue?` —— 在 `Fin card` 模型中詮釋 `t`；**型別或範圍不合回傳 `None`**
  （卡住），不假裝成功。
* `reify(v)` —— `VElem(i) ↦ CElem(i)`；`VPath(b) ↦ CRefl`（若 `b = id`）或
  `CUa(CSigma(lehmer_code b))`（否則）。
* `cnorm(t) = reify(ceval(t))` —— 這就是 **NBE**：不逐項重寫，而是「求値到語義、
  再讀回語法」（Sterling–Angiuli–Gratzer 2019 的有限版本）。卡住的項原樣保留。

### 4.3 重寫規則

`crewrite_step` 套用第一條可用規則（`crewrite_top` 做上下文閉包，`crewrite` 迭代到不動點）：

| 規則 | 左邊 → 右邊 | 數學內容 | 守衛 |
|---|---|---|---|
| R1 | `transport(refl, x) → x` | refl 的傳輸是恒等 | `x` 求値為元素 |
| R4 | `transport(ua σ, x) → transport(σ, x)` | `ua` 的 glue 就是 `σ` | `x` 求値為元素 |
| R5 | `transport(p, x) → el(j)` | **Kan 填充**（§3.2） | `p` 求値為路徑、`x` 為元素 |
| R6 | `sym(sym p) → p` | 對合 | `p` 求値為路徑 |
| R7 | `trans(refl, q) → q`、`trans(p, refl) → p` | 單位律 | 另一邊求値為路徑 |
| R10 | `sym(ua σ) → ua σ⁻¹`（或 `refl`） | `ua` 保 `sym` | `σ` 是合法秩 |
| R11 | `trans(ua σ, ua τ) → ua (τ∘σ)`（或 `refl`） | `ua` 保 `trans`（群胚函子性） | 兩個秩合法 |
| R12 | `ua(id) → refl` | uaη | 秩合法且為恒等 |

R10/R11/R12 就是 `docs/UNIVALENCE.md` 裡「`ua` 是群胚函子」的三條定律，
現在變成**可執行的重寫規則**（而不只是布林檢查）。

### 4.4 守衛的必要性：一個真實的反例

第一版實作**沒有守衛**，驗證立刻抓到不健全：

```
t = transport(refl, σ0)        // σ0 = 秩 0 的等價，是「路徑」而不是「元素」
ceval(t) = None                // 盒的第二個參數 sort 不對 ⇒ 卡住
R1 無守衛：t → σ0，而 ceval(σ0) = Some(VPath id)
```

語義從「卡住（`None`）」變成「有値（`Some`）」⇒ **重寫不保語義**。修法是把每條規則
限制在「redex 於模型中良型」時才開火（`ceval_is_elem` / `ceval_is_path`）。
修好之後 `rewrite_sound` 對**全部** 7,385 個枚舉項成立（包括卡住的項），
而且 `cnorm` 的輸出真的是不動點（`normal_forms`）。

> 這條反例是本報告最想留下的東西：**窮盡驗證不是儀式，它抓到了真實的 bug**。
> 回歸測試見 `cubical/cubical_test.mbt` 的 K3c（`crewrite(transport(refl, σ0)) = 0 步`）。

### 4.5 終止性：勢函數

**定理（強正規化）**：`crewrite` 對任何項都在 ≤ `cterm_size(t)` 步內收斂。

*證明*：取 Φ₁(t) = `cterm_size(t)`（結構大小）。逐條檢查：R1/R6/R7 減 2；R4 減 2；
R5 把運輸項化為 `el(j)`（size 1，原本 ≥ 3）；R10 把 `sym(ua σ)`(3) 化為 `ua σ⁻¹`(2)
或 `refl`(1)；R11 把 5 化為 ≤ 3；R12 把 3 化為 1。每條都**嚴格減少** Φ₁。
又 `cterm_size` 對子項可加，所以在子項開火（上下文閉包）時，整個項的 Φ₁ 減少同樣的量。
Φ₁ ∈ ℕ 嚴格遞減 ⇒ 無窮遞降不存在。∎

`nbe_proof.measure_ok` 逐步驗證這件事（用字典序勢函數 `Φ = (Φ₁, Φ₂)`，
Φ₂ = `cterm_sym_count`；Φ₁ 已經足夠，Φ₂ 是冗餘的安全邊際），
`terminated` / `max_steps` 則回報實測收斂步數（實測最大 **3** 步）。

### 4.6 為什麼 R8（結合律）不在重寫關係裡

`trans(trans(p,q), r) → trans(p, trans(q,r))` 是**保大小**的（兩邊節點數相同），
會破壞 §4.5 的嚴格遞減；而且它的勢函數分析需要更細緻的路徑度量
（左脊深度在 `q` 本身左巢時不會減少）。所以：

* 把它降級為**語義層的 coherence**：`creassoc` 是純語法函數，
  `nbe_proof.reassoc_sound` 窮盡驗證它**保語義且保大小**；
* 結合性在語義層由 `ceval` 一次性處理（`cnorm` 對任意巢狀都能算），
  並且在 K2 以 `functorial`（`transport (q∘p) = transport q ∘ transport p`）驗證過。

測試 K3c 也斷言 `judgmental_eq_ct(t, creassoc(t))` —— 重結合前後判斷相等。

### 4.7 定理清單（`nbe_proof`，全部窮盡）

| 欄位 | 陳述 |
|---|---|
| `rewrite_sound` | 每一步重寫都保語義：`ceval(cur) = ceval(next)`（`None ↔ None` 也算一致） |
| `norm_sound` | `ceval(cnorm t) = ceval t` |
| `agrees` | 重寫系統與 NBE 一致：`cnorm(crewrite t) = cnorm t`（良型項） |
| `idempotent` | `cnorm(cnorm t) = cnorm t` |
| `normal_forms` | 範式是不動點：`crewrite_top(cnorm t)` 不再變化（良型項） |
| `terminated` / `max_steps` | 全部項在 `max_steps` 內收斂；回報實測最大步數 |
| `measure_ok` | 勢函數 Φ 每步字典序嚴格遞減（§4.5 的可執行見證） |
| `reassoc_sound` | R8 重結合保語義、保大小（§4.6） |
| `equivalence` | `judgmental_eq_ct` 是自反、對稱、遞歸的（等價關係） |
| `eq_sound` | 判斷相等 ⇒ 語義相同 |
| `eq_complete` | 語義相同 ⇒ 判斷相等（**可判定**） |

`agrees` / `normal_forms` 限定在良型項（`ceval t = Some`）：卡住的項 `cnorm` 原樣保留，
但它的**內部**仍可能含良型 redex，所以「範式是不動點」這句話對卡住的項不成立，
也不該成立（NBE 的陳述本來就只涉及良型項）。

### 4.8 一個完整的化簡例子（demo 輸出）

```
transport(ua(σ3), el(1))  ⟶  transport(σ3, el(1))  ⟶  el(2)          （2 步）
```

其中 `σ3` 是 3-循環 `(0 1 2)` 的 Lehmer 秩（`lehmer_code([1,2,0]) = 1·2! + 1·1! = 3`），
`σ3(1) = 2`。第一步是 R4（ua 的 glue 消除），第二步是 R5（Kan 填充）。
這一行就是 **uaβ 作為計算**的樣子：`transport (ua e) x ≡ e x`。

---

## 5. 可執行驗證結果

### 5.1 K1（`cubical_proof`）

| dim | faithful | C1 | C2 | C3 | assoc/unit | count | variants | generated | sound_eq | checks |
|---|---|---|---|---|---|---|---|---|---|---|
| 2 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 11,367 |
| 3 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 93,767 |
| 4 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | **4,172,976** |

（`assoc/unit` 只在 dim ≤ 2 做三重循環，因為它是 `|Hom|³` 的規模；dim=4 時
`|Hom(4,4)| = 321`，三重循環達 3.3×10⁷。）

### 5.2 K2 / K3

見 §3.5 與 §4.7 的表格。摘要：`kan_holds(card)` 對 card ≤ 5 全 `true`；
`nbe_holds(3,1,6,8)`、`nbe_holds(2,2,2,8)`、`nbe_proof(4,1,4,8)` 全 `true`，
共 **7,385 + 230 + 189 = 7,804** 個項、**36,885** 次原子比較。

### 5.3 測試清單（`cubical/cubical_test.mbt`，12 個）

| 測試 | 內容 |
|---|---|
| K1a | dim ≤ 3 的 9 條定律 + `cubical_holds(4)` + checks > 90000 |
| K1b | `∂_{0,1}` / `σ_1` 的具體座標與逐點作用値 |
| K1c | Hom 計數三層公式（13/14/16、19/22/25、38/44/64、63/86/125）與枚舉、生成律 |
| K1d | 面數 8/12/6/1、χ(Q^n)=1（公式 + 枚舉）、Gray 碼 Hamiltonian 圈（n ≤ 5） |
| K2a | card ≤ 5 的七條 Kan 定律 + `kan_holds` |
| K2b | 不相容的盒回傳 `None`、越界元素被拒、`|Fin3=Fin3| = 6` |
| K2c | Lehmer 排名/反排名互逆（card ≤ 5）、秩越界回傳 `None` |
| K3a | NBE 的 11 條定律（含 `measure_ok`、`reassoc_sound`） |
| K3b | 具體化簡：uaβ、`ua(id)→refl`、`transport refl`、`sym∘sym`、`trans` 單位律、`ua σ ∘ ua σ⁻¹ → refl`、卡住的項不被假裝修好 |
| K3c | 守衛反例（§4.4）、勢函數嚴格遞減（§4.5）、重結合 coherence（§4.6） |
| K0 | `cubical_axiom_count() = 0`、`univalence_axiom_count() = 0` |
| H1 | `cubical_transport(refl, 99) = 99`、`kan_transport_code`、加法直線族 |

### 5.4 重現步驟

```bash
export PATH="$HOME/.moon/bin:$PATH"     # moon 0.1.20261012 / moonc v0.10.15
moon check                              # 0 errors, 113 warnings
moon test                               # Total tests: 112, passed: 112, failed: 0
moon test cubical                       # Total tests: 18（12 黑盒 + 6 個 cubical/README.mbt.md 的 mbt check）
moon run cmd/main                       # 見下面的 cubical: 行
moon build --target wasm-gc,js,native   # 三個目標皆 0 errors
```

> 本文寫成時（commit `d28105a`，扁平檔案佈局）的實測值為 `moon check` 0 errors / 101 warnings、
> `moon test` 51 passed；package 重構之後（commit `5af71c5` 起）變成上面的數字，
> **K1–K3 的數學內容與實測數據（checks、項數、定律）完全不變**。

> **不要跑 `moon fmt`**（`AGENTS.md` 的慣例在此版本不安全）：實測 `moonfmt` 會把
> 型別標註裡的 `Int` 改寫成 `Int32`（連獨立 scratch 檔也一樣），那是**語義變更**而非排版；
> 它同時會插入 `///|` 並重排全部 33 個追蹤檔。本庫（含既有檔案）一律維持手寫排版。

```
cubical: axioms=0 K1(dim<=3 checks=93767 C1C2C3=true assoc=true count=true gen=true euler_Q3=1 gray=true) K2(card<=4 checks=2880 kan=true fill(ua(012),1)=2) K3(terms=230 sound=true nbe=true decidable=true transport(ua(σ3),el(1))=el(2)/2步)
```

---

## 6. 行為變更（API 相容，數值語義修正）

| 項目 | 舊 | 新 | 原因 |
|---|---|---|---|
| `normalize(Term{2048,"x"})` | `{48, "x_nf"}` | `{2048, "x"}`（恒等） | `Term` 無內部結構；`% 1000` 是伪造範式 |
| `judgmental_eq(Term{1001,"t"}, Term{1,"t"})` | `true` | **`false`** | 假陽性：1001 ≢ 1 |
| demo 行 `hott_algo:` | `eq=true norm_code=48` | `eq=false norm_code=2048 kan_fill=2` | 同上；`kan_fill` 是真正的 Kan 填充結果 |
| `cubical_transport(p, v)` | `v + p.code` | `v + p.code`（**不變**） | 保留為 code 直線族的特例，文件改為誠實聲明 + 指向 `cubical_transport_kan` |
| `axiom_test.mbt` | 斷言 `judgmental_eq(...) = true` | 斷言 `false` + `normalize` 為恒等 + `cubical_kan_demo() = "2"` | 跟隨修正 |

新增 API（`cubical/hott_cubical.mbt`，約 60 個）：`Coord`/`CubeMap`/`cubemap_*`、
`face_map`/`degen_map`/`swap_map`、`cube_points`/`cube_points_gray`/`gray_hamiltonian_check`、
`cube_face_count`/`cube_faces_enum`/`cube_euler`/`cube_euler_enum_check`、
`cubemap_all_standard`/`_with_swaps`/`_full`、`cube_hom_count_*`、`cubemap_generated`、
`cubical_proof`/`cubical_holds`/`cubical_line`；
`ElBox`/`KanFill`/`kan_fill_el`/`kan_compose`/`kan_proof`/`kan_holds`/`kan_transport_code`；
`CTerm`/`CValue`/`ceval`/`cnorm`/`crewrite*`/`judgmental_eq_ct`/`cterms_upto`/`cterm_show`/
`cterm_size`/`cterm_sym_count`/`cterm_phi`/`phi_lt`/`creassoc`/`nbe_proof`/`nbe_holds`；
`perm_from_lehmer`/`lehmer_bijection_check`/`cube_factorial`/`cubical_axiom_count`。
`hott_algorithms/hott_algorithms.mbt` 新增 `cubical_transport_kan`、`cubical_kan_demo`；
`axiom.mbt` 新增 `cubical_demo()`；`cmd/main/main.mbt` 新增 cubical 區塊。

---

## 7. 誠實聲明：這個「演算法」的邊界

1. **MoonBit 不是證明助手**。`Path` 的端點不被型別檢查，`CTerm` 的 sort 也不被型別檢查
   （所以 `ceval` 會在執行期回傳 `None`）。本文所有「定理」都是
   **模型論式的可執行證明**：在語義明確、相等可判定的有限模型裡，把定律化為有限計算並
   窮盡驗證。這與 `docs/UNIVALENCE.md` §7 的立場一致。
2. **有限範圍**：K1 dim ≤ 4（4,172,976 次比較）、K2 card ≤ 5（120 條路徑）、
   K3 深度 ≤ 2（8,034 個項）。超出範圍的維度/基數**沒有被驗證**。
3. **K1 是「座標函數」的具體模型**，不是語法範疇：態射被表示為 `{0,1}`-値的座標函數，
   這在有限維度下與 □ 的抽象定義等價（§2.3 的忠实性 + §2.5 的生成律就是這件事的證據），
   但它不涵蓋 connections/diagonals 之外的更高階結構。
4. **K2 的 Kan 填充是在單值性纖維 `El` 上**，不是在「全宇宙的每個 Kan 型別」上。
   真正的 cubical TT 需要對每個型別形成子（`PathP`、`Glue`、`hcomp`）都給出填充演算法；
   這裡只實現了 `El`（有限集合）這一族 —— 但它正好是單值性需要的那一族。
   另外，本庫的盒是**一維**的（一個路徑方向 + 一個元素方向）；
   高維 `hcomp`（多方向同時開盒）未實作。
5. **K3 的完備性是相對模型的**：`eq_complete` 說的是「在 `Fin card` 模型中語義相同 ⇒
   範式相同」。若兩個項在更大的模型中才可區分，這裡的判定不會發現。
   此外 `CTerm` 沒有 λ/Π，所以這不是完整 cubical TT 的 NBE，而是
   「群胚 + 元素」這一片段的 NBE。
6. **`cubical_transport` 仍是 code 加法**（保留向後相容）。它是 `family(x) = x + code`
   這個直線族的特例；要真正的傳輸請用 `cubical_transport_kan` / `kan_fill_el`。

---

## 8. 後續可做（不影響本次結論）

* **高維 `hcomp`**：實作多方向同時開盒的填充（需要 side 列表 + 相容性條件），
  並驗證填充的唯一性與 naturality。
* **`PathP`（依賴路徑）與 `Glue` 型別形成子**：把 K2 從 `El` 一族推廣到依賴族，
  這樣 `transport` 才能沿著宇宙路徑搬運**結構**（目前 `sip_monoid_fin` 是手工搜索的）。
* **connections**：加入 `Γ_{i,ε}` 生成元，把 K1 推到最大 cube 範疇（`(m+2)^n` 那一層），
  並驗證 connections 的六組關係。
* **完整的 cubical 項代數**：`CTerm` 加上 `λ`/`Π`/`W`/區間變數 `i`，
  讓 K3 成為真正的 cubical NBE（Sterling–Angiuli–Gratzer 的中性項/値分離）。
* **把 dim 推到 5、card 推到 6**：需要剪枝（`cubical_proof` 的 `|Hom|²` 項是瓶頸：
  `|Hom(4,4)| = 321`、`|Hom(5,5)| = 1,683`，平方後 2.8×10⁶ 格，每格再跑 32 個頂點）。
* **型別層證明**：把 `CubeMap`/`UPath`/`CTerm` 移植到 Agda 的 cubical 庫或 Lean 4，
  §2.2 的三組恆等式與 §4.5 的終止性可以逐條變成型別層定理。

---

## 附錄：術語對照

| 中文 | 英文 | 程式碼 |
|---|---|---|
| 立方體範疇 | cube category □ | `CubeMap` / `cubemap_comp` |
| 面映射（coface） | face map ∂_{i,ε} | `face_map` |
| 退化映射（codegeneracy） | degeneracy σ_i | `degen_map` |
| 對稱（swap） | symmetry s_i | `swap_map` |
| 座標函數 | coordinate function | `Coord` |
| 忠实性 | faithfulness | `CubicalProof.faithful` |
| 外延相等 | extensional equality | `cubemap_eq_points` |
| 生成律 | generated by faces/degeneracies | `cubemap_generated` |
| n-立方體的面格 | face lattice of Q^n | `cube_faces_enum` |
| Euler 特徵數 | Euler characteristic χ | `cube_euler` |
| Gray 碼 Hamiltonian 圈 | Gray code Hamiltonian cycle | `cube_points_gray` |
| 開放盒 / 填充 | open box / filler | `ElBox` / `kan_fill_el` |
| Kan 填充 | Kan filling | `kan_fill_el` / `kan_compose` |
| 盒條件 | box condition | `KanProof.unique_iff` |
| 傳輸 | transport | `upath_transport` / `cubical_transport_kan` |
| 計算律 uaβ | computation rule | `KanProof.ua_beta` |
| 求値 / 具體化 | evaluate / reify | `ceval` / `reify` |
| 正規化_by_求値 | normalization by evaluation | `cnorm` |
| 重寫規則 | rewrite rules R1–R12 | `crewrite_step` |
| 良型守衛 | typing guard | `ceval_is_elem` / `ceval_is_path` |
| 勢函數 / 強正規化 | potential / strong normalization | `cterm_phi` / `measure_ok` |
| 範式 | normal form | `cnorm` / `normal_forms` |
| 判斷相等 | judgmental equality | `judgmental_eq_ct` |
| Lehmer 秩 | Lehmer code / rank | `lehmer_code` / `perm_from_lehmer` |

**參考文獻**

1. Cohen, Coquand, Huber, Mörtberg, *Cubical Type Theory: A Constructive Interpretation of
   the Univalence Axiom* (2016) —— 立方體範疇的生成元與關係、glue、Kan 填充使 `ua` 可計算。
2. Kan, *Functors involving c.s.s. complexes* (1958) —— cube category 與 ∂/σ 關係的原始來源。
3. Orton, Pitts, *Univalence in Constructive Set Theory / Cubical Sets* (2016)。
4. Angiuli, *Constructive Homotopy Type Theory* (2019) —— cartesian cubical（swap 生成元）
   與 Kan 型別宇宙上的單值性。
5. Sterling, Angiuli, Gratzer, *Normalization for Cubical Type Theory* /
   *A Cubical Language for Univalence* (2019) —— cubical NBE（eval-then-reify、中性項）。
6. Grandi, *Cubical Type Theory* lecture notes；Rijke, *Introduction to HoTT* §
   —— 面/退化關係的索引約定對照（見 §2.2 的約定警告）。
7. `docs/UNIVALENCE.md`（本庫）—— 單值性：公理 → 定理；K2 是其 §8 第一項的完成報告。
