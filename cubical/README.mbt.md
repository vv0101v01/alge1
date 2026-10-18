# `cubical` — 有限立方體演算法 K1–K3：立方體範疇 □ · Kan 填充 · cubical NBE

> **package** `axiom/axiom/cubical` · **alias** `@cubical` · **依賴**：`@hott_core` · `@univalence`
> **檔案**：`hott_cubical.mbt`（1444 行）· `cubical_test.mbt`（黑盒測試 12 個）· `moon.pkg`
> **公開 API**：63 項 = 3 個 enum + 6 個 struct + 54 個函數 · **本 package 引入的公理：0**（`cubical_axiom_count() = 0`）

## 1. 呢個資料夾做乜

**立方體類型論**（cubical type theory）用「立方體範疇 □」代替 Martin-Löf 嘅恆等類型，
令單值性變成**可計算**嘅（`ua` 有 glue、`transport` 就係 Kan 填充）。呢個 package 喺
**有限模型**上把三件事真係做出嚟，並且**窮盡驗證**：

| 編號 | 演算法 | 內容 | 入口 | 證明物件 |
|---|---|---|---|---|
| **K1** | 立方體範疇 □ | 態射 = 座標函數（常數 0/1 或投影）；face/degen/swap 生成元；C1/C2/C3 交換律；三種範疇變體嘅態射計數；BFS 生成律；面數與 Euler 特徵數；Gray code Hamiltonian 圈 | `cubical_proof(n)` | `CubicalProof`（11 欄） |
| **K2** | Kan 填充 | 單值性纖維 $El : U_{fin} \to \mathsf{Type}$ 上嘅**開放盒**求解：上邊缺失 ⇒ 填充體由 glue 消除規則給出（**呢個就係 transport**）；上邊給定 ⇒ 只有相容先有解 | `kan_proof(card)` | `KanProof`（9 欄） |
| **K3** | cubical NBE | 有限項代數 `CTerm`（元素／已驗證等價 σ／refl／sym／trans／ua／transport）+ 帶良型守衛嘅重寫系統 R1–R12 + eval-then-reify 正規化 + 可判定判斷相等 + **終止性證明**（勢函數嚴格遞減） | `nbe_proof(card, depth, sigma_limit, max_steps)` | `NbeProof`（15 欄） |

三者串起嚟就係 `cubical_summary(card)` 嘅一行輸出，亦係 root `cubical_demo()` 嘅內容：

```text
cubical: axioms=0 K1(dim<=3 checks=93767 C1C2C3=true assoc=true count=true gen=true euler_Q3=1 gray=true)
         K2(card<=4 checks=2880 kan=true fill(ua(012),1)=2)
         K3(terms=230 sound=true nbe=true decidable=true transport(ua(σ3),el(1))=el(2)/2步)
```

完整推導、約定同實驗數據見 **`docs/CUBICAL.md`**（589 行）。

## 2. 公理

**無。** `cubical_axiom_count()` 恆為 `0`：K1 嘅態射全部由座標函數**構造**出嚟，
K2 嘅填充體由 `@univalence.UPath` 嘅 `glue`（已驗證嘅 `Bij`）**計算**出嚟，
K3 嘅範式由 `ceval` + `reify` **計算**出嚟。冇任何一個布林値係寫死嘅 `true`。

> **誠實邊界**：
> 1. MoonBit 唔係證明助理。`CTerm` 嘅 **sort 唔會被型別檢查器追蹤**：`CElem(i)` 係元素定係
>    `CUa(σ)` 係路徑，由 `ceval` 喺求値時判定（唔合就回 `None`），唔係由型別保證。
> 2. 呢度嘅「區間」係**有限立方體** $\{0,1\}^n$，唔係形式化嘅 interval object；
>    `Coord` 只有 `CZero`/`COne`/`CVar(i)`，冇一般 cubical TT 嘅連接（connection）項，
>    但 `cubemap_all_full` 枚舉咗「加咗 connections／對角線嘅最大 cubical 範疇」嘅全部態射
>    （$(m+2)^n$ 個）作為上界對照。
> 3. K3 嘅重寫系統有**良型守衛**，健全性因此係無條件嘅；但 **R8（trans 結合律）冇納入
>    重寫關係**——佢係 size-中立嘅，會破壞勢函數嘅嚴格遞減。佢仍然被窮盡驗證
>    （`nbe_proof.reassoc_sound`：重結合保語義且保大小）。
> 4. 所有驗證都係**有限範圍內窮盡**（dim ≤ 4、card ≤ 5、項數 ≤ 7,804），
>    加上 `docs/CUBICAL.md` 嘅書面推導（CCHM 2016、Orton–Pitts 2016、Angiuli 2019、
>    Sterling–Angiuli–Gratzer NBE）。**唔係**機器檢查嘅形式證明。

## 3. K1 — 立方體範疇 □

### 3.1 定義（類型）

| 名稱 | 數學內容 | 實作 |
|---|---|---|
| `Coord` | 座標函數：常數 0、常數 1、或第 $i$ 個投影 | `enum { CZero, COne, CVar(Int) }` |
| `CubeMap` | 態射 $[dom] \to [cod]$：`cod` 個座標函數，每個係 `dom` 個輸入座標嘅投影或常數 | `{ dom : Int; cod : Int; coords : Array[Coord] }`（`coords.length() == cod`） |
| `CubicalProof` | K1 嘅證明物件：**每一欄都由窮盡計算得出** | 見 §3.3 |

### 3.2 演算法

| 名稱 | 語義 | 內容 |
|---|---|---|
| `cubemap_id(n)` | $id_{[n]}$ | `coords = [CVar(0)..CVar(n-1)]` |
| `cubemap_comp(g, f)` | 複合 $g \circ f$（先 f 後 g；要求 `g.dom == f.cod`） | 逐座標代入；唔合規格回 `None` |
| `cubemap_eq(f, g)` | 語法相等 | `dom`/`cod`/`coords` 逐項 |
| `cubemap_apply(f, pt)` | 態射作用在頂點上 $\{0,1\}^{dom} \to \{0,1\}^{cod}$ | 逐座標求値 |
| `cubemap_eq_points(f, g)` | **外延相等**：喺全部 $2^{dom}$ 個頂點上逐點相同 | 窮盡比對 |
| `face_map(n, i, eps)` | 面映射（coface）$\partial_{i,\varepsilon} : [n] \to [n+1]$：喺第 $i$ 個座標插入常數 $\varepsilon$ | $j<i \mapsto \mathtt{Var}(j)$；$j=i \mapsto \mathtt{Const}(\varepsilon)$；$j>i \mapsto \mathtt{Var}(j-1)$ |
| `degen_map(n, i)` | 退化映射（codegeneracy）$\sigma_i : [n+1] \to [n]$：忘掉第 $i$ 個座標 | $j<i \mapsto \mathtt{Var}(j)$；$j \ge i \mapsto \mathtt{Var}(j+1)$ |
| `swap_map(n, i)` | 對稱生成元 $s_i : [n+1] \to [n+1]$：交換相鄰座標 $i, i+1$ —— cartesian cubical TT（Angiuli）比 coarse □ 多嘅生成元 | — |
| `cubemap_is_ordered(f)` | 變數嚴格遞增 ⇒ 屬於**標準 □**（Kan/CCHM 嘅 coarse cube category） | — |
| `cubemap_is_var_injective(f)` | 變數互不重複 ⇒ 屬於 □ + swap 生成嘅 **cartesian** 版本 | — |
| `cube_points(n)` | $\{0,1\}^n$ 全部頂點（$2^n$ 個，字典序） | — |
| `cube_points_gray(n)` | Gray code 順序嘅 $2^n$ 個頂點：相鄰（含首尾）恰差一位 ⇒ n-立方體圖嘅 **Hamiltonian 圈** | — |
| `cubemap_all_standard(dom, cod)` | 枚舉標準 □ 嘅態射（變數嚴格遞增） | — |
| `cubemap_all_with_swaps(dom, cod)` | 枚舉 cartesian □（加 swap）嘅態射（變數互不重複、順序任意） | — |
| `cubemap_all_full(dom, cod)` | 枚舉 $\{0,1\}^{dom} \to \{0,1\}^{cod}$ 嘅**全部**自然變換：$(dom+2)^{cod}$ 個（= 加咗 connections／對角線嘅最大 cubical 範疇） | — |
| `cubemap_generated(dom, cod)` | **生成律演算法**：從 $id_{[dom]}$ 出發反覆後複合 face/degen（BFS 閉包），取出 cod 相符者；結果應恰好等於 `cubemap_all_standard` | — |
| `cube_hom_count_standard(m, n)` | 計數公式 $\vert Hom_\square([m],[n])\vert = \Sigma_k C(n,k)C(m,k)2^{n-k}$ | 選 $k$ 個輸出座標放變數、選 $k$ 個輸入變數、順序被遞增性強制、其餘 $n-k$ 個座標放常數 |
| `cube_hom_count_swaps(m, n)` | 加 swap：$\Sigma_k C(n,k)(m)_k 2^{n-k}$，$(m)_k$ 為降階乘 | — |
| `cube_hom_count_full(m, n)` | 加 connections（最大）：$(m+2)^n$ | — |
| `cube_face_count(n, k)` | $n$-立方體嘅 $k$ 維面數 $= C(n,k)2^{n-k}$ | 固定 $n-k$ 個座標、其餘自由 |
| `cube_faces_enum(n, k)` | **枚舉**（唔套公式）全部 $k$ 維面：簽名陣列中 `-1` = 自由座標，`0/1` = 固定値 | — |
| `cube_euler(n)` | Euler 特徵數（公式版）$\chi(Q^n) = \Sigma_k (-1)^k C(n,k)2^{n-k} = (2-1)^n = 1$ | — |
| `cube_euler_enum_check(n)` | 用**枚舉**出嚟嘅面重算 $\chi$，同公式比對，並檢查 $\chi = 1$（n-立方體可縮） | — |
| `gray_hamiltonian_check(n)` | Gray code 檢查：$2^n$ 個頂點互異、相鄰（含首尾）恰差一位 ⇒ Hamiltonian 圈 | — |
| `cubical_proof(n)` | 對維度上限 `n` **窮盡驗證**立方體範疇嘅全部公理 | 回傳 `CubicalProof` |
| `cubical_holds(n)` | K1 嘅總結判準 | 全部欄位皆 true |
| `cubical_line(pf)` | K1 一行摘要（demo／文件用） | — |

### 3.3 `CubicalProof` 嘅欄位（= K1 驗證咗啲乜）

| 欄位 | 內容 |
|---|---|
| `dim` | 驗證到嘅維度上限 |
| `faithful` | □ 喺 $\{0,1\}^n$ 上**忠實**：語法相等 ⟺ 外延相等（窮盡比對所有態射對） |
| `coface_coface` | **C1** $\partial_{j,\delta}\partial_{i,\varepsilon} = \partial_{i+1,\varepsilon}\partial_{j,\delta}$（$i \le j$） |
| `degen_degen` | **C2** $\sigma_j\sigma_i = \sigma_i\sigma_{j+1}$（$i \le j$） |
| `degen_coface` | **C3** $\sigma_j\partial_{i,\varepsilon}$ 嘅三種情況（$i<j$ / $i=j,j+1$ / $i>j+1$） |
| `assoc_unit` | 複合嘅結合律與單位律（窮盡三元組） |
| `count_law` | 枚舉數 = 三條計數公式（standard／swaps／full） |
| `variant_counts` | 三種範疇變體嘅態射數逐個核對（見 §3.4 表） |
| `generated_by` | **生成律**：BFS 閉包 = `cubemap_all_standard`（face/degen 生成整個 □） |
| `sound_eq` | `cubemap_eq` 與頂點窮盡比對一致 |
| `checks` | 執行過嘅原子比較次數（窮盡程度嘅見證） |

### 3.4 K1 實測數據

| 項目 | 數値 |
|---|---|
| `cubical_proof(2).checks` | 11,367 |
| `cubical_proof(3).checks` | 93,767 |
| `cubical_proof(4).checks` | 4,172,976（約 6 秒） |
| $\vert Hom([4],[4])\vert$（標準 □） | 321 |
| $\vert Hom([5],[5])\vert$（標準 □） | 1,683 |
| Hom 三層（std／swaps／full），$n=2$ | $m=1$: 8／8／9 · $m=2$: 13／14／16 · $m=3$: 19／22／25 |
| Hom 三層，$n=3$ | $m=1$: 20／20／27 · $m=2$: 38／44／64 · $m=3$: 63／86／125 |
| $Q^4$ 嘅 $k$ 維面數 | 16／32／24／8／1（$k=0..4$，$=C(4,k)2^{4-k}$） |
| $\chi(Q^n)$ | 1（全部 $n$；`cube_euler_enum_check` 用枚舉重算亦為 1） |
| Gray code Hamiltonian 圈 | $n \le 5$ 全部驗證通過 |

## 4. K2 — Kan 填充（transport 就係解開放盒）

### 4.1 定義（類型）

| 名稱 | 數學內容 | 實作 |
|---|---|---|
| `ElBox` | 單值性纖維 $El : U_{fin} \to \mathsf{Type}$ 上嘅**開放盒**：左邊 = 路徑 `path : base =_U target`（帶 glue），下邊 = 元素 `bottom ∈ El(base)`，上邊 = `top?`（缺失 ⇒ 開放盒） | `{ path : @univalence.UPath; bottom : Int; top : Int? }` |
| `KanFill` | Kan 填充結果 | `{ top : Int; compatible : Bool }` |
| `KanProof` | K2 嘅證明物件 | 見 §4.3 |

### 4.2 演算法

| 名稱 | 語義 | 內容 |
|---|---|---|
| `kan_fill_el(box)` | **Kan 填充演算法**：解開放盒。上邊缺失 ⇒ 填充體由 glue 嘅消除規則給出（**呢個就係 transport**）；上邊給定 ⇒ 只有相容（`top = transport path bottom`）先有解，否則回 `None` | 填充體 = `upath_transport(path, bottom)` = `bij_apply(glue, bottom)` |
| `kan_compose(p, q, x)` | 二維 Kan 複合：沿 $q \circ p$ 嘅傳輸 = 兩次 1-維填充嘅串接（**運輸嘅函子性**） | 越界回 `None` |
| `kan_transport_code(c, v)` | 舊 API（H1）嘅加法直線族：transport 沿 code 為 $c$ 嘅路徑把 $v$ 平移 $c$。呢個係 Kan 填充喺「code 族」上嘅特例（refl ⇒ $c=0$ ⇒ 恒等） | — |
| `kan_proof(card)` | 對 `Fin card` **窮盡驗證** Kan 填充嘅全部定律 | 回傳 `KanProof` |
| `kan_holds(card)` | K2 嘅總結判準 | — |

### 4.3 `KanProof` 嘅欄位

| 欄位 | 內容 |
|---|---|
| `card` | 驗證嘅基數 |
| `exists` | 開放盒**必有**填充體（對全部 $card!$ 條路徑 × 全部元素） |
| `unique_iff` | 閉盒（上邊給定）有解 **當且僅當** 上邊 = transport 嘅結果 |
| `universal` | 填充體嘅萬有性：任何相容嘅上邊都等於填充結果 |
| `functorial` | 運輸嘅函子性：$transport(q \circ p) = transport\ q \circ transport\ p$ |
| `roundtrip` | $transport(p^{-1}) \circ transport(p) = id$ |
| `refl_law` | $transport(refl) = id$ |
| `ua_beta` | **uaβ**：$transport(ua\ e)\ x = e\ x$（glue 消除規則） |
| `checks` | 原子比較次數 |

### 4.4 K2 實測數據

| `card` | `kan_proof(card).checks` | $\vert a =_U b\vert$（`upath_all`） |
|---|---|---|
| 0 | 0 | 1 |
| 1 | 4 | 1 |
| 2 | 24 | 2 |
| 3 | 198 | 6 |
| 4 | 2,880 | 24 |
| 5 | 76,200 | 120 |

`exists`／`unique_iff`／`universal`／`functorial`／`roundtrip`／`refl_law`／`ua_beta` 對 $card \le 5$ 全部 true。
示範：`cubical_kan_demo()`（喺 `hott_algorithms`）= `"2"`，即喺 `Fin 3` 上沿 3-循環 $(0\ 1\ 2)$ 嘅 `ua` 路徑把 $1$ 填到 $2$。

## 5. K3 — cubical NBE（正規化 + 可判定判斷相等 + 終止性）

### 5.1 定義（類型）

| 名稱 | 數學內容 | 實作 |
|---|---|---|
| `CTerm` | cubical **項代數**（有限） | `enum { CElem(Int)`（元素 $el(i) \in El(Fin\ card)$）`, CSigma(Int)`（Lehmer 秩為 $k$ 嘅置換 = **已驗證**雙射）`, CRefl, CSym(CTerm), CTrans(CTerm,CTerm), CUa(CTerm)`（ua：等價 → 路徑）`, CTransport(CTerm,CTerm)`（路徑 × 元素 → 元素）`}` |
| `CValue` | 語義値 | `enum { VPath(@univalence.Bij)`（路徑 = glue 雙射）`, VElem(Int)`（元素）`}` |
| `NbeProof` | K3 嘅證明物件 | 見 §5.3 |

### 5.2 演算法

| 名稱 | 語義 | 內容 |
|---|---|---|
| `cterm_eq(a, b)` | 項嘅結構相等 | 遞歸 |
| `cterm_size(t)` | 項嘅大小（**終止性度量** $\Phi_1$） | 子項可加 |
| `cterm_sym_count(t)` | $\Phi_2$：`sym` 節點數（次要勢函數；每條規則都令佢唔增） | — |
| `cterm_phi(t)` | 勢函數 $\Phi(t) = (\Phi_1, \Phi_2)$ | — |
| `phi_lt(a, b)` | $\Phi$ 嘅字典序嚴格小於 | — |
| `cterm_show(t)` | 項嘅可讀表示（demo／文件用） | 例：`transport(ua(σ3),el(1))` |
| `perm_from_lehmer(card, k)` | **Lehmer 反排名**：秩 $k$ 嘅置換（`lehmer_code` 嘅逆） | 例：`perm_from_lehmer(3,1) = [0,2,1]` |
| `lehmer_bijection_check(card)` | Lehmer 排名／反排名互逆：$S_n \cong [0,n!)$ 嘅顯式雙射（窮盡驗證） | — |
| `ceval(t, card)` | **求値**：喺 `Fin card` 嘅有限模型中詮釋項；型別／範圍唔合時回 `None` | — |
| `cnorm(t, card)` | **cubical NBE**：正規化 = 求値後再具體化（eval-then-reify）；`reify(VPath b) = CRefl`（若 $b$ 係恆等）否則 `CUa(CSigma(lehmer_code b))` | — |
| `crewrite_step(t, card)` | 單步重寫：套用第一條可用嘅 cubical 化簡規則，回傳 (結果, 是否有變化) | 見 §5.4 |
| `crewrite(t, card, max_steps)` | 全步重寫至不動點；回傳 (範式, 步數)。**步數即終止性嘅見證** | — |
| `judgmental_eq_ct(a, b, card)` | **可判定嘅判斷相等**：範式相同 ⟺ 判斷相等 | — |
| `cterms_upto(card, depth, sigma_limit)` | 窮盡枚舉深度 ≤ `depth` 嘅項（葉子：`CElem(i)`、`CSigma(k)`、`CRefl`） | — |
| `creassoc(t)` | 純語法嘅 trans 右重結合（R8 嘅內容；**只用於驗證 coherence，唔參與重寫**） | — |
| `nbe_proof(card, depth, sigma_limit, max_steps)` | 對枚舉出嘅**全部**項窮盡驗證 cubical NBE 嘅性質 | 回傳 `NbeProof` |
| `nbe_holds(card, depth, sigma_limit, max_steps)` | K3 嘅總結判準 | — |

### 5.3 `NbeProof` 嘅欄位

| 欄位 | 內容 |
|---|---|
| `card` / `terms` / `checks` | 模型基數／枚舉出嘅項數／原子比較次數 |
| `rewrite_sound` | **健全性**：每步重寫都保語義 |
| `norm_sound` | **NBE 健全性**：$eval(norm\ t) = eval\ t$ |
| `agrees` | 重寫系統與 NBE 一致（良型項）：$norm(rewrite\ t) = norm\ t$ |
| `idempotent` | 冪等：$norm(norm\ t) = norm\ t$ |
| `normal_forms` | 範式係不動點（良型項）：$rewrite(norm\ t)$ 唔再變化 |
| `max_steps` / `terminated` | 全部項都喺 `max_steps` 內終止 |
| `measure_ok` | 勢函數 $(\Phi_1,\Phi_2)$ 逐步字典序遞減 |
| `reassoc_sound` | R8 重結合保語義且保大小 |
| `equivalence` | `CSigma(k)` 對應嘅置換確實係**已驗證**等價 |
| `eq_sound` / `eq_complete` | 判斷相等嘅健全性與完備性（對良型項） |

### 5.4 重寫規則與終止性

```text
R1  transport(refl, x)      → x
R4  transport(ua σ, x)      → transport(σ, x)        （glue / uaβ）
R5  閉項傳輸                 → Kan 填充結果
R6  sym(sym p)              → p
R7  trans 單位律
R10 sym(ua σ)               → ua σ⁻¹
R11 ua σ ∘ ua τ             → ua (τ ∘ σ)
R12 ua(id)                  → refl
R8  trans 結合律             → **不納入重寫**（size-中立，會破壞嚴格遞減；另行驗證 reassoc_sound）
```

**守衛**：每條規則只喺 redex 於模型中**良型**（求値成功且 sort 正確）時開火 ⇒ 重寫對
**全部**項（包括卡住嘅項）都保語義，`crewrite` 嘅健全性因此係無條件嘅。
（冇守衛會出事：`t = transport(refl, σ0)` 而 σ0 係路徑 sort ⇒ `ceval t = None`，
但無守衛嘅 R1 會把佢重寫成 `σ0`，`ceval` 變成 `Some(VPath id)` —— 由 `None` 變 `Some`，
健全性就破咗。）

**終止性（強正規化）**：$\Phi_1(t) = \mathsf{cterm\_size}(t)$。每條規則都**嚴格減少** $\Phi_1$：
R1/R6/R7 減 2，R4 減 2，R5 把運輸項化為 `el(j)`（size 1），R10 把 `sym(ua σ)`(3) 化為
`ua σ⁻¹`(2) 或 `refl`(1)，R11 把 5 化為 ≤3，R12 把 3 化為 1；而 size 對子項可加，
所以上下文閉包繼承同樣差量。$\Phi_1 \in \mathbb{N}$ 嚴格遞減 ⇒ 無窮遞降唔存在 ⇒
強正規化，且**步數 ≤ size(t)**。$\Phi_2$（sym 節點數）係冗餘嘅安全邊際。

### 5.5 K3 實測數據

| 參數 `(card, depth, sigma_limit)` | 項數 | checks | 最大步數 |
|---|---|---|---|
| (3, 1, 6) | 230 | 3,158 | ≤ 1 |
| (2, 2, 2) | 7,385 | 30,732 | ≤ 3 |
| (4, 1, 4) | 189 | 2,995 | ≤ 1 |
| **合計** | **7,804** | **36,885** | 15 個欄位全 true |

示範：`transport(ua(σ3), el(1))` 其中 $\sigma_3 = (0\ 1\ 2)$（Lehmer 秩 3）⇒ 2 步重寫成 `el(2)`。
假相等嘅見證：`CUa(CSigma(1))` 與 `CRefl` 語義唔同 ⇒ `judgmental_eq_ct` 回 `false`。

## 6. 頂層 API

| 名稱 | 內容 |
|---|---|
| `cubical_summary(card)` | 一行摘要（demo／README 用） |
| `cubical_axiom_count()` | **公理審計**：恆為 `0` |

## 7. 可運行例子

以下 ```mbt check``` 區塊由 `moon test` **真的編譯並執行**（成本已控制）。

```mbt check
test "README K1: 立方體範疇 □ 的態射、生成元與交換律" {
  // 態射 = cod 個座標函數
  let id2 = @cubical.cubemap_id(2)
  assert_eq(id2.dom, 2)
  assert_eq(id2.coords.length(), 2)
  // face_map(n, i, ε) : [n] → [n+1]，在第 i 個座標插入常數 ε
  // 約定：j<i ↦ Var(j)，j=i ↦ Const(ε)，j>i ↦ Var(j-1)
  // face_map / degen_map 回傳 CubeMap?（維度或索引越界時為 None）
  let f = @cubical.face_map(1, 0, 1).unwrap() // [1] → [2]，coords = [COne, CVar(0)]
  assert_eq(f.dom, 1)
  assert_eq(f.cod, 2)
  assert_eq(@cubical.cubemap_apply(f, [0]), [1, 0])
  assert_eq(@cubical.cubemap_apply(f, [1]), [1, 1])
  // degen_map(n, i) : [n+1] → [n]，忘掉第 i 個座標（j<i ↦ Var(j)，否則 Var(j+1)）
  let d = @cubical.degen_map(1, 0).unwrap() // [2] → [1]，coords = [CVar(1)]
  assert_eq(d.cod, 1)
  assert_eq(@cubical.cubemap_apply(d, [0, 1]), [1])
  // C3 的一個實例：σ_i ∘ ∂_{i,ε} = id_[n]
  let c3 = @cubical.cubemap_comp(d, f).unwrap()
  assert_true(@cubical.cubemap_eq(c3, @cubical.cubemap_id(1)))
  assert_true(@cubical.cubemap_eq_points(c3, @cubical.cubemap_id(1)))
  // C1/C2 的完整窮盡驗證交給 cubical_proof（見下）
  // 忠實性：語法相等 ⟺ 全部頂點上外延相等
  assert_true(@cubical.cubemap_eq_points(id2, @cubical.cubemap_id(2)))
  // 窮盡驗證（dim ≤ 2：11,367 次原子比較）
  let pf = @cubical.cubical_proof(2)
  assert_eq(pf.dim, 2)
  assert_true(pf.faithful)
  assert_true(pf.coface_coface)
  assert_true(pf.degen_degen)
  assert_true(pf.degen_coface)
  assert_true(pf.assoc_unit)
  assert_true(pf.count_law)
  assert_true(pf.generated_by) // BFS 閉包 = cubemap_all_standard
  assert_true(pf.checks > 10000)
  assert_true(@cubical.cubical_holds(2))
}
```

```mbt check
test "README K1: 態射計數公式與枚舉一致" {
  // |Hom([m],[n])| = Σ_k C(n,k)C(m,k)2^(n-k)
  assert_eq(@cubical.cubemap_all_standard(1, 2).length(), 8)
  assert_eq(@cubical.cube_hom_count_standard(1, 2), 8)
  // dom=2, cod=2 的三層：13 / 14 / 16
  assert_eq(@cubical.cubemap_all_standard(2, 2).length(), 13)
  assert_eq(@cubical.cube_hom_count_standard(2, 2), 13)
  // 加 swap：Σ_k C(n,k)(m)_k 2^(n-k)
  assert_eq(@cubical.cubemap_all_with_swaps(2, 2).length(), 14)
  assert_eq(@cubical.cube_hom_count_swaps(2, 2), 14)
  // 加 connections（最大）：(m+2)^n = 4²
  assert_eq(@cubical.cubemap_all_full(2, 2).length(), 16)
  assert_eq(@cubical.cube_hom_count_full(2, 2), 16)
  // dom=3, cod=2 的三層：19 / 22 / 25
  assert_eq(@cubical.cubemap_all_standard(3, 2).length(), 19)
  assert_eq(@cubical.cubemap_all_with_swaps(3, 2).length(), 22)
  assert_eq(@cubical.cubemap_all_full(3, 2).length(), 25)
  // 生成律：face/degen 的 BFS 閉包恰好是標準 □
  assert_eq(@cubical.cubemap_generated(2, 2).length(), 13)
  // 面數與 Euler 特徵數：Q³ 的 k 維面 = C(3,k)2^(3-k) = 8/12/6/1，χ = 1
  assert_eq(@cubical.cube_face_count(3, 1), 12)
  assert_eq(@cubical.cube_faces_enum(3, 1).length(), 12)
  assert_eq(@cubical.cube_euler(3), 1)
  assert_true(@cubical.cube_euler_enum_check(3))
  // Gray code：2³ 個頂點構成 Hamiltonian 圈
  assert_true(@cubical.gray_hamiltonian_check(3))
  assert_eq(@cubical.cube_points_gray(3).length(), 8)
}
```

```mbt check
test "README K2: Kan 填充 — transport 就是解開放盒" {
  let a = @univalence.fin("A", 3)
  let b = @univalence.fin("B", 3)
  let sigma = @univalence.bij_make(3, [1, 2, 0]).unwrap() // 3-循環 (0 1 2)
  let p = @univalence.ua_fin(sigma, a, b).unwrap()
  // 開放盒（top 缺失）⇒ 填充體由 glue 的消除規則給出：1 ↦ σ(1) = 2
  let fill = @cubical.kan_fill_el({ path: p, bottom: 1, top: None }).unwrap()
  assert_eq(fill.top, 2)
  assert_true(fill.compatible)
  // 閉盒：只有相容的上邊才有解
  assert_true(@cubical.kan_fill_el({ path: p, bottom: 1, top: Some(2) }) is Some(_))
  assert_true(@cubical.kan_fill_el({ path: p, bottom: 1, top: Some(0) }) is None) // 不相容 ⇒ 無解
  // 元素越界 ⇒ 盒不成立（不會假裝填得出來）
  assert_true(@cubical.kan_fill_el({ path: p, bottom: 5, top: None }) is None)
  // 運輸的函子性：沿 q∘p 傳輸 = 兩次填充串接
  let q = @univalence.ua_fin(@univalence.bij_make(3, [2, 0, 1]).unwrap(), b, a).unwrap()
  assert_eq(@cubical.kan_compose(p, q, 1).unwrap(), @univalence.upath_transport(@univalence.upath_trans(p, q).unwrap(), 1))
  // refl ⇒ 恒等填充
  let r = @univalence.upath_refl(a)
  assert_eq(@cubical.kan_fill_el({ path: r, bottom: 2, top: None }).unwrap().top, 2)
  // 窮盡驗證（card = 3：198 次原子比較，7 條定律全 true）
  let kp = @cubical.kan_proof(3)
  assert_eq(kp.card, 3)
  assert_eq(kp.checks, 198)
  assert_true(kp.exists)
  assert_true(kp.unique_iff)
  assert_true(kp.universal)
  assert_true(kp.functorial)
  assert_true(kp.roundtrip)
  assert_true(kp.refl_law)
  assert_true(kp.ua_beta)
  assert_true(@cubical.kan_holds(3))
}
```

```mbt check
test "README K3: cubical NBE — 項、重寫、正規化、判斷相等" {
  // Lehmer 排名/反排名互逆：S₃ ≅ [0,6)
  assert_true(@cubical.lehmer_bijection_check(3))
  // perm_from_lehmer 回傳 Bij?（秩超出 [0,n!) 時為 None）
  assert_true(@cubical.perm_from_lehmer(3, 6) is None) // 6 ≥ 3! ⇒ 無此置換
  let s1 = @cubical.perm_from_lehmer(3, 1).unwrap()
  assert_eq(s1.fwd.length(), 3)
  assert_eq(s1.fwd[1], 2) // 秩 1 的置換 = [0,2,1]
  assert_eq(@univalence.lehmer_code(s1), 1) // 排名/反排名互逆
  // 項與可讀表示
  let t = @cubical.CTransport(@cubical.CUa(@cubical.CSigma(3)), @cubical.CElem(1))
  assert_true(@cubical.cterm_show(t).contains("transport"))
  assert_true(@cubical.cterm_size(t) > 1)
  // 求値：σ₃ = (0 1 2) 把 el(1) 送到 el(2)
  assert_true(@cubical.ceval(t, 3) is Some(_))
  // 重寫至不動點：2 步，範式是 el(2)
  let rw = @cubical.crewrite(t, 3, 10)
  assert_eq(rw.1, 2) // 步數 = 終止性的見證
  assert_true(@cubical.cterm_eq(rw.0, @cubical.CElem(2)))
  // NBE：eval-then-reify，與重寫結果一致
  assert_true(@cubical.cterm_eq(@cubical.cnorm(t, 3), @cubical.CElem(2)))
  // 可決定的判斷相等
  assert_true(@cubical.judgmental_eq_ct(t, @cubical.CElem(2), 3))
  assert_true(!@cubical.judgmental_eq_ct(@cubical.CUa(@cubical.CSigma(1)), @cubical.CRefl, 3))
  // R1：transport(refl, x) → x
  let r1 = @cubical.CTransport(@cubical.CRefl, @cubical.CElem(0))
  assert_true(@cubical.cterm_eq(@cubical.crewrite(r1, 3, 10).0, @cubical.CElem(0)))
  // R6：sym(sym p) → p
  let r6 = @cubical.CSym(@cubical.CSym(@cubical.CUa(@cubical.CSigma(3))))
  assert_true(@cubical.cterm_eq(@cubical.crewrite(r6, 3, 10).0, @cubical.CUa(@cubical.CSigma(3))))
}
```

```mbt check
test "README K3: NBE 的 15 條性質與終止性" {
  // (card=3, depth=1, sigma_limit=6, max_steps=2)：230 個項、3,158 次檢查
  let pf = @cubical.nbe_proof(3, 1, 6, 2)
  assert_eq(pf.card, 3)
  assert_eq(pf.terms, 230)
  assert_eq(pf.checks, 3158)
  assert_true(pf.rewrite_sound) // 每步重寫都保語義
  assert_true(pf.norm_sound) // eval(norm t) = eval t
  assert_true(pf.agrees) // norm(rewrite t) = norm t（良型項）
  assert_true(pf.idempotent)
  assert_true(pf.normal_forms)
  assert_true(pf.terminated) // 全部項都在 max_steps 內終止
  assert_true(pf.measure_ok) // 勢函數 (Φ₁,Φ₂) 逐步字典序遞減
  assert_true(pf.reassoc_sound) // R8 保語義且保大小（但不參與重寫）
  assert_true(pf.equivalence) // CSigma(k) 確實是已驗證等價
  assert_true(pf.eq_sound)
  assert_true(pf.eq_complete)
  assert_true(@cubical.nbe_holds(3, 1, 6, 2))
  // 枚舉項數：深度 ≤1、σ 秩 <6 ⇒ 230 個
  assert_eq(@cubical.cterms_upto(3, 1, 6).length(), 230)
}
```

```mbt check
test "README: 公理審計與一行摘要" {
  assert_eq(@cubical.cubical_axiom_count(), 0)
  // cubical_summary = cubical_line(K1) + K2 的逐條定律
  let s = @cubical.cubical_summary(3)
  assert_true(s.contains("K1 dim<=3"))
  assert_true(s.contains("faithful=true"))
  assert_true(s.contains("C1C2C3=true"))
  assert_true(s.contains("generated=true"))
  assert_true(s.contains("K2 card=3"))
  assert_true(s.contains("exists=true"))
  assert_true(s.contains("uaβ=true"))
  // 含 K1/K2/K3 與 axioms=0 的完整一行由 root 的 @axiom.cubical_demo() 組合而成
}
```

## 8. 測試

| 檔案 | 內容 |
|---|---|
| `cubical_test.mbt` | 12 個黑盒測試：K1（座標約定、C1/C2/C3、計數、生成律、面／Euler／Gray）· K2（開放盒／閉盒／越界／函子性／7 條定律）· K3（Lehmer 雙射、重寫、NBE、判斷相等、終止性、守衛反例） |
| 本檔 §7 | 6 個 `mbt check` 文件測試，由 `moon test` 執行 |

```bash
moon test cubical   # 單 package
```

## 9. 去邊

- **`univalence/`** — `Fin` / `Bij` / `UPath`（帶 glue 嘅宇宙路徑）：K2 嘅盒同 K3 嘅 `CSigma` 都由佢哋提供
- **`hott_core/`** — `Path` / `Equiv` / `ua`（舊 API）：K2 嘅 `kan_transport_code` 係佢嘅真版本
- **`hott_algorithms/`** — H1 `cubical_transport_kan` 直接調用 `kan_fill_el`
- **`docs/CUBICAL.md`** — K1–K3 嘅完整推導（589 行）：座標約定、三條計數公式嘅證明、
  守衛嘅必要性反例、終止性證明、實測數據、附錄（CCHM 2016／Orton–Pitts 2016／
  Angiuli 2019／Sterling–Angiuli–Gratzer NBE）同 §5.4 嘅 `moon fmt` 警告
