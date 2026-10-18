# `structures` — 原有數學結構（8 個檔案 · 141 個公開 API · 零 HoTT 依賴）

> **package** `axiom/axiom/structures` · **alias** `@structures` · **依賴**：無（同 `hott_core` 一樣係依賴圖嘅根）
> **檔案**：`category.mbt`(98) · `functor.mbt`(106) · `vect.mbt`(175) · `topos.mbt`(115) · `linear.mbt`(88) · `homotopy.mbt`(158) · `groupoid.mbt`(160) · `algorithms.mbt`(225)
> **測試**：`structures_test.mbt`（11 個黑盒）· `structures_wbtest.mbt`（6 個白盒不變量）
> **公開 API**：141 項 = 37 struct + 6 enum + 1 trait + 97 fn · **本 package 引入的公理：0**

## 1. 呢個資料夾做乜

呢度係**上游原有嘅數學結構庫**（HoTT 重構之前嘅部分），八個主題各自一個檔案，
全部係純計算、冇任何公理，亦**唔依賴任何 HoTT package**——所以佢可以獨立編譯，
同時亦係 `hott_redefine/`（把佢哋逐項 HoTT 化）嘅輸入。

| 檔案 | 主題 | 主要內容 |
|---|---|---|
| `category.mbt` | 範疇論核心 | `ObjTag` · 終端／離散範疇 · 恆等函子 · 自然變換（自然性方塊）· Yoneda `Hom(A,-)` |
| `functor.mbt` | 三大函子 | `Equivalence`（三角恆等式）· `Free`（自由代數 + fold）· `FreeTrie`（A1 嘅共享存储）· `FlatFunctor`（平坦函子／濾餘極限） |
| `vect.mbt` | 線性代數 | 兩個域（`DoubleField` ZST · `IntModField`）· `Vect[K]` · `SparseVect[K]` · `LinMap[K]` · 矩陣向量乘／張量積／直和／對偶配對／隨機投影 |
| `topos.mbt` | 拓撲與 Topos | `Topology`（開集族）· `ContinuousMap` · `Site`（Grothendieck 覆蓋）· `Sheaf[F]` · `Omega`（子物件分類器）· 冪物件 · `Presheaf`/`sheafify` · 幾何態射 · Mitchell-Bénabou 語言 |
| `linear.mbt` | 線性邏輯 | `Linear[X]`（一次性資源）· `Lolli[A,B]`（$A \multimap B$）· `Tensor`（$\otimes$）· `With`（$\&$）· `Plus`（$\oplus$）· `Bang`（$!A$ 指數）· `Clone` trait · `Dual` · `ProofNet` |
| `homotopy.mbt` | 同倫代數／DAG | `Simplex` · `SimplicialOp`（face/degeneracy）· `SSet`（單純集合）· `ModelCat`（弱等價 + 2-of-3）· `HomotopyGroup`/$\pi_n$ · `AnimatedRing` · `CotangentComplex`（Betti 數 + Euler + 形變障礙）· hocolim |
| `groupoid.mbt` | 群胚／2-群 | `Morph`（帶逆標籤）· `Groupoid`（連通分量）· `CrossedModule`（Peiffer 恆等式 + $\pi_0,\pi_1$）· `TwoGroupElem`（半直積乘法）· `orbit_reduction` · `GroupoidCache` |
| `algorithms.mbt` | **衍生演算法 A1–A10** | 用上面嘅抽象把複雜度降下來，見 §5 |

## 2. 公理

**無。** 呢個 package 冇 `axiom` 宣告，亦冇引用任何 HoTT 公理：所有結構都係具體資料結構
（陣列、Map、整數碼），所有「定律」都係可執行嘅判定程序（`check_triangle`、`check_peiffer`、
`is_groupoid`、`two_of_three`、`is_correct`、`is_continuous`）。

> **誠實邊界**：呢度嘅「範疇」「Topos」「模型範疇」都係**有限組合模型**，唔係類型論意義下嘅
> 完整結構。具體簡化清單見 §6（包括一個**已知缺陷**：A1 嘅記憶化鍵會碰撞）。
> MoonBit 唔係證明助理，冇任何機器檢查嘅形式證明。

## 3. 定義（類型）

### 3.1 `category.mbt`（6）

| 名稱 | 內容 | 欄位 |
|---|---|---|
| `ObjTag` | 物件嘅名字（全庫通用嘅輕量標籤） | `struct ObjTag(String)` |
| `TerminalCat` | 終端範疇 $\mathbf{1}$：一個物件、一個態射 | `struct {}`（ZST；`impl Category` 給 `cat_id = 0`） |
| `DiscreteCat` | 離散範疇：只有恆等態射 | `{ objs : Array[ObjTag] }` |
| `IdFunctor` | 恆等函子 | `struct {}`（ZST） |
| `NatTrans` | 自然變換 $\alpha : F \Rightarrow G$，滿足自然性方塊 $G(f)\circ\alpha_A = \alpha_B\circ F(f)$ | `{ components : Array[(ObjTag, Int)] }` |
| `HomFunctor` | Yoneda：$Hom(A,-)$ | `{ source : ObjTag }` |

### 3.2 `functor.mbt`（4）

| 名稱 | 內容 | 欄位／變體 |
|---|---|---|
| `Equivalence` | 等價函子：$\eta$ 與 $\varepsilon$ 以互逆整數對模擬 | `{ unit : Array[(ObjTag, Int, Int)]; counit : Array[(ObjTag, Int, Int)] }` |
| `Free[X]` | 自由代數（自由么半群嘅泛化）：點構造 + 運算構造 | `enum { Return(X); Op(String, Array[Free[X]]) }` |
| `FreeTrie[X]` | A1 嘅共享存储：以字串鍵索引 `Free[X]` | `{ trie : Map[String, Free[X]] }` |
| `FlatFunctor` | 平坦函子＝濾餘極限 $\mathsf{colim}_i\,Hom(A_i,-)$ 嘅錐 | `{ active : Array[ObjTag]; cocone : Map[String, Int] }` |

### 3.3 `vect.mbt`（5）

| 名稱 | 內容 | 欄位 |
|---|---|---|
| `DoubleField` | $\mathbb{R}$ 嘅域運算（**ZST**，編譯期被常量傳播消除） | `struct {}` |
| `IntModField` | $\mathbb{Z}/m$ | `{ modulus : Int }` |
| `Vect[K]` | $K$ 上嘅向量空間 | `{ dim : Int; data : Array[K] }` |
| `SparseVect[K]` | 稀疏向量（只存非零項） | `{ dim : Int; entries : Array[(Int, K)] }` |
| `LinMap[K]` | 線性映射＝矩陣 | `{ rows : Int; cols : Int; mat : Array[Array[K]] }` |

### 3.4 `topos.mbt`（7）

| 名稱 | 內容 | 欄位／變體 |
|---|---|---|
| `Topology` | 拓撲：點集 + 開集族 | `{ points : Array[String]; opens : Array[Array[String]] }` |
| `ContinuousMap` | 連續映射：開集嘅原像仍為開集 | `{ domain : Topology; codomain : Topology; mapping : Map[String, String] }` |
| `Site` | Grothendieck site：物件 + 覆蓋族 | `{ objects : Array[ObjTag]; covers : Map[String, Array[Array[ObjTag]]] }` |
| `Sheaf[F]` | 層：site 上嘅函子 + 黏合見證 | `{ site : Site; functor : F; gluing_witness : Array[Bool] }` |
| `Omega` | 子物件分類器 $\Omega$（古典二値） | `enum { False, True }` |
| `Presheaf[P]` | 預層 | `{ data : P }` |
| `GeometricMorphism[FStar, FStar2]` | 幾何態射 $f^* \dashv f_*$ | `{ inverse_image : FStar; direct_image : FStar2 }` |

### 3.5 `linear.mbt`（9）

| 名稱 | 內容 | 欄位／變體 |
|---|---|---|
| `Linear[X]` | 一次性資源（用完即棄） | `{ val : X; mut consumed : Bool }` |
| `Lolli[A, B]` | 線性蘊含 $A \multimap B$ | `{ func : (A) -> B }` |
| `Tensor[A, B]` | 張量積 $A \otimes B$ | `{ left : A; right : B }` |
| `With[A, B]` | 加法連接 $A \& B$（被動選擇） | `enum { Fst(A); Snd(B) }` |
| `Plus[A, B]` | 加法析取 $A \oplus B$（主動選擇） | `enum { Inl(A); Inr(B) }` |
| `Bang[A]` | 指數 $!A$（可複製／可丟棄） | `{ val : A }` |
| `Clone` | 可複製嘅 trait | `trait Clone { fn clone(Self) -> Self }`；`impl Clone for Int`（**冇 `pub` ⇒ package 私有**，見 §6） |
| `Dual[A]` | 對偶 $A^\perp$ | `{ lolli : Lolli[A, Unit] }` |
| `ProofNet` | 證明網（線性邏輯嘅正確性判準） | `{ nodes : Array[String]; axiom_links : Array[(Int, Int)] }` |

### 3.6 `homotopy.mbt`（8）

| 名稱 | 內容 | 欄位／變體 |
|---|---|---|
| `Simplex` | 單純形 $\Delta^n$ | `{ dim : Int }` |
| `SimplicialOp` | 單純算子：面映射／退化映射 | `enum { Face(Int); Degeneracy(Int) }` |
| `SSet` | 單純集合：逐維度嘅單純形陣列 | `{ simplices : Array[Array[Int]] }` |
| `ModelLabel` | 模型範疇嘅態射標籤 | `enum { WeakEquiv; Cofibration; Fibration; TrivCof; TrivFib; Any }` |
| `ModelCat` | 模型範疇（弱等價／上纖維／纖維三族） | `{ weaks, cofs, fibs : Array[(Int, Int)] }` |
| `HomotopyGroup` | $\pi_n$ | `{ n : Int; rank : Int }` |
| `AnimatedRing` | 動畫化環（導出代數幾何）：基環 + 截斷 + 逐層維度 | `{ base : String; trunc : Int; levels : Array[Int] }` |
| `CotangentComplex` | 餘切複形 $L_{A/k}$ | `{ ring : AnimatedRing; betti : Array[Int] }` |

### 3.7 `groupoid.mbt`（5）

| 名稱 | 內容 | 欄位 |
|---|---|---|
| `Morph` | 群胚態射（帶逆嘅標籤） | `{ src, dst, label, inv_label : String }` |
| `Groupoid` | 群胚：每個態射都有逆 | `{ objects : Array[String]; morphs : Array[Morph] }` |
| `CrossedModule` | 交叉模 $(H \xrightarrow{\partial} G, \triangleright)$ | `{ h_order, g_order : Int; boundary : Array[Int]; action : Array[Array[Int]] }` |
| `TwoGroupElem` | 2-群元素 $(g, h)$ | `{ g : Int; h : Int }` |
| `GroupoidCache[V]` | 群胚商化緩存：以連通分量嘅規範代表元為鍵 | `{ store : Map[String, V]; groupoid : Groupoid }` |

## 4. 函數與方法（97）

### 4.1 `category.mbt`

| 名稱 | 內容 |
|---|---|
| `DiscreteCat::make(objs)` | 離散範疇 |
| `NatTrans::make(comps)` | 由分量表構造自然變換 |
| `NatTrans::component(obj)` | 取某物件上嘅分量（`Int?`） |
| `is_natural_square(nt, f_dom, f_cod, f_image, g_image)` | **自然性方塊**：$G(f)\circ\alpha_A = \alpha_B\circ F(f)$，以整數加法表化為 `(g_image + α_A) == (α_B + f_image)` |
| `HomFunctor::make(source)` | Yoneda 嵌入 $Hom(A,-)$ |
| `HomFunctor::hom_set(target)` | $Hom(A,B)$：同一物件 ⇒ `[0]`（恆等），否則 `[]` |

### 4.2 `functor.mbt`

| 名稱 | 內容 |
|---|---|
| `Equivalence::make(unit, counit)` | 由 $\eta$／$\varepsilon$ 表構造等價 |
| `Equivalence::check_triangle()` | **三角恆等式**：$\eta$ 與 $\varepsilon$ 逐項互逆 |
| `transport_via_equivalence(eq, x)` | 沿等價傳輸元素 —— **佔位**：恆回 `x`（見 §6） |
| `Free::fold(ret, op)` | 自由代數嘅泛性：給 `Return` 與 `Op` 嘅解釋即得唯一同態 |
| `FreeTrie::empty()` / `insert(key, v)` / `lookup(key)` | A1 嘅共享存储 |
| `concat_free(a, b)` | 陣列串接（自由么半群嘅乘法） |
| `FlatFunctor::make(active)` | 由活躍物件集構造平坦函子 |
| `FlatFunctor::is_flat()` | `active` 非空（**簡化判準**，見 §6） |
| `FlatFunctor::advance(obj, val)` | 推進錐（A2 嘅增量更新） |
| `FlatFunctor::eval(obj)` | 求値錐（`Int?`） |
| `flat_preserves_limit_example(flat, objs)` | 平坦函子保有限極限嘅示例：逐物件求値 |

### 4.3 `vect.mbt`

| 名稱 | 內容 |
|---|---|
| `IntModField::make(m)` | $\mathbb{Z}/m$ |
| `Vect::zeros(dim, zero)` / `Vect::from_array(arr)` | 零向量／由陣列構造 |
| `SparseVect::from_dense(v, is_zero)` / `to_dense(zero)` | 稠密 ↔ 稀疏互轉（A4 嘅基礎） |
| `LinMap::zeros(rows, cols, zero)` / `LinMap::identity(n, zero, one)` | 零矩陣／單位矩陣 |
| `apply_double(lin, v, field)` | $\mathbb{R}$ 上嘅矩陣向量乘 |
| `apply_sparse_double(lin, sv, field)` | 稀疏版（只遍歷非零項） |
| `tensor_double(v, w, field)` | 張量積 $V \otimes W$，$\dim = \dim V \cdot \dim W$ |
| `direct_sum(a, b)` | 直和 $V \oplus W$ |
| `pairing_double(cov, v, field)` | 對偶配對 $\langle cov, v\rangle$（維度唔同會 `assert_eq` 失敗） |
| `random_projection(dim_in, dim_out, seed)` | 雜湊驅動嘅 $\{-1,0,1\}$ 隨機投影（高維降維，A 高維管線用） |

### 4.4 `topos.mbt`

| 名稱 | 內容 |
|---|---|
| `Topology::discrete(points)` | 離散拓撲：`opens = [[]] + 單點集 + 全集` |
| `Topology::indiscrete(points)` | 平凡拓撲：`opens = [[], points]` |
| `Topology::is_open(s)` | 判定開集（逐陣列精確比對） |
| `ContinuousMap::is_continuous()` | 連續性：每個開集嘅原像都係開集 |
| `contractible_reduction(topo)` | 可縮化：$\le 1$ 點則原樣，否則塌成 `indiscrete(["⋆"])` |
| `Site::make(objects)` | 由物件集構造 site（覆蓋族初始為空） |
| `Sheaf::make(site, functor)` | 層（`gluing_witness` 初始為空） |
| `omega_and` / `omega_or` / `omega_implies` | $\Omega$ 嘅 Heyting 代數運算（古典二値：`implies(True, False) = False`，其餘 `True`） |
| `characteristic(set, pred, x)` | 特徵態射 $\chi : X \to \Omega$ |
| `power_object(a)` | 冪物件 —— **簡化**：只回 `[[], a]`（見 §6） |
| `sheafify(psh)` | 層化 —— **佔位**：恆等（見 §6） |
| `mitchell_benabou_eval(formula, ctx)` | Mitchell-Bénabou 語言求値 —— **佔位**：忽略 `ctx`，回傳 `formula`（見 §6） |

### 4.5 `linear.mbt`

| 名稱 | 內容 |
|---|---|
| `Linear::make(x)` / `Linear::consume()` | 包裝／**一次性消耗**資源 |
| `Lolli::make(f)` / `Lolli::apply(x)` | $A \multimap B$：把 `Linear[A]` 消耗成 `Linear[B]` |
| `compose_lolli(f, g)` | $(A \multimap B) \to (B \multimap C) \to (A \multimap C)$ |
| `linear_batch(arr)` | 批量消耗 `Array[Linear[A]] → Array[A]` |
| `Tensor::make(a, b)` / `Tensor::split()` | $\otimes$ 嘅构造與消構 |
| `Bang::make(x)` / `derelict()` / `duplicate()` | $!A$：dereliction $!A \to A$、複製 $!A \to !A \otimes !A$ |
| `ProofNet::is_correct()` | 證明網正確性：公理鏈唔可以連接同一個節點 |

### 4.6 `homotopy.mbt`

| 名稱 | 內容 |
|---|---|
| `SSet::empty()` / `standard_simplex(n)` | 空單純集合／標準單形 $\Delta^n$（第 $k$ 層有 $C(n+1,k+1)$ 個） |
| `SSet::num_simplices(dim)` | 某維度嘅單純形個數 |
| `ModelCat::is_weak_equiv(f)` | 查表：`f` 是否喺 `weaks` 內 |
| `two_of_three(weaks, f, g, comp)` | **2-of-3 公理**：$f,g,g\circ f$ 之中有兩個係弱等價則第三個都係 |
| `pi_n(s, n)` | $\pi_n$：$n=0$ ⇒ 0-單純形個數；否則 $\chi(s) \bmod (n+2)$（**簡化模型**，見 §6） |
| `AnimatedRing::polynomial(base, vars)` | 多項式環 $k[x_1..x_n]$（`levels = [vars]`） |
| `AnimatedRing::tensor_product(a, b)` | 張量積：逐層**相加**（$k[x_1..x_m] \otimes k[y_1..y_n]$ 有 $m+n$ 個變數），層數取兩者嘅最大值 |
| `cotangent_of_poly(vars)` | $L_{k[x]/k}$：`betti = [vars]` |
| `CotangentComplex::euler()` | Betti 數嘅交錯和 $\Sigma (-1)^i \beta_i$ |
| `deformation_obstruction(cot)` | 形變障礙：$\chi = 0$ ⇒ `"unobstructed (光滑)"`，否則 `"obstruction rank N"` |
| `hocolim_via_replacement(s)` | 同倫餘極限：逐層做「替換」（每個元素複製一份 +1000） |

### 4.7 `groupoid.mbt`

| 名稱 | 內容 |
|---|---|
| `Groupoid::discrete(objs)` | 離散群胚：只有恆等態射 |
| `Groupoid::pair_groupoid(objs)` | 對群胚：任意兩物件之間恰有一條態射（連通） |
| `Groupoid::is_groupoid()` | 每個態射都搵得到逆（`src`/`dst`/`inv_label` 對應） |
| `Groupoid::connected_components()` | 連通分量（$\pi_0$） |
| `compose_paths(a, b)` | 態射複合：`a.dst != b.src` ⇒ `None` |
| `CrossedModule::trivial(h, g)` | 平凡交叉模（$\partial$ 全零、作用平凡） |
| `CrossedModule::check_peiffer()` | **Peiffer 恆等式** $\partial(x \triangleright h) = \partial(x)\,h\,\partial(x)^{-1}$ |
| `CrossedModule::pi0()` | $\pi_0 = \vert G\vert / \vert \mathrm{Im}\,\partial\vert$ |
| `CrossedModule::pi1()` | $\pi_1 = \vert \ker\partial\vert$ |
| `tensor_2group(a, b, cm)` | 2-群乘法：$g$ 分量模 $g\_order$ 相加、$h$ 分量經作用後模 $h\_order$ |
| `orbit_reduction(cm, elems)` | 軌道商化：鍵 $= (g \bmod \pi_0,\ h \bmod \max(1,\pi_1))$ |
| `GroupoidCache::make(g)` / `canonical_key(obj)` | 以連通分量嘅**首元素**為規範鍵（A9 嘅基礎） |

## 5. 衍生演算法 A1–A10（`algorithms.mbt`，14 個函數）

| 編號 | 函數 | 複雜度改善 | 內容 |
|---|---|---|---|
| **A1** | `free_rewrite_batch(terms, rule)` | $O(n^2) \to O(n\,\alpha(n))$ | 自由項批量重寫：以 `debug_string` 為鍵共享重寫結果（**鍵會碰撞，見 §6**） |
| **A2** | `sliding_flat_eval(flat, stream, window)` | $O(N) \to O(\log N)$ | 滑動窗口平坦求値：增量更新錐，逐窗口回傳 `Int?` |
| **A3** | `canonicalize_via_equivalence(eq, objs)` | — | 規範形：沿等價把物件表化成 `Map[String, ObjTag]` |
| **A4** | `fused_chain_double(ops, v, field)` | $O(n^3) \to O(nnz\cdot k)$ | 融合鏈：多個 `LinMap` 一次過作用，免中間向量 |
| | `adaptive_apply_double(lin, v, field)` | — | 自適應：按稀疏度選擇稠密／稀疏路徑 |
| **A5** | `sheaf_query_optimized(site, obj, covers)` | $O(2^n) \to O(n\log n)$ | 層查詢：以覆蓋長度為鍵去重，免重複檢查同形覆蓋 |
| **A6** | `linear_pipeline(f, g, h, x)` | — | 線性管道：三個 `Lolli` 複合後一次消耗資源 |
| | `linear_map_inplace(arr, f)` | — | 原地映射（免配置新陣列） |
| **A7** | `hocolim_parallel(s, levels)` | $O(N) \to O(\log N)$ | hocolim 並行：重複 `hocolim_via_replacement` `levels` 次（每層元素數 ×2） |
| **A8** | `jacobian_via_cotangent(cot, jacobian_full)` | — | 餘切驅動雅可比：只保留 `betti.length()` 行（截斷剪枝） |
| **A9** | `symmetric_search(groupoid, states, expand)` | $O(\vert G\vert n) \to O(\vert\pi_0\vert n)$ | 群胚對稱搜尋：BFS 时用 `GroupoidCache` 嘅規範鍵把同連通分量視為已訪問 |
| **A10** | `two_group_orbit_count(cm, elems)` | $O(\vert G\vert\vert H\vert n) \to O(\vert\pi_0\vert\vert\pi_1\vert n)$ | 2-群軌道計數：`orbit_reduction` 之後數鍵嘅個數 |
| 高維 | `high_dim_pipeline(vecs, proj, field)` | — | 隨機投影降維 + 批量套用 |
| 安全 | `checked_matmul(a, b)` | — | 維度檢查版矩陣乘：`a.cols != b.rows` ⇒ `None`（唔會靜默出錯） |

## 6. 佔位／簡化實作一覽（誠實邊界）

用之前必須知道以下項目係**簡化模型**而唔係完整數學實作。全部都有可運行嘅驗證或反例：

| 項目 | 實作 | 影響 |
|---|---|---|
| **A1 `free_rewrite_batch` 嘅記憶化鍵** | 私有 `debug_string` 把 `Return(_)` 一律映成 `"R"`、`Op(name,args)` 映成 `name + "(" + arity + ")"`，**完全唔含 payload** | ⚠️ **已知缺陷**：`Return(1)` 與 `Return(2)` 共用鍵 ⇒ 第二項會攞到第一項嘅重寫結果。§7 有可運行反例（得到 `101`，正確應為 `102`）。**使用前提**：重寫規則必須喺每個 `debug_string` 等价類內不變（即只依賴項嘅形狀、唔依賴 payload 値）。`Free[X]` 冇 `Debug`/`Show` derive，所以無法喺唔加型別約束嘅情況下造出忠實嘅鍵 |
| `transport_via_equivalence(eq, x)` | 恆回 `x` | 「沿等價傳輸」只係佔位；真正帶 glue 嘅傳輸喺 `@univalence.upath_transport` / `@cubical.kan_fill_el` |
| `power_object(a)` | 只回 `[[], a]` | 真正嘅冪物件有 $2^n$ 個子集 |
| `sheafify(psh)` | 恆等 | 冇做真正嘅層化（plus-construction） |
| `mitchell_benabou_eval(formula, ctx)` | 忽略 `ctx`，回傳 `formula` | Mitchell-Bénabou 語言只係佔位 |
| `FlatFunctor::is_flat()` | `active.length() > 0` | 冇真正驗證餘濾性（filteredness）；HoTT 版嘅判準見 `@hott_redefine.FlatHoTT::is_flat_hott` |
| `pi_n(s, n)` | $n=0$ ⇒ 0-單純形數；否則 $\chi(s) \bmod (n+2)$ | 由 Euler 特徵數**湊出**嘅秩，唔係真正嘅同倫群計算；真正嘅 $\pi_1(S^1)=\mathbb{Z}$ 喺 `@hott_theorems`（Encode-Decode） |
| `ModelCat::is_weak_equiv` / `two_of_three` | 查表 | 弱等價由輸入嘅 `weaks` 陣列**指定**，唔係由映射本身計算 |
| `Omega` | `enum { False, True }` | 古典二値，唔係一般 Topos 嘅子物件分類器（冇 Heyting 結構嘅完整驗證） |
| `HomFunctor::hom_set(target)` | 同一物件 ⇒ `[0]`，否則 `[]` | 只適用於離散／終端範疇 |
| `hocolim_via_replacement(s)` | 每元素複製一份並 `+1000` | 「替換」嘅組合模型，唔係真正嘅同倫餘極限 |
| `ContinuousMap::is_continuous` | 對 `codomain.opens` 逐一算原像再比對 | 正確但係指數級；只適合小拓撲 |
| `impl Clone for Int`（`linear.mbt:64`） | **冇加 `pub`** | package 外部（包括黑盒測試同本 README 嘅例子）會得到 `Type Int does not implement trait Clone`；trait 本身係 `pub` 嘅，只有 impl 係私有 |

## 7. 可運行例子

以下 ```mbt check``` 區塊由 `moon test` **真的編譯並執行**，數値全部實測。

```mbt check
test "README §3.1: 範疇論核心 — 自然性方塊與 Yoneda" {
  let a = @structures.ObjTag("A")
  let b = @structures.ObjTag("B")
  // 離散範疇與終端範疇都是 ZST 或純標籤容器
  let dc = @structures.DiscreteCat::make([a, b])
  assert_eq(dc.objs.length(), 2)
  // 自然變換 α : F ⇒ G 的分量
  let nt = @structures.NatTrans::make([(a, 1), (b, 2)])
  assert_eq(nt.component(a), Some(1))
  assert_eq(nt.component(@structures.ObjTag("Z")), None)
  // 自然性方塊：G(f) ∘ α_A = α_B ∘ F(f) ⇔ (g_image + α_A) == (α_B + f_image)
  assert_true(@structures.is_natural_square(nt, a, b, 0, 1)) // (1+1) == (2+0)
  assert_true(!@structures.is_natural_square(nt, a, b, 0, 5))
  // Yoneda：Hom(A,A) = [0]（恆等），Hom(A,B) = []
  let y = @structures.HomFunctor::make(a)
  assert_eq(y.hom_set(a).length(), 1)
  assert_eq(y.hom_set(b).length(), 0)
}
```

```mbt check
test "README §3.2: 三大函子 — 等價三角恆等式、Free 折疊、平坦函子" {
  // 等價：η 與 ε 互逆 ⇒ 三角恆等式成立
  let eq = @structures.Equivalence::make([(@structures.ObjTag("A"), 1, -1)], [(@structures.ObjTag("B"), 2, -2)])
  assert_true(eq.check_triangle())
  // 自由代數的泛性：fold 給出唯一同態
  let term : @structures.Free[Int] = @structures.Op("add", [@structures.Return(1), @structures.Return(2)])
  let res = term.fold(fn(x : Int) -> Int { x }, fn(name : String, args : Array[Int]) -> Int {
    if name == "add" { args[0] + args[1] } else { 0 }
  })
  assert_eq(res, 3)
  // FreeTrie：A1 的共享存储
  let trie = @structures.FreeTrie::empty()
  trie.insert("k", @structures.Return(7))
  assert_true(trie.lookup("k") is Some(_))
  assert_true(trie.lookup("missing") is None)
  assert_eq(@structures.concat_free([1, 2], [3]).length(), 3)
  // 平坦函子：advance 更新錐，eval 讀取；保有限極限的示例逐物件求値
  let flat = @structures.FlatFunctor::make([@structures.ObjTag("A"), @structures.ObjTag("B")])
  flat.advance(@structures.ObjTag("A"), 10)
  flat.advance(@structures.ObjTag("B"), 20)
  assert_true(flat.is_flat())
  assert_eq(flat.eval(@structures.ObjTag("A")), Some(10))
  assert_eq(flat.eval(@structures.ObjTag("Z")), None)
  let vals = @structures.flat_preserves_limit_example(flat, [@structures.ObjTag("A"), @structures.ObjTag("B"), @structures.ObjTag("C")])
  assert_eq(vals.length(), 3)
  assert_eq(vals[0], Some(10))
  assert_eq(vals[2], None) // C 不在錐內
}
```

```mbt check
test "README §3.3: 線性代數 — 稠密/稀疏、張量積、直和、配對、維度檢查" {
  let field = @structures.DoubleField::{} // ZST：編譯期消除
  let v = @structures.Vect::from_array([1.0, 2.0, 0.0, 4.0])
  let m = @structures.LinMap::identity(4, 0.0, 1.0)
  assert_eq(@structures.apply_double(m, v, field).data, [1.0, 2.0, 0.0, 4.0])
  // 稀疏化只留非零項
  let sv = @structures.SparseVect::from_dense(v, fn(x : Double) -> Bool { x == 0.0 })
  assert_eq(sv.entries.length(), 3)
  assert_eq(@structures.apply_sparse_double(m, sv, field).data, [1.0, 2.0, 0.0, 4.0])
  // 張量積：dim(V⊗W) = dim V · dim W，t = [1·3,1·4,1·5,2·3,2·4,2·5]
  let w = @structures.Vect::from_array([3.0, 4.0, 5.0])
  let t = @structures.tensor_double(@structures.Vect::from_array([1.0, 2.0]), w, field)
  assert_eq(t.dim, 6)
  assert_eq(t.data, [3.0, 4.0, 5.0, 6.0, 8.0, 10.0])
  assert_eq(@structures.direct_sum(@structures.Vect::from_array([1.0, 2.0]), @structures.Vect::from_array([3.0])).dim, 3)
  // 對偶配對 = 點積
  assert_eq(@structures.pairing_double(@structures.Vect::from_array([1.0, 2.0]), @structures.Vect::from_array([3.0, 4.0]), field), 11.0)
  // checked_matmul：維度不合 ⇒ None（不會靜默出錯）
  let id2 = @structures.LinMap::identity(2, 0.0, 1.0)
  assert_true(@structures.checked_matmul(id2, @structures.LinMap::identity(3, 0.0, 1.0)) is None)
  let sq = @structures.checked_matmul(id2, id2)
  assert_true(sq is Some(_))
  // 隨機投影：4 維 → 2 維
  assert_eq(@structures.random_projection(4, 2, 7).rows, 2)
  // IntModField
  assert_eq(@structures.IntModField::make(7).modulus, 7)
}
```

```mbt check
test "README §3.4: 拓撲與 Topos — 開集、連續性、Ω、site/sheaf" {
  let pts = ["p", "q"]
  let disc = @structures.Topology::discrete(pts)
  assert_true(disc.is_open([])) // 空集是開集
  assert_true(disc.is_open(["p"])) // 離散拓撲：單點集是開集
  assert_true(disc.is_open(pts))
  let ind = @structures.Topology::indiscrete(pts)
  assert_true(!ind.is_open(["p"])) // 平凡拓撲：單點集不是開集
  // 可縮化：>1 點 ⇒ 塌成單點的平凡拓撲
  let contr = @structures.contractible_reduction(disc)
  assert_eq(contr.points.length(), 1)
  // Ω 的 Heyting 運算（古典二値）
  assert_eq(@structures.omega_and(@structures.True, @structures.False), @structures.False)
  assert_eq(@structures.omega_or(@structures.False, @structures.False), @structures.False)
  assert_eq(@structures.omega_implies(@structures.True, @structures.False), @structures.False)
  assert_eq(@structures.omega_implies(@structures.False, @structures.False), @structures.True)
  // 特徵態射
  assert_eq(@structures.characteristic([1, 2, 3], fn(x : Int) -> Bool { x > 1 }, 2), @structures.True)
  assert_eq(@structures.characteristic([1, 2, 3], fn(x : Int) -> Bool { x > 1 }, 1), @structures.False)
  // site / sheaf（注意 power_object 只回 [[], a]，見 §6）
  let site = @structures.Site::make([@structures.ObjTag("U"), @structures.ObjTag("V")])
  assert_eq(site.objects.length(), 2)
  let sh = @structures.Sheaf::make(site, 0)
  assert_eq(sh.gluing_witness.length(), 0)
  assert_eq(@structures.power_object([1, 2, 3]).length(), 2)
  // 預層與層化（sheafify 是佔位的恆等）
  let psh = @structures.Presheaf::{ data: 42 }
  assert_eq(@structures.sheafify(psh).data, 42)
  // 幾何態射 f* ⊣ f*
  let gm : @structures.GeometricMorphism[Int, Int] = { inverse_image: 1, direct_image: 2 }
  assert_eq(gm.inverse_image, 1)
}
```

```mbt check
test "README §3.5: 線性邏輯 — 一次性資源、⊗、!A、證明網" {
  // Linear：consume 只能一次（consumed 旗標）
  let lin = @structures.Linear::make(5)
  assert_eq(lin.consume(), 5)
  assert_true(lin.consumed)
  // Lolli：A ⊸ B 消耗 Linear[A] 得到 Linear[B]
  let f = @structures.Lolli::make(fn(x : Int) -> Int { x + 1 })
  let g = @structures.Lolli::make(fn(x : Int) -> Int { x * 2 })
  let h = @structures.compose_lolli(f, g)
  assert_eq(h.apply(@structures.Linear::make(5)).consume(), 12) // (5+1)*2
  // A6 線性管道：三個 Lolli 複合後一次消耗
  let pipe = @structures.linear_pipeline(
    @structures.Lolli::make(fn(x : Int) -> Int { x + 1 }),
    @structures.Lolli::make(fn(x : Int) -> Int { x * 2 }),
    @structures.Lolli::make(fn(x : Int) -> Int { x - 3 }),
    @structures.Linear::make(5),
  )
  assert_eq(pipe.consume(), 9) // ((5+1)*2)-3
  // 批量消耗
  assert_eq(@structures.linear_batch([@structures.Linear::make(1), @structures.Linear::make(2)]).length(), 2)
  // Tensor：⊗ 的构造與消構
  let t = @structures.Tensor::make(1, "a")
  assert_eq(t.split(), (1, "a"))
  // !A 指數：dereliction 與複製
  let bang = @structures.Bang::make(3)
  assert_eq(bang.derelict(), 3)
  let dup = bang.duplicate()
  let (d1, d2) = dup.split() // Bang 沒有 derive(Eq)，所以比較 derelict 後的値
  assert_eq(d1.derelict(), 3)
  assert_eq(d2.derelict(), 3)
  // With / Plus
  let w : @structures.With[Int, String] = @structures.Fst(1)
  assert_true(w is @structures.Fst(_))
  let p : @structures.Plus[Int, String] = @structures.Inr("x")
  assert_true(p is @structures.Inr(_))
  // 對偶 A⊥ = A ⊸ Unit
  let d : @structures.Dual[Int] = { lolli: @structures.Lolli::make(fn(_ : Int) -> Unit { () }) }
  d.lolli.apply(@structures.Linear::make(1)).consume() |> ignore // A⊥ = A ⊸ Unit
  // 證明網：公理鏈不可連接同一節點
  assert_true(@structures.ProofNet::{ nodes: ["a", "b"], axiom_links: [(0, 1)] }.is_correct())
  assert_true(!@structures.ProofNet::{ nodes: ["a", "b"], axiom_links: [(0, 0)] }.is_correct())
  // 注：`Clone` trait 的 `impl Clone for Int`（linear.mbt:64）**冇加 `pub`**，
  // 屬於 package 私有 ⇒ 黑盒測試／README 例子入面睇唔到（`Type Int does not implement
  // trait Clone`）。要喺 package 外用，需要把它改成 `pub impl` 或直接調用底層函數。
}
```

```mbt check
test "README §3.6: 同倫代數 — 單純集合、模型範疇、πₙ、餘切複形" {
  // Δ² 的各維度單純形數 = C(3, k+1) = 3/3/1
  let s = @structures.SSet::standard_simplex(2)
  assert_eq(s.num_simplices(0), 3)
  assert_eq(s.num_simplices(1), 3)
  assert_eq(s.num_simplices(2), 1)
  assert_eq(@structures.SSet::empty().simplices.length(), 0)
  // 模型範疇：弱等價查表 + 2-of-3
  let mc = @structures.ModelCat::{ weaks: [(0, 1)], cofs: [(1, 2)], fibs: [] }
  assert_true(mc.is_weak_equiv((0, 1)))
  assert_true(!mc.is_weak_equiv((1, 2)))
  assert_true(@structures.two_of_three([(0, 1)], (0, 1), (1, 2), (0, 2)))
  // πₙ（簡化模型，見 §6）：n=0 ⇒ 0-單純形數；否則 χ mod (n+2)
  assert_eq(@structures.pi_n(s, 0).rank, 3)
  assert_eq(@structures.pi_n(s, 1).rank, 1) // χ(Δ²) = 3-3+1 = 1，1 mod 3 = 1
  // 動畫化環與餘切複形
  let r = @structures.AnimatedRing::polynomial("k", 3)
  assert_eq(r.levels.length(), 1)
  assert_eq(r.levels[0], 3)
  assert_eq(r.base, "k")
  let tp = @structures.AnimatedRing::tensor_product(r, @structures.AnimatedRing::polynomial("k", 5))
  assert_eq(tp.levels.length(), 1)
  assert_eq(tp.levels[0], 8) // k[x₁..x₃] ⊗ k[y₁..y₅] 有 3+5 = 8 個變數
  let cot = @structures.cotangent_of_poly(3)
  assert_eq(cot.euler(), 3)
  assert_eq(@structures.deformation_obstruction(cot), "obstruction rank 3")
  assert_eq(@structures.deformation_obstruction(@structures.cotangent_of_poly(0)), "unobstructed (光滑)")
  // hocolim 的替換模型：每層元素數 ×2
  let rep = @structures.hocolim_via_replacement(@structures.SSet::standard_simplex(1))
  assert_eq(rep.num_simplices(0), 4)
  // 單純算子
  let op : @structures.SimplicialOp = @structures.Face(0)
  assert_true(op is @structures.Face(_))
  let lab : @structures.ModelLabel = @structures.TrivCof
  assert_true(lab is @structures.TrivCof)
  let spx = @structures.Simplex::{ dim: 2 }
  assert_eq(spx.dim, 2)
}
```

```mbt check
test "README §3.7: 群胚與 2-群 — 連通分量、Peiffer、π₀/π₁" {
  // 對群胚：連通；離散群胚：每個物件一個分量
  let g = @structures.Groupoid::pair_groupoid(["a", "b", "c"])
  assert_true(g.is_groupoid())
  assert_eq(g.connected_components().length(), 1)
  assert_eq(g.connected_components()[0].length(), 3)
  let d = @structures.Groupoid::discrete(["a", "b"])
  assert_eq(d.connected_components().length(), 2)
  assert_true(d.is_groupoid())
  // 態射複合：dst 與 src 不合 ⇒ None
  let m1 = @structures.Morph::{ src: "a", dst: "b", label: "f", inv_label: "f⁻¹" }
  let m2 = @structures.Morph::{ src: "b", dst: "c", label: "g", inv_label: "g⁻¹" }
  let comp = @structures.compose_paths(m1, m2)
  assert_true(comp is Some(_))
  assert_eq(comp.unwrap().src, "a")
  assert_eq(comp.unwrap().dst, "c")
  assert_true(@structures.compose_paths(m1, m1) is None)
  // 交叉模：Peiffer 恆等式、π₀ = |G|/|Im ∂|、π₁ = |Ker ∂|
  let cm = @structures.CrossedModule::trivial(2, 4)
  assert_true(cm.check_peiffer())
  assert_eq(cm.pi0(), 4)
  assert_eq(cm.pi1(), 2)
  // 2-群乘法與軌道商化
  let e1 = @structures.TwoGroupElem::{ g: 1, h: 1 }
  let e2 = @structures.TwoGroupElem::{ g: 2, h: 0 }
  assert_eq(@structures.tensor_2group(e1, e2, cm).g, 3) // (1+2) mod 4
  let orbits = @structures.orbit_reduction(cm, [e1, e2, @structures.TwoGroupElem::{ g: 5, h: 3 }])
  assert_true(orbits.length() >= 1)
  // GroupoidCache：以連通分量的首元素為規範鍵
  let cache : @structures.GroupoidCache[Int] = @structures.GroupoidCache::make(g)
  assert_eq(cache.canonical_key("b"), "a")
  assert_eq(cache.canonical_key("c"), "a")
}
```

```mbt check
test "README §5: 衍生演算法 A1-A10（含 A1 的已知缺陷反例）" {
  // A1 自由項批量重寫：輸出與輸入等長
  let terms = [@structures.Return(1), @structures.Op("add", [@structures.Return(1), @structures.Return(2)]), @structures.Return(1)]
  let id_rule = fn(t : @structures.Free[Int]) -> @structures.Free[Int] { t }
  assert_eq(@structures.free_rewrite_batch(terms, id_rule).length(), 3)
  // ⚠️ A1 的記憶化鍵碰撞（見 §6）：Return(1) 與 Return(2) 的鍵都是 "R"
  let plus100 = fn(t : @structures.Free[Int]) -> @structures.Free[Int] {
    match t {
      @structures.Return(x) => @structures.Return(x + 100)
      @structures.Op(name, args) => @structures.Op(name, args)
    }
  }
  let payload = fn(t : @structures.Free[Int]) -> Int {
    t.fold(fn(x : Int) -> Int { x }, fn(_ : String, args : Array[Int]) -> Int { args[0] })
  }
  let buggy = @structures.free_rewrite_batch([@structures.Return(1), @structures.Return(2)], plus100)
  assert_eq(payload(buggy[0]), 101)
  assert_eq(payload(buggy[1]), 101) // ← 應為 102；第二項拿到了第一項的緩存結果
  assert_eq(payload(plus100(@structures.Return(2))), 102) // 直接套用規則才是對的
  // A2 滑動窗口平坦求値
  let flat = @structures.FlatFunctor::make([])
  let stream = [(@structures.ObjTag("A"), 1), (@structures.ObjTag("B"), 2), (@structures.ObjTag("A"), 3)]
  let win = @structures.sliding_flat_eval(flat, stream, 2)
  assert_eq(win.length(), 3)
  assert_eq(win[0], Some(1))
  assert_eq(win[2], Some(3))
  // A3 規範形
  let eq = @structures.Equivalence::make([(@structures.ObjTag("A"), 1, -1)], [(@structures.ObjTag("B"), 2, -2)])
  assert_eq(@structures.canonicalize_via_equivalence(eq, [@structures.ObjTag("A"), @structures.ObjTag("B")]).length(), 2)
  // A4 融合鏈 = 逐個套用（結果相同，但免中間向量）
  let field = @structures.DoubleField::{}
  let v = @structures.Vect::from_array([1.0, 2.0])
  let idm = @structures.LinMap::identity(2, 0.0, 1.0)
  assert_eq(@structures.fused_chain_double([idm, idm], v, field).data, [1.0, 2.0])
  assert_eq(@structures.adaptive_apply_double(idm, v, field).data, [1.0, 2.0])
  // A5 層查詢去重
  let site = @structures.Site::make([@structures.ObjTag("U")])
  assert_true(@structures.sheaf_query_optimized(site, @structures.ObjTag("U"), [[@structures.ObjTag("U")], [@structures.ObjTag("U"), @structures.ObjTag("V")]]))
  // A6/A7 線性原地映射 與 hocolim 並行（每層 ×2）
  let arr = [1, 2, 3]
  @structures.linear_map_inplace(arr, fn(x : Int) -> Int { x * 10 })
  assert_eq(arr.length(), 3) // 原地映射：長度不變，內容逐項檢查
  assert_eq(arr[0], 10)
  assert_eq(arr[1], 20)
  assert_eq(arr[2], 30)
  assert_eq(@structures.hocolim_parallel(@structures.SSet::standard_simplex(1), 2).num_simplices(0), 8)
  // A8 餘切驅動的截斷剪枝：betti.length() = 1 ⇒ 3 行的雅可比只留 1 行
  assert_eq(@structures.jacobian_via_cotangent(@structures.cotangent_of_poly(2), [[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]]).length(), 1)
  // A9 群胚對稱搜索：同連通分量的狀態被視為已訪問 ⇒ 只回起點
  let g = @structures.Groupoid::pair_groupoid(["a", "b"])
  let found = @structures.symmetric_search(g, ["a"], fn(_ : String) -> Array[String] { ["b"] })
  assert_eq(found.length(), 1)
  assert_eq(found[0], "a")
  // A10 2-群軌道計數：鍵 = (g mod π₀, h mod π₁) ⇒ (0,0),(1,1),(0,0) 共 2 個軌道
  let cm = @structures.CrossedModule::trivial(2, 4)
  let elems = [@structures.TwoGroupElem::{ g: 0, h: 0 }, @structures.TwoGroupElem::{ g: 1, h: 1 }, @structures.TwoGroupElem::{ g: 4, h: 2 }]
  assert_eq(@structures.two_group_orbit_count(cm, elems), 2)
  // 高維管線：4 維 → 隨機投影 → 2 維
  let hd = @structures.high_dim_pipeline([@structures.Vect::from_array([1.0, 2.0, 3.0, 4.0])], @structures.random_projection(4, 2, 7), field)
  assert_eq(hd[0].dim, 2)
}
```

## 8. 測試

| 檔案 | 內容 |
|---|---|
| `structures_test.mbt` | 11 個黑盒測試：Vect（恆等／稀疏／張量／直和）· Free fold · 平坦函子 · 等價三角 · $\Omega$ · 群胚連通性 · 2-群交叉模 · 線性邏輯 · 單純集合與 Euler · 融合鏈 |
| `structures_wbtest.mbt` | 6 個**白盒**測試（可訪問私有成員）：內部不變量 |
| 本檔 §7 | 8 個 `mbt check` 文件測試，由 `moon test` 執行 |

```bash
moon test structures   # 單 package（含 README 的 mbt check 例子）
```

## 9. 去邊

- **`hott_redefine/`** — 把呢度每個結構逐項加上 h-層次（`HoTTCat`、`FreeHoTT`、`FlatHoTT`、`VectHoTT`、`InfTopos`、`LinearHoTT`、`hott_sphere`、`crossed_to_hott`、`orbit_hott`）
- **`hott_algorithms/`** — H3 `truncated_orbit_search` 調用呢度嘅 `two_group_orbit_count`
- **`hott_theorems/`** — 真正嘅 $\pi_1(S^1) = \mathbb{Z}$（代替呢度簡化嘅 `pi_n`）
- **`univalence/`** — 真正帶 glue 嘅傳輸（代替呢度佔位嘅 `transport_via_equivalence`）
- **root `axiom.mbt`** — `demo_pipeline()` / `high_dim_demo()` 把呢度嘅結構串成整合管線
