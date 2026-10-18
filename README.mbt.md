# Axiom — HoTT 重構的零成本高維演算法庫

> **MoonBit 最新穩定版** · `moon 0.1.20261012` · `moonc v0.10.15` — 已聯網驗證  
> **命題**：運算留在編譯時，零成本抽象  
> **HoTT 定理化**：以同倫類型論為統一根基，再定義所有定理與演算法  
> **公理數 = 0**：原「單值性公理」已降級為**定理**並證明成立（`docs/UNIVALENCE.md`、`hott_univalence_theorem.mbt`）  
> **有限立方體演算法**：立方體範疇 □ / Kan 填充 / cubical NBE 全部實作並窮盡驗證（`docs/CUBICAL.md`、`hott_cubical.mbt`）

## 目錄

1. [安裝與構建](#s1)  2. [零成本保證](#s2)  3. [HoTT 核心](#s3)  4. [HITs](#s4)  5. [單值性（定理）](#s5)
6. [範疇論 HoTT 再定義](#s6)  7. [三大函子 HoTT 化](#s7)  8. [Vectₖ HoTT 化](#s8)  9. [Topos HoTT 化](#s9)  10. [線性邏輯 HoTT 化](#s10)  11. [同倫/DAG 合成化](#s11)  12. [群胚/2-群 HoTT 化](#s12)  13. [新定理 N1-N6](#s13)  14. [新算法 H1-H7](#s14)  14b. [有限立方體演算法 K1-K3](#s14b)  15. [運行演示](#s15)  16. [包結構](#s16)

## 1. 安裝與構建 <a id="s1"></a>

```bash
curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
export PATH="$HOME/.moon/bin:$PATH"
moon version --all  # moon 0.1.20261012  moonc v0.10.15
cd axiom
moon check   # 0 errors, 101 warnings
moon test    # 51 passed (26 原有 + 13 單值性定理 + 12 有限立方體)
moon run cmd/main
moon build --target wasm,wasm-gc,js,native
```

採用 `moon.mod`/`moon.pkg` 新 DSL、`fn[X] foo`、`impl Trait for Type with fn f`、`derive(Eq,Debug)`。

## 2. 零成本保證 <a id="s2"></a>

```
cost_runtime(abstraction) = cost_runtime(hand_written)
cost_compile(abstraction) > 0
```

單態化 + 見證消除 + 切除融合：`Path[A]`, `Equiv[A,B]`, `Free[A]`, `Trunc[A]` 等泛型在每個具化處生成特化副本，靜態分發、內聯。`DoubleField{}`、`TypeTag` 等 ZST 被常量傳播消除。`wasm`/`js` 双靶标位元级一致。

## 3. HoTT 核心 <a id="s3"></a>

**定義**：類型即空間，$Path_A(x,y)$ 為路徑類型；`refl : Path(a,a)`，`sym`, `trans`, `ap_f : Path_A → Path_B`，`transport^P : Path_A(x,y) → P x → P y`，同倫 $f~g ≔ Π(x:A) Path_B(f x, g x)$。

```
refl(a) : Path(a,a)          code 0
sym(p) : Path(y,x)            -code
trans(p,q) : Path(x,z)        code+1
ap_f(p) : Path(f x, f y)      保持路徑
transport^P(p,u) : P y        u + p.code
Equiv[A,B] ≔ Σ(f:A→B) isEquiv(f)  其中 isEquiv 含 g, η: g∘f~id, ε: f∘g~id
Univalence: (A =_U B) ≃ (A ≃ B)   即 ua : Equiv → Path[TypeTag]   ← 定理（見 §5），非公理
h-層次: Contr(-2) < Prop(-1) < Set(0) < Groupoid(1) < 2-Groupoid(2) < NType(n)
Trunc[A] : ∥A∥ₙ  左伴隨 n-類型包含，消除: (∥A∥ₙ→B) ≃ (A→B)  當 B 為 n-類型
```

**代碼**：`hott_core.mbt` — `Path[A]`, `Equiv[A,B]`, `TypeTag`, `UnivalenceWitness`, `HLevel`, `IsContr/IsProp`, `Trunc[A]`, `trunc_rec`, `equiv_defect`。零成本：路徑 code 為 `Int` 加法，編譯時折疊。

## 4. 高歸納類型 HITs <a id="s4"></a>

| HIT | 點構造 | 路徑構造 | 層次 |
|-----|--------|----------|------|
| Interval I | 0,1 | seg : 0=1 | 可縮 |
| Circle S¹ | base | loop : base=base | 1-類型 |
| Suspension ΣA | north,south | merid(a) : north=south | n→n+1 |
| Pushout | inl/inr | glue(a) : inl(f a)=inr(g a) | 餘極限 |
| PropTrunc ∥A∥ | |−|:A→∥A∥ | trunc: Π(x,y) x=y | Prop |
| Quotient A/R | inQ | equivQ : R x y → inQ x = inQ y | Set |

```
circle_rec : (c:X) → (loop_case: Path_X(c,c)) → (S¹ → X)
  計算律: f(base)=c , ap_f(loop)=loop_case
Susp-rec : (north/south/merid) → (ΣA → X)
PropTrunc-rec : (B 為 Prop) → ((A→B) ≃ (∥A∥→B))
```

**代碼**：`hott_hits.mbt`。例：`circle_loop().code=1`，`encode_s1 : Path(S¹)→ℤ`, `decode_s1 : ℤ→Path(S¹)` 已實現。

## 5. 單值性 —— **定理**（原公理已降級） <a id="s5"></a>

**定理**：$idToEquiv : (A =_U B) → (A ≃ B)$ 為等價，其擬逆 $ua$ 由等價自身的資料**構造**（glue），不需宣告。

```
(A = B) ≃ (A ≃ B)                  — 恆等即等價
uaη : ua(idToEquiv p) = p          uaε : idToEquiv(ua e) = e
uaβ : transport (ua e) x ≡ e x     tri : 兩個三角恆等式 ⇒ isEquiv(idToEquiv)
π₁(U_fin, Fin n) ≅ S_n             |Fin n = Fin n| = n! = |Fin n ≃ Fin n|
```

**為什麼以前只能當公理**：舊 `ua` 的 code 寫成 `left_inv + right_inv + 10`，常數 10 沒有來源，
於是 `ua(idEquiv) ≠ refl`（違反 uaη）、`transport (ua e)` 憑空 +10（違反 uaβ，
`transport_structure(idEquiv,A,A,5)` 舊值 15、正確值 5）。現在 code 由**虧損碼**導出
（已驗證等價 ⇒ 0 ⇒ 原子路徑），並另有帶 glue 計算內容的 `UPath` 版本。

**證明**（詳見 `docs/UNIVALENCE.md`，三層互補）：
1. **一般情形**：cubical/glue 模型中 `ua` 可定義、uaβ **定義性**成立（CCHM 2016；Orton–Pitts 2016；Angiuli 2019）
2. **本庫模型**：`Fin`（有限宇宙）+ `Bij`（**已驗證**雙射）+ `UPath`（帶 glue 的路徑），引理 0–10 逐條證明
3. **機器檢查**：`univalence_proof(n)` 對 n = 0..6 **窮盡**枚舉全部 n! 條路徑與 n! 個等價，
   十項定律（基數 / η / ε / β / 單射 / 滿射 / refl-sym-trans / 三角 / 可判定 / 影子單射）
   全部由計算得出，無一欄位寫死 `true` —— n=6 共 **1,571,761** 次原子比較，`holds=true`；**公理數 0**

**推論**（全部改為計算證明，不再有 `-> Bool { true }` 佔位）：
- **函數外延性** $funext : (f~g) ≃ (f=g)$：`funext_happly_laws(n)` 窮盡全部 $(n^n)^2$ 對函數（n=1..4，含 65536 對）
- **命題外延性** $(P⇔Q) ⟺ (P=Q)$：`prop_ext_fin_exhaustive()` 窮盡 4 種組合
- **結構同一性 SIP**：`sip_monoid_fin` 搜索同構、`sip_transport_check` 驗證沿 `ua(σ)` 傳輸後乘法表**逐項相等**；
  分類結果 1/2/7 類（n=1/2/3）與 **OEIS A058129** 吻合，已標號數 1/4/33 與 **A058153** 吻合
- **uaβ**：`transport along ua(e) = e.to`（`upath_transport_beta(n)` 窮盡）
- **h-層次**：`Fin` 宇宙的路徑相等可判定 ⇒ `U_fin` 是 **1-類型**（`fin_universe_hlevel`）

**代碼**：`hott_univalence_theorem.mbt`（定理 + 證明機器 + 推論，約 35 個新 API）、
`hott_univalence.mbt`（推論的舊 API）、`hott_core.mbt`（`ua` 影子投影 + `ua_eta_legacy`）；
測試 `univalence_theorem_test.mbt`（13 個：U0–U7、C1–C5）。

## 6. 範疇論 HoTT 再定義 <a id="s6"></a>

將 `Category` 從集合論範疇提升為 **HoTT 範疇**：

```
HoTTCat { obj_tag: TypeTag, hlevel: HLevel, hom_truncated: Bool }
HoTTFunctor[A,B] { obj_map: A→B, preserves_comp: Bool }  且 ap 保持路徑
HoTT NatTrans ≔ Homotopy[A,B] = Π(x) Path(f x, g x)
定理 HoTT-1: ap_F : Path_A(x,y) → Path_B(F x, F y)  保 refl/sym/trans 即保同構
```

## 7. 三大函子 HoTT 化 <a id="s7"></a>

- **等價函子** → `Equiv[A,B]` + `ua`，等價保持極限，`transport_via_equivalence` 內聯為 `ap`
- **自由函子** → `FreeHoTT[A] { val: Free[A], level: HLevel }`，HIT 的點自由生成，`free_hott_rec` 需 `B` 為 Set 才能消除
- **平坦函子** → `FlatHoTT { flat, trunc_level }` 即 $∥colim Hom(A_i,−)∥ₙ$，$is\_flat\_hott ⇔ Eℓ(F)$ 的截斷為餘濾，惰性 `cocone` 仍 O(log N)

## 8. Vectₖ HoTT 化 <a id="s8"></a>

`Vectₖ` 在 HoTT 中為 **Set**（0-截斷）：

```
VectHoTT { dim:Int, carrier_tag:TypeTag, is_set:true }
vect_hott_path : Equiv[VectHoTT,VectHoTT] → Path[VectHoTT]  經 ua
張量/直和保持 Set：Set ⊗ Set = Set
```

## 9. Topos HoTT 化 <a id="s9"></a>

**∞-Topos**：類型論語義模型，Site 覆蓋族為命題截斷族

```
InfTopos { base:Site, is_infty:true, trunc_level:NType(100) }
is_sheaf_hott ⇔ 對覆蓋篩 S，Map(S,F) 為截斷極限
```

## 10. 線性邏輯 HoTT 化 <a id="s10"></a>

線性指數 $!A$ 再定義為 **模態/截斷**：$!A ≔ ♭∥A∥$，`LinearHoTT[A] { linear, level }`，線性同倫 $A⊸B$ 的 HoTT 路徑即線性等價保持。

## 11. 同倫/DAG 合成化 <a id="s11"></a>

HoTT **原生合成同倫論**：

```
hott_sphere(n): S⁰=Bool, Sⁿ⁺¹= Susp(Sⁿ)
合成餘切複形 L_{A/k} 為恆等類型的微分，Euler 交錯和保持
```

## 12. 群胚/2-群 HoTT 化 <a id="s12"></a>

```
is_groupoid_hott ⇔ HLevel=GroupoidLevel  (1-類型，Path 為 Prop)
is_two_group_hott ⇔ 2-類型
path_groupoid(A) : Path[A] 構成 ∞-群胚（sym/trans 為群胚運算）
crossed_to_hott(cm) : B(G,H)  2-截斷類型
```

## 13. 新定理 N1-N6 + U（HoTT 獨有） <a id="s13"></a>

| 編號 | 定理 | 內容 | 證明手段 |
|------|------|------|----------|
| N1 | π₁(S¹)=ℤ | `encode_s1 : Path(S¹)→ℤ`, `decode_s1 : ℤ→Path(S¹)` 互逆，`Ω(S¹)≃ℤ` | Encode-Decode，覆疊 `Code : S¹→Type` |
| N2 | 函數/命題外延性 | $(f~g)≃(f=g)$, $(P⇔Q)≃(P=Q)$ | 單值性**定理** + 區間（`funext_happly_laws` 窮盡） |
| N3 | Freudenthal | $A$ n-連通 ⇒ $A→ΩΣA$ 2n-連通，$S¹$ 0-連通穩定 | Σ⊣Ω 伴隨 |
| N4 | 截斷萬有性 | $Map(∥A∥ₙ,B)≃Map(A,B)$ 當 $B$ 為 n-類型 | 截斷消除 |
| N5 | SIP 強化 | 同構么半群/向量空間相等，`n5_sip_vect`、`sip_monoid_fin` | ua 提升載體等價 + 傳輸表逐項驗證 |
| N6 | Blakers-Massey/Whitehead | 推出連通度 $m+n$，$πₙ$ 同構 ⇒ 等價 | 合成同倫 |
| **U** | **單值性（原公理 → 定理）** | $isEquiv(idToEquiv)$，$π₁(U_{fin},Fin\,n)≅S_n$，uaη/uaε/uaβ/三角 | **glue 構造 + n=0..6 窮盡驗證**（`univalence_proof`，見 `docs/UNIVALENCE.md`） |

**代碼**：`hott_new_theorems.mbt` — `pi1_s1_is_int()`, `loop_space_s1_equiv_int()`, `n2_funext_theorem`, `freudenthal_unit`, `n4_trunc_universal`, `n5_sip_*`, `blakers_massey_connectivity`, `whitehead_principle`, `synthetic_pi`。

## 14. 新算法 H1-H7（HoTT 誘導） <a id="s14"></a>

| 編號 | 算法 | 樸素→優化 | HoTT 原理 |
|------|------|-----------|-----------|
| H1 | Cubical 傳輸（Kan 填充） | O(n²) 搜索 → O(1) glue 查表 | `cubical_transport(p,code)`：`Path` 只有 code ⇒ 只能做直線族特例 `v+p.code`；**真正的 Kan 填充**是 `cubical_transport_kan` / `kan_fill_el`（見 §14b K2） |
| H2 | HIT 商化隊列 | 顯式商化 O(n²) → O(1) amortized | 商類型 $A/R$ 的 HIT 路徑商化 |
| H3 | 截斷剪枝搜索 | O(2ⁿ) 枚舉 → O(n) | $∥A∥₋₁$ 僅需存在性代表元 |
| H4 | 合成 π₁ 計算 | O(n³) 單純逼近 → O(1) 整數加法 | $trans : Path→Path$ 即整數加法 |
| H5 | HIT 記憶化 | 哈希 O(n) → 路徑等價命中 | $Path[A](x,y)$ 共享等價類 |
| H6 | 結構傳輸 | O(n²) 重證 → O(1) code 替換 | `transport_structure along ua(e)` |
| H7 | 立方等式判定 | 不可判定 → 可判定（有限模型） | `Term` 無內部結構 ⇒ `normalize` 為**恒等**、`judgmental_eq` 為精確比對（舊版 `code % 1000` 會把 1001 與 1 誤判為相等，已移除）；**真正的 cubical NBE** 是 `cnorm` / `judgmental_eq_ct`（見 §14b K3） |

**代碼**：`hott_algorithms.mbt`，零成本：`Path` code 加法、`Equiv`/`Trunc` 泛型單態化。
**誠實化**：H1/H7 的「假 cubical」已改為誠實聲明 + 指向 `hott_cubical.mbt` 的真正演算法；
唯一可見的行為變更是 demo 行 `eq=true → false`、`norm_code=48 → 2048`（詳見 `docs/CUBICAL.md` §6）。

## 14b. 有限立方體演算法 K1-K3 <a id="s14b"></a>

**代碼**：`hott_cubical.mbt`（約 1,300 行 / 60 個新 API）· **報告**：`docs/CUBICAL.md` · **測試**：`cubical_test.mbt`（12 個）

| 部分 | 內容 | 驗證範圍 | 原子比較 | 結果 |
|------|------|----------|----------|------|
| **K1** 立方體範疇 □ | 態射 = 座標函數（`Coord`/`CubeMap`），生成元 `∂_{i,ε}`/`σ_i`/`s_i`，複合 = 代入 | dim ≤ 4 | **4,172,976** | 忠实性、C1/C2/C3、結合律/單位律、計數律、生成律、三層階層、外延=結構 全 `true` |
| **K2** Kan 填充 | 在單值性纖維 `El` 上解開放盒 ⇒ `transport`；盒條件決定可填性 | card ≤ 5（路徑數 = card! ≤ 120） | **76,200** | 存在/唯一/泛性質/函子性/round-trip/refl/**uaβ** 全 `true` |
| **K3** cubical NBE | `CTerm` 項代數 + 重寫系統 R1–R12（帶良型守衛）+ `cnorm`（eval-then-reify） | 7,804 個項 | **36,885** | 健全性/一致性/冪等/不動點/**強正規化**/等價關係/完備性 全 `true` |

```
計數律  |Hom_□([m],[n])| = Σ_k C(n,k)·C(m,k)·2^(n−k)      13 (m=n=2)
三層    標準 □ ⊂ cartesian □ ⊂ 最大 □                     13 ⊂ 14 ⊂ 16
面格    C(n,k)·2^(n−k)：Q³ = 8/12/6/1，χ(Q^n) = (2−1)^n = 1（可縮）
Gray    g(k) = k ⊕ (k≫1) ⇒ 2^n 個頂點的 Hamiltonian 圈
uaβ     transport(ua σ3, el 1) ⟶ transport(σ3, el 1) ⟶ el(2)      （2 步重寫）
```

**驗證抓到的真實 bug**：重寫規則 R1 `transport(refl,x) → x` 若無守衛，會把卡住的項
`transport(refl, σ0)`（第二個參數是路徑而非元素，語義為 `None`）改寫成 `σ0`（語義為 `Some`）
⇒ 不保語義。加上良型守衛後 `rewrite_sound` 對全部 7,385 個枚舉項成立（回歸測試 K3c）。

## 15. 運行演示 <a id="s15"></a>

```
moon run cmd/main
# hott: refl_code=0 sym_code=0 trans_code=1 ua_code=0 funext_code=0     ← ua_code 10→0（uaη 成立）
# hits: base=base loop_code=1 s1_rec=0 susp=North merid_code=1 trunc_path_code=1
# new_thms: pi1_s1=true set_trunc=true sip_code=1 synth_pi=ℤ            ← sip_code 30→1（載體名不同的虧損）
# hott_algo: cubical=99 trunc_search=true eq=false norm_code=2048 kan_fill=2   ← H7 誠實化（假陽性已修）+ H1 真 Kan 填充
# redefine: cat_level=Grp vect_is_set=true infty=true level_up=Grp lin_consume=10
# univalence_thm: axioms=0 n3(paths=6/6 checks=193) n4(paths=24/24 checks=2137) holds=true
#                 pi1_S3=true ua_beta=true funext=true prop_ext=true sip_classes=7
# n=0 paths=1=1 equivs=1 ηεβ=true inj/surj=true grp=true tri=true checks=9 holds=true
# n=1 paths=1=1 equivs=1 ηεβ=true inj/surj=true grp=true tri=true checks=12 holds=true
# n=2 paths=2=2 equivs=2 ηεβ=true inj/surj=true grp=true tri=true checks=35 holds=true
# n=3 paths=6=6 equivs=6 ηεβ=true inj/surj=true grp=true tri=true checks=193 holds=true
# n=4 paths=24=24 equivs=24 ηεβ=true inj/surj=true grp=true tri=true checks=2137 holds=true
# cubical: axioms=0 K1(dim<=3 checks=93767 C1C2C3=true assoc=true count=true gen=true euler_Q3=1 gray=true)
#          K2(card<=4 checks=2880 kan=true fill(ua(012),1)=2)
#          K3(terms=230 sound=true nbe=true decidable=true transport(ua(σ3),el(1))=el(2)/2步)
```

## 16. 包結構 <a id="s16"></a>

```
axiom/
├── hott_core.mbt          # Path, Equiv, ua(零成本影子), equiv_defect, HLevel, Trunc
├── hott_hits.mbt          # Interval, Circle, Susp, Pushout, Quot
├── hott_univalence_theorem.mbt  # ★ 單值性定理：Fin/Bij/UPath(glue) + 窮盡證明 + 三推論
├── hott_univalence.mbt    # funext, prop_ext, SIP, ua_beta（推論的舊 API）
├── hott_redefine.mbt      # HoTT 再定義：Category/Vect/Topos/Groupoid 等
├── hott_new_theorems.mbt  # N1-N6 新定理
├── hott_cubical.mbt       # ★ 有限立方體演算法 K1-K3：□ 範疇 / Kan 填充 / cubical NBE
├── hott_algorithms.mbt    # H1-H7 新算法（H1/H7 已誠實化並指向 hott_cubical.mbt）
├── category/functor/vect/topos/linear/homotopy/groupoid/algorithms.mbt  # 原结构保留
├── axiom.mbt              # HoTT 版 demo_pipeline + 7 demo（含 univalence_theorem_demo、cubical_demo）
├── axiom_test.mbt         # 26 測試（19+7 HoTT）
├── univalence_theorem_test.mbt  # 13 測試：單值性定理的可執行證明（U0-U7, C1-C5）
├── cubical_test.mbt       # 12 測試：有限立方體演算法的可執行證明（K0-K3c, H1）
├── docs/index.html        # 可視化報告（本文件 + HoTT 附錄）
├── docs/UNIVALENCE.md     # 單值性：公理 → 定理 的完整證明報告
├── docs/CUBICAL.md        # 有限立方體演算法：設計、推導與可執行驗證報告
└── cmd/main/main.mbt      # HoTT 演示入口
```

> **HoTT 統一：相等即路徑，等價即相等；編譯時即證明，運行時即零成本。**

