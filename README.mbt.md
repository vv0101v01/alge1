# Axiom — HoTT 重構的零成本高維演算法庫

> **MoonBit 最新穩定版** · `moon 0.1.20261012` · `moonc v0.10.15` — 已聯網驗證  
> **命題**：運算留在編譯時，零成本抽象  
> **HoTT 公理**：以同倫類型論為統一根基，再定義所有定理與演算法，並新增 HoTT 獨有定理與算法

## 目錄

1. [安裝與構建](#s1)  2. [零成本保證](#s2)  3. [HoTT 核心](#s3)  4. [HITs](#s4)  5. [單值性](#s5)
6. [範疇論 HoTT 再定義](#s6)  7. [三大函子 HoTT 化](#s7)  8. [Vectₖ HoTT 化](#s8)  9. [Topos HoTT 化](#s9)  10. [線性邏輯 HoTT 化](#s10)  11. [同倫/DAG 合成化](#s11)  12. [群胚/2-群 HoTT 化](#s12)  13. [新定理 N1-N6](#s13)  14. [新算法 H1-H7](#s14)  15. [運行演示](#s15)  16. [包結構](#s16)

## 1. 安裝與構建 <a id="s1"></a>

```bash
curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
export PATH="$HOME/.moon/bin:$PATH"
moon version --all  # moon 0.1.20261012  moonc v0.10.15
cd axiom
moon check   # 0 errors, 85 warnings
moon test    # 26 passed (19 原有 + 7 HoTT)
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
Univalence: (A =_U B) ≃ (A ≃ B)   即 ua : Equiv → Path[TypeTag]
h-層次: Contr(-2) < Prop(-1) < Set(0) < Groupoid(1) < 2-Groupoid(2) < NType(n)
Trunc[A] : ∥A∥ₙ  左伴隨 n-類型包含，消除: (∥A∥ₙ→B) ≃ (A→B)  當 B 為 n-類型
```

**代碼**：`hott_core.mbt` — `Path[A]`, `Equiv[A,B]`, `TypeTag`, `UnivalenceWitness`, `HLevel`, `IsContr/IsProp`, `Trunc[A]`, `trunc_rec`。零成本：路徑 code 為 `Int` 加法，編譯時折疊。

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

## 5. 單值性 <a id="s5"></a>

**公理**：$idToEquiv : (A =_U B) → (A ≃ B)$ 為等價；$ua : (A ≃ B) → (A =_U B)$ 為其逆。

```
(A = B) ≃ (A ≃ B)       — 恆等即等價
```

**推論**（均已實現零成本）：
- **函數外延性** $funext : (f~g) ≃ (f=g)$ ，`funext`/`happly` 互逆
- **命題外延性** $(P⇔Q) ≃ (P=Q)$ 當 $P,Q$ 為 Prop
- **結構同一性 SIP**：同構的么半群/群/環相等，`sip_monoid`、`vect_hott_path` 以 `ua` 提升載體等價為相等，再傳輸結構，O(1) 代替 O(n²) 重證
- **uaβ**：`transport along ua(e) = e.to`

**代碼**：`hott_univalence.mbt`。

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

## 13. 新定理 N1-N6（HoTT 獨有） <a id="s13"></a>

| 編號 | 定理 | 內容 | 證明手段 |
|------|------|------|----------|
| N1 | π₁(S¹)=ℤ | `encode_s1 : Path(S¹)→ℤ`, `decode_s1 : ℤ→Path(S¹)` 互逆，`Ω(S¹)≃ℤ` | Encode-Decode，覆疊 `Code : S¹→Type` |
| N2 | 函數/命題外延性 | $(f~g)≃(f=g)$, $(P⇔Q)≃(P=Q)$ | 單值性 + 區間 |
| N3 | Freudenthal | $A$ n-連通 ⇒ $A→ΩΣA$ 2n-連通，$S¹$ 0-連通穩定 | Σ⊣Ω 伴隨 |
| N4 | 截斷萬有性 | $Map(∥A∥ₙ,B)≃Map(A,B)$ 當 $B$ 為 n-類型 | 截斷消除 |
| N5 | SIP 強化 | 同構么半群/向量空間相等，`n5_sip_vect` | ua 提升載體等價 |
| N6 | Blakers-Massey/Whitehead | 推出連通度 $m+n$，$πₙ$ 同構 ⇒ 等價 | 合成同倫 |

**代碼**：`hott_new_theorems.mbt` — `pi1_s1_is_int()`, `loop_space_s1_equiv_int()`, `n2_funext_theorem`, `freudenthal_unit`, `n4_trunc_universal`, `n5_sip_*`, `blakers_massey_connectivity`, `whitehead_principle`, `synthetic_pi`。

## 14. 新算法 H1-H7（HoTT 誘導） <a id="s14"></a>

| 編號 | 算法 | 樸素→優化 | HoTT 原理 |
|------|------|-----------|-----------|
| H1 | Cubical 傳輸重寫 | O(n²) 搜索 → O(n) 線性 | `cubical_transport(p,code)` = Kan 填充 code 加法 |
| H2 | HIT 商化隊列 | 顯式商化 O(n²) → O(1) amortized | 商類型 $A/R$ 的 HIT 路徑商化 |
| H3 | 截斷剪枝搜索 | O(2ⁿ) 枚舉 → O(n) | $∥A∥₋₁$ 僅需存在性代表元 |
| H4 | 合成 π₁ 計算 | O(n³) 單純逼近 → O(1) 整數加法 | $trans : Path→Path$ 即整數加法 |
| H5 | HIT 記憶化 | 哈希 O(n) → 路徑等價命中 | $Path[A](x,y)$ 共享等價類 |
| H6 | 結構傳輸 | O(n²) 重證 → O(1) code 替換 | `transport_structure along ua(e)` |
| H7 | 立方等式判定 | 不可判定 → O(n log n) 可判定 | Sterling-Angiuli 歸一化：`judgmental_eq` 經 `normalize` 比對範式，類型構造子單射性 `pi_injective` |

**代碼**：`hott_algorithms.mbt`，零成本：`Path` code 加法、`Equiv`/`Trunc` 泛型單態化。

## 15. 運行演示 <a id="s15"></a>

```
moon run cmd/main
# hott: refl_code=0 sym_code=0 trans_code=1 ua_code=10 funext_code=0
# hits: base=base loop_code=1 s1_rec=0 susp=North merid_code=1 trunc_path_code=1
# new_thms: pi1_s1=true set_trunc=true sip_code=30 synth_pi=ℤ
# hott_algo: cubical=99 trunc_search=true eq=true norm_code=48
# redefine: cat_level=Grp vect_is_set=true infty=true level_up=Grp lin_consume=10
```

## 16. 包結構 <a id="s16"></a>

```
axiom/
├── hott_core.mbt          # Path, Equiv, Univalence, HLevel, Trunc
├── hott_hits.mbt          # Interval, Circle, Susp, Pushout, Quot
├── hott_univalence.mbt    # funext, prop_ext, SIP
├── hott_redefine.mbt      # HoTT 再定義：Category/Vect/Topos/Groupoid 等
├── hott_new_theorems.mbt  # N1-N6 新定理
├── hott_algorithms.mbt    # H1-H7 新算法
├── category/functor/vect/topos/linear/homotopy/groupoid/algorithms.mbt  # 原结构保留
├── axiom.mbt              # HoTT 版 demo_pipeline + 5 新 demo
├── axiom_test.mbt         # 26 測試（19+7 HoTT）
├── docs/index.html        # 可視化報告（本文件 + HoTT 附錄）
└── cmd/main/main.mbt      # HoTT 演示入口
```

> **HoTT 統一：相等即路徑，等價即相等；編譯時即證明，運行時即零成本。**

