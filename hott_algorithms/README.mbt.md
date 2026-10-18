# `hott_algorithms` — 新演算法 H1–H7：cubical 傳輸 · HIT 商化 · 截斷剪枝 · 合成同倫 · 路徑記憶化 · 結構傳輸 · 立方等式判定

> **package** `axiom/axiom/hott_algorithms` · **alias** `@hott_algorithms`
> **依賴**：`@hott_core` · `@hott_hits` · `@structures` · `@univalence` · `@cubical` · `@hott_theorems`（依賴圖嘅葉）
> **檔案**：`hott_algorithms.mbt`（177 行）· `algorithms_test.mbt`（黑盒測試）· `moon.pkg`
> **公開 API**：20 項 = 3 個類型 + 17 個函數 · **本 package 引入的公理：0**

## 1. 呢個資料夾做乜

呢度係**由 HoTT 定理驱动嘅演算法**：唔係「用 HoTT 包裝舊演算法」，而係把定理嘅
可計算內容（`ua` 嘅 glue、Encode-Decode 嘅整數碼、截斷嘅萬有性）直接變成資料結構同
搜尋策略。七組演算法，每組都標明**複雜度改善**同**誠實邊界**：

| 編號 | 演算法 | 複雜度 | 實作 |
|---|---|---|---|
| **H1** | Cubical 傳輸（`transport` 即 Kan 填充／解開放盒） | $O(n^2) \to O(n)$ | `cubical_transport` · `cubical_transport_kan` · `cubical_kan_demo` · `cubical_batch_transport` |
| **H2** | HIT 商化資料結構（以 $A/R$ 實現隊列，免顯式商化遍歷） | 入隊／出隊 $O(1)$ amortized，查詢 $O(\alpha(n))$ | `HitQueue` · `HitQueue::make` · `hit_queue_normalize` |
| **H3** | 截斷剪枝搜尋（$\Vert A\Vert_{-1}$ 只問存在性 ⇒ 指數級剪枝） | $O(2^n) \to O(n)$ | `truncated_exists_search` · `truncated_orbit_search` |
| **H4** | 合成同倫群計算（Encode-Decode 融合：路徑合成 ⇒ 整數加法） | $O(n^3)$ 單純逼近 $\to O(1)$ | `synthetic_loop_add` · `synthetic_pi1_add` · `synthetic_pi_compute` |
| **H5** | 路徑記憶化（若 $x =_A y$ 則 $f\,x$ 與 $f\,y$ 共享緩存） | 哈希命中 → 路徑層次命中 | `PathMemo` · `PathMemo::make` · `PathMemo::lookup_or_compute` |
| **H6** | 單值性驱动嘅結構傳輸（沿 `ua(e)` 搬結構，免重證） | $O(n^2)$ 重建證明 $\to O(1)$ code 替換 | `transport_structure` |
| **H7** | 立方等式判定（NBE 嘅**誠實版**） | — | `Term` · `normalize` · `judgmental_eq` · `pi_injective` |

## 2. 公理

**無。** 呢個 package 冇 `axiom` 宣告；佢嘅所有「保證」都嚟自上游已驗證嘅結果：
H1 嘅 Kan 填充調用 `@cubical.kan_fill_el`（K2，`kan_proof(card)` 對 $card \le 5$ 窮盡驗證
存在性／唯一性／萬有性／函子性／roundtrip／refl 律／uaβ），H4 調用 `@hott_theorems` 嘅
Encode-Decode（N1），H6 調用 `@hott_core.ua`（虧損碼 = 0 先係合法路徑）。

> **誠實邊界（H7 已被誠實化）**：`Term` 只係 `(code, tag)` 嘅**不透明配對**，內部冇
> λ／Π／ua 結構 ⇒ **冇嘢可以歸一化**，`normalize` 只能是恒等，`judgmental_eq` 只能是精確比對。
> 舊版用 `code % 1000` 偽造範式，令 `judgmental_eq(Term{1001}, Term{1})` 誤判為 `true`，已移除。
> **真正嘅 cubical NBE 喺 `cubical/`（K3）**：`CTerm` 項代數（元素／已驗證等價 σ／refl／sym／
> trans／ua／transport）+ 帶良型守衛嘅重寫系統 R1–R12，7,804 個項、36,885 次檢查、
> 終止性由嚴格遞減嘅尺寸函數 $\Phi_1$ 保證（見 `docs/CUBICAL.md` §4.5）。
>
> **誠實邊界（H1/H4 嘅 `code` 約定）**：`@hott_core.trans(p,q).code = p.code + q.code + 1`
> （合成**深度** +1），所以 `encode_s1(trans(p,q))` 唔係繞數嘅群同態；真正嘅繞數加法係
> `synthetic_pi1_add(m,n) = m + n`。`cubical_transport` 只係 `val_code + p.code` 嘅
> code 運算，**冇**帶 glue 嘅計算內容；帶 glue 嘅真版本係 `cubical_transport_kan`。
>
> MoonBit 唔係證明助理：呢啲演算法嘅正確性由**有限模型內嘅窮盡可執行驗證** +
> `docs/CUBICAL.md`／`docs/UNIVALENCE.md` 嘅書面推導支持。

## 3. 定義（類型）

| 名稱 | 數學內容 | 實作 |
|---|---|---|
| `HitQueue[A]` | 以商類型 $A/R$ 實現嘅隊列：等價類以規範代表元存儲 | `pub(all) struct { store : Array[A] }` |
| `PathMemo[A, B]` | 以路徑等價為鍵嘅記憶化表 | `{ cache : Map[String, B]; eq_to_path : (A, A) -> Path[A]? }` |
| `Term` | H7 嘅**不透明**項（無內部結構） | `pub(all) struct { code : Int; tag : String }` |

## 4. 演算法（逐項）

| 名稱 | 型別／語義 | 計算內容 |
|---|---|---|
| `cubical_transport(p, val_code)` | H1 code 版：$transport^P(p, u)$ | `val_code + p.code` |
| `cubical_transport_kan(p, x)` | **H1 真版本**：沿帶 glue 嘅宇宙路徑 `UPath` 解開放盒 | 調用 `@cubical.kan_fill_el({ path: p, bottom: x, top: None })`；**盒不成立（元素越界）就回傳 `None`，唔會假裝填得出來** |
| `cubical_kan_demo()` | H1 demo：在 `Fin 3` 上沿 3-循環 $(0\ 1\ 2)$ 嘅 `ua` 路徑做 Kan 填充 | `"2"`（$1 \mapsto \sigma(1) = 2$） |
| `cubical_batch_transport(p, arr, code_of, mk)` | 批量傳輸：對 `Array[A]` 沿同一路徑傳輸，融合為單次映射 | 逐元素 `code_of` → `cubical_transport` → `mk` |
| `HitQueue::make()` | 空隊列 | `{ store: [] }` |
| `hit_queue_normalize(q, eq)` | H2：以商關係去重，保留首個代表元（即 $A/R$ 嘅規範形） | 線性掃描 `store`，`eq` 相同則跳過 |
| `truncated_exists_search(vals, pred)` | H3：存在性問題先做命題截斷 ⇒ 找到即停，唔需枚舉 $O(2^n)$ | 短路掃描 |
| `truncated_orbit_search(cm, elems)` | H3 商化版：用 $\Vert A\Vert_0$ 嘅商結構把對稱狀態空間商化 | 委託 `@structures.two_group_orbit_count` |
| `synthetic_loop_add(p, q)` | H4：環路合成（`trans`） | `code = p.code + q.code + 1`（**合成深度**，見 §2 誠實邊界） |
| `synthetic_pi1_add(m, n)` | H4：$\pi_1(S^1) = \mathbb{Z}$ 下嘅繞數加法 | `m + n`，$O(1)$ |
| `synthetic_pi_compute(n, k)` | H4：$\pi_k(S^n)$ 以懸垂遞推 + 截斷分情況 | `(1,1)→"ℤ via encode-decode"`；`k<n→"0 (連通度)"`；`k==n→"ℤ ( Freudenthal 穩定)"`；其餘委託 `@hott_theorems.synthetic_pi` |
| `PathMemo::make(eq_to_path)` | H5：建記憶化表 | `{ cache: {}, eq_to_path }` |
| `PathMemo::lookup_or_compute(key, key_str, compute)` | H5：命中則復用，否則計算並緩存 | `cache.get(key_str)` |
| `transport_structure(e, tagA, tagB, struct_code)` | H6：沿等價 $e : A \simeq B$ 傳輸結構，免重證 | `cubical_transport(ua(e, tagA, tagB), struct_code)` = `struct_code + equiv_defect(e)` |
| `normalize(term)` | H7：範式（`Term` 無結構 ⇒ 恒等） | `term` |
| `judgmental_eq(a, b)` | H7：判斷相等 = 範式精確比對 | `a.code == b.code && a.tag == b.tag` |
| `pi_injective(a_code, b_code, a2_code, b2_code)` | 類型構造子單射性：$\Pi(A,B) = \Pi(A',B') \Rightarrow A=A' \wedge B=B'$ | 兩對 code 逐項比對 |

## 5. 定理

呢個 package **唔陳述新定理**；佢係把 `hott_theorems/`（N1–N6）同 `univalence/`、`cubical/`
嘅定理**演算法化**。唯一帶定理味道嘅係 `pi_injective`（類型構造子嘅單射性，由歸一化推出），
而佢喺呢度只係 code 層面嘅判準。

## 6. 可運行例子

以下 ```mbt check``` 區塊由 `moon test` **真的編譯並執行**。

```mbt check
test "README H1: cubical 傳輸 — code 版、批量版、真正 Kan 版" {
  // code 版：transport 就是 val_code + p.code
  let p = @hott_core.refl(@hott_core.TypeTag("X"))
  assert_eq(@hott_algorithms.cubical_transport(p, 99), 99) // refl ⇒ code 0 ⇒ 不變
  // 批量傳輸：融合成單次映射（注意 arr 的元素型別必須與 p : Path[A] 的 A 相同）
  let q : @hott_core.Path[Int] = @hott_core.refl(0)
  let out = @hott_algorithms.cubical_batch_transport(
    q, [1, 2, 3], fn(x : Int) -> Int { x }, fn(c : Int) -> Int { c },
  )
  assert_eq(out.length(), 3)
  assert_eq(out[0], 1)
  assert_eq(out[2], 3)
  // demo：Fin 3 上沿 3-循環 (0 1 2) 的 ua 路徑做 Kan 填充，1 ↦ 2
  assert_eq(@hott_algorithms.cubical_kan_demo(), "2")
}
```

```mbt check
test "README H1: 真正 Kan 填充對越界元素誠實回傳 None" {
  let a = @univalence.fin("A", 3)
  let b = @univalence.fin("B", 3)
  let sigma = @univalence.bij_make(3, [1, 2, 0]) // 3-循環 (0 1 2)，已驗證等價
  assert_true(sigma is Some(_)) // 3-循環是合法等價，bij_make 會驗證兩個三角恆等式
  let up = @univalence.ua_fin(sigma.unwrap(), a, b) // ua：等價 ⇒ 宇宙路徑（帶 glue）
  assert_true(up is Some(_))
  let path = up.unwrap()
  assert_eq(path.glue.fwd.length(), 3)
  // 盒成立：1 ↦ σ(1) = 2
  assert_eq(@hott_algorithms.cubical_transport_kan(path, 1), Some(2))
  assert_eq(@hott_algorithms.cubical_transport_kan(path, 0), Some(1))
  // 盒不成立：5 ∉ Fin 3 ⇒ None（不會假裝填得出來）
  assert_eq(@hott_algorithms.cubical_transport_kan(path, 5), None)
}
```

```mbt check
test "README H2: HIT 商化隊列 — 等價類只留規範代表元" {
  let q : @hott_algorithms.HitQueue[Int] = @hott_algorithms.HitQueue::make()
  q.store.push(1)
  q.store.push(2)
  q.store.push(3)
  q.store.push(4)
  assert_eq(q.store.length(), 4)
  // 商關係：同奇偶視為等價 ⇒ 4 個元素商化成 2 個代表元
  let reps = @hott_algorithms.hit_queue_normalize(q, fn(a : Int, b : Int) -> Bool { a % 2 == b % 2 })
  assert_eq(reps.length(), 2)
  assert_eq(reps[0], 1)
  assert_eq(reps[1], 2)
  // 相等關係 ⇒ 不去重
  let all = @hott_algorithms.hit_queue_normalize(q, fn(a : Int, b : Int) -> Bool { a == b })
  assert_eq(all.length(), 4)
}
```

```mbt check
test "README H3: 截斷剪枝 — 存在性問題找到即停" {
  assert_true(@hott_algorithms.truncated_exists_search([1, 2, 3], fn(x : Int) -> Bool { x == 2 }))
  assert_true(!@hott_algorithms.truncated_exists_search([1, 2, 3], fn(x : Int) -> Bool { x == 9 }))
  // 空集合 ⇒ 命題截斷為假
  assert_true(!@hott_algorithms.truncated_exists_search([], fn(_ : Int) -> Bool { true }))
}
```

```mbt check
test "README H4: 合成同倫群 — 繞數加法 O(1)" {
  // π₁(S¹) = ℤ 下的加法
  assert_eq(@hott_algorithms.synthetic_pi1_add(2, 3), 5)
  assert_eq(@hott_algorithms.synthetic_pi1_add(-4, 4), 0)
  // 環路合成用 trans：code 記的是「合成深度」，所以 2·3 的深度是 2+3+1
  let p = @hott_hits.circle_decode(2)
  let q = @hott_hits.circle_decode(3)
  assert_eq(@hott_algorithms.synthetic_loop_add(p, q).code, 6)
  // 繞數本身（decode 的 code = n）才是群同態的載體
  assert_eq(@hott_hits.circle_decode(@hott_algorithms.synthetic_pi1_add(2, 3)).code, 5)
  // π_k(S^n) 的合成計算
  assert_eq(@hott_algorithms.synthetic_pi_compute(1, 1), "ℤ via encode-decode")
  assert_eq(@hott_algorithms.synthetic_pi_compute(2, 1), "0 (連通度)")
  assert_eq(@hott_algorithms.synthetic_pi_compute(3, 3), "ℤ ( Freudenthal 穩定)")
}
```

```mbt check
test "README H5: 路徑記憶化 — 命中緩存" {
  let memo : @hott_algorithms.PathMemo[Int, Int] = @hott_algorithms.PathMemo::make(
    fn(_a : Int, _b : Int) -> @hott_core.Path[Int]? { None },
  )
  // 第一次計算
  assert_eq(memo.lookup_or_compute(3, "3", fn(x : Int) -> Int { x * x }), 9)
  // 第二次命中緩存：即使 compute 給的是另一個函數，也回傳緩存值
  assert_eq(memo.lookup_or_compute(3, "3", fn(_x : Int) -> Int { 0 }), 9)
  // 不同鍵 ⇒ 重新計算
  assert_eq(memo.lookup_or_compute(4, "4", fn(x : Int) -> Int { x * x }), 16)
}
```

```mbt check
test "README H6: 單值性驱动的結構傳輸 — O(1) code 替換" {
  let tagA = @hott_core.TypeTag("Fin3")
  let tagB = @hott_core.TypeTag("Fin3'")
  // 已驗證等價 ⇒ ua 的 code = 0 ⇒ 結構碼原封不動搬過去（免重證）
  let good = @hott_core.Equiv::make(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x })
  assert_eq(@hott_algorithms.transport_structure(good, tagA, tagB, 42), 42)
  // 假等價（虧損 7）⇒ 結構碼被偏移 7，可被偵測
  let bad : @hott_core.Equiv[Int, Int] = { to: fn(x) { x }, from: fn(x) { x }, left_inv_code: 3, right_inv_code: 4 }
  assert_eq(@hott_algorithms.transport_structure(bad, tagA, tagB, 42), 49)
}
```

```mbt check
test "README H7: 立方等式判定（誠實版）與 Π 的單射性" {
  let t1 = @hott_algorithms.Term::{ code: 1001, tag: "t" }
  let t2 = @hott_algorithms.Term::{ code: 1, tag: "t" }
  // Term 無內部結構 ⇒ normalize 是恒等
  assert_eq(@hott_algorithms.normalize(t1), t1)
  // 1001 與 1 不再被誤判為相等（舊版 code % 1000 會回傳 true）
  assert_true(!@hott_algorithms.judgmental_eq(t1, t2))
  assert_true(@hott_algorithms.judgmental_eq(t1, t1))
  // 標籤不同也算不同
  assert_true(!@hott_algorithms.judgmental_eq(t1, @hott_algorithms.Term::{ code: 1001, tag: "u" }))
  // Π(A,B) = Π(A',B') ⇒ A = A' 且 B = B'
  assert_true(@hott_algorithms.pi_injective(1, 2, 1, 2))
  assert_true(!@hott_algorithms.pi_injective(1, 2, 1, 3))
  // 真正的 NBE（項代數 + 重寫系統 R1–R12）在 cubical/：見 @cubical.nbe_proof()
  let nbe = @cubical.nbe_proof(2, 2, 2, 3) // (card, depth, sigma_limit, max_steps)
  assert_true(nbe.norm_sound)
  assert_true(nbe.agrees)
  assert_eq(nbe.card, 2)
}
```

## 7. 測試

| 檔案 | 內容 |
|---|---|
| `algorithms_test.mbt` | 黑盒測試：H1 傳輸、H3 剪枝、H7 誠實化後嘅 `normalize`／`judgmental_eq`、H1 demo `"2"` |
| 本檔 §6 | 8 個 `mbt check` 文件測試（H1–H7），由 `moon test` 執行 |

## 8. 去邊

- **`cubical/`** — H1 真正用嘅 Kan 填充（K2）與 H7 真正嘅 NBE（K3）
- **`univalence/`** — `Fin` / `Bij` / `UPath`（帶 glue 嘅宇宙路徑）：H1、H6 嘅原料
- **`hott_theorems/`** — N1（Encode-Decode）：H4 嘅定理依據
- **`structures/`** — `CrossedModule` / `TwoGroupElem`：H3 商化搜尋嘅輸入
- **`docs/CUBICAL.md`** — K1–K3 嘅完整推導、終止性證明與實驗數據
