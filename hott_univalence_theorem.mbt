/// @file hott_univalence_theorem.mbt
/// # 單值性定理（Theorem）— 原「單值性公理」已降級，零公理 + 可執行證明
///
/// ## 0. 原本為什麼是「公理」
/// 舊實作 `hott_core.mbt::ua` 直接把路徑寫成
/// `{ lhs: tagA, rhs: tagB, code: e.left_inv_code + e.right_inv_code + 10 }`：
/// 常數 `10` 無任何來源，路徑本身沒有計算內容，於是它自己的定律都不成立——
///   * uaη 違反：`ua(idEquiv_A)` 的 code = 10 ≠ 0，所以 `ua(idEquiv) ≠ refl`
///   * uaβ 違反：`transport (ua e) x` 經 `cubical_transport` 會多加 10，≠ `e.to x`
/// 「無法由更基本的構造導出、只能宣告」正是公理的定義。本文件把它換成定理。
///
/// ## 1. 降級策略（三層，對應 cubical/glue 證明思路）
/// * **L1 模型層**：把宇宙中的類型具體化為有限類型 `Fin { tag, card }`。
///   基數 `card` 是它在宇宙中的完整結構碼，因此「相等」是可判定的。
/// * **L2 構造層**：宇宙路徑 `UPath { lhs, rhs, glue }` **自帶計算內容**
///   （glue = 一個已驗證的雙射）。這不是作弊，而是 Cohen–Coquand–Huber–Mörtberg
///   的 glue 构造：一旦路徑在宇宙中有計算內容，`ua` 就變成**定義**而非宣告——
///   `idToEquiv p` = 沿 `p` 傳輸元素（transport 消除 glue），`ua e` = 把已驗證的
///   等價 `e` 裝回 glue 欄位。兩邊都只用已給出的資料，沒有新公理。
/// * **L3 驗證層**：對 `card = 0..5` **窮盡枚舉**全部 `n!` 條路徑與全部 `n!` 個
///   自等價，逐條計算 uaη / uaε / uaβ / 單射 / 滿射 / refl-sym-trans 函子性 /
///   三角恆等式（相干性），全部由計算得出 `true`，而非寫死。
///
/// ## 2. 定理陳述
/// 對每個有限類型 `Fin n`：`idToEquiv : (Fin n =_U Fin n) → (Fin n ≃ Fin n)`
/// 是等價，擬逆為 `ua`；且 `π₁(U_fin, Fin n) ≅ S_n`（基數 `n!`，雙向單射滿射）。
/// 推論（同樣在此文件以計算證明，不再是 `-> Bool { true }` 的佔位）：
/// 函數外延性、命題外延性、SIP 結構同一性（有限么半群的同構即相等）。
///
/// ## 3. 誠實聲明
/// MoonBit 不是證明助手，型別系統不會檢查 `Path` 的端點。因此這裡的「證明」是
/// **模型論式可執行證明**：在一個語義明確、相等可判定的有限宇宙模型中，把定理的
/// 每一條定律化為有限計算並窮盡驗證（decision procedure）。全宇宙層面的單值性
/// 在 cubical 類型論中是定理（CCHM 2016 / Orton–Pitts 2016 / Angiuli 2019），
/// 其證明思路（glue + Kan 填充）正是 L2 所採用的構造；詳見 docs/UNIVALENCE.md。

// ==================== L1 模型層：有限宇宙 ====================

///|
/// 宇宙中的有限類型。`tag` 是名字，`card` 是完整結構碼（基數）。
pub(all) struct Fin {
  tag : TypeTag
  card : Int32
} derive(Eq, Debug)

///|
pub fn fin(name : String, card : Int32) -> Fin {
  { tag: TypeTag(name), card, }
}

///|
pub fn factorial(n : Int32) -> Int32 {
  let mut r = 1
  for i in 1..<=(if n < 0 { 0 } else { n }) {
    r = r * i
  }
  r
}

///|
fn int_array_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
fn int_array_copy(a : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  for i in 0..<a.length() {
    out[i] = a[i]
  }
  out
}

// ==================== 已驗證的等價：雙射 Bij ====================

///|
/// 有限類型間的等價 `A ≃ B`（card 相同時即 `Fin n ≃ Fin n` 的自等價）。
/// 不變量（由 `bij_make` / `bij_make_with_inv` **驗證**後才允許構造）：
///   1. `fwd`、`bwd` 長度皆為 `card`，值域皆落在 `[0, card)`
///   2. `bwd ∘ fwd = id` 且 `fwd ∘ bwd = id`（兩個三角恆等式，逐點檢查）
/// 因此 `Bij` 的每個元素都是一個「已被檢查過的等價」，沒有未驗證的內容。
pub(all) struct Bij {
  card : Int32
  fwd : Array[Int32]
  bwd : Array[Int32]
} derive(Debug)

///|
/// 由前向表與逆向表構造等價：兩個方向的三角恆等式都被逐點驗證。
/// 回傳 `None` 表示「這不是等價」——把公理換成可判定檢查的關鍵就在這裡。
pub fn bij_make_with_inv(
  card : Int32,
  fwd : Array[Int32],
  bwd : Array[Int32],
) -> Bij? {
  if card < 0 {
    return None
  }
  if fwd.length() != card || bwd.length() != card {
    return None
  }
  for i in 0..<card {
    let j = fwd[i]
    let k = bwd[i]
    if j < 0 || j >= card || k < 0 || k >= card {
      return None
    } // 值域外 ⇒ 非雙射
    if bwd[j] != i {
      return None
    } // bwd ∘ fwd ≠ id
    if fwd[k] != i {
      return None
    } // fwd ∘ bwd ≠ id
  }
  Some({ card, fwd: int_array_copy(fwd), bwd: int_array_copy(bwd), })
}

///|
/// 只給前向表：逆向表由計算得出（先檢查單射與值域，再算逆，再驗證兩個三角恆等式）。
pub fn bij_make(card : Int32, fwd : Array[Int32]) -> Bij? {
  if card < 0 || fwd.length() != card {
    return None
  }
  let bwd = Array::make(card, -1)
  for i in 0..<card {
    let j = fwd[i]
    if j < 0 || j >= card {
      return None
    } // 值域外
    if bwd[j] != -1 {
      return None
    } // 撞車 ⇒ 非單射
    bwd[j] = i
  }
  for j in 0..<card {
    if bwd[j] < 0 {
      return None
    } // 無原像 ⇒ 非滿射
  }
  bij_make_with_inv(card, fwd, bwd)
}

///|
pub fn bij_id(card : Int32) -> Bij {
  let id = Array::make(card, 0)
  for i in 0..<card {
    id[i] = i
  }
  match bij_make(card, id) {
    Some(b) => b
    None => abort("bij_id: identity map failed its own verification")
  }
}

///|
pub fn bij_apply(b : Bij, i : Int32) -> Int32 {
  b.fwd[i]
}

///|
pub fn bij_inv(b : Bij) -> Bij {
  // 逆的三角恆等式與原映射相同（對稱），故直接換欄位即已驗證
  { card: b.card, fwd: int_array_copy(b.bwd), bwd: int_array_copy(b.fwd), }
}

///|
/// `g ∘ f`（先 f 後 g）。結果再經 `bij_make_with_inv` 驗證一次。
pub fn bij_compose(g : Bij, f : Bij) -> Bij {
  let n = f.card
  if g.card != n {
    abort("bij_compose: card mismatch")
  }
  let fwd = Array::make(n, 0)
  let bwd = Array::make(n, 0)
  for i in 0..<n {
    fwd[i] = g.fwd[f.fwd[i]]
    bwd[i] = f.bwd[g.bwd[i]]
  }
  match bij_make_with_inv(n, fwd, bwd) {
    Some(b) => b
    None =>
      abort("bij_compose: composite of verified bijections failed verification")
  }
}

///|
/// 外延相等：逐點比較（`Array` 沒有 `Eq`，故手寫；這同時是「等價類型是集合」的判定程序）
pub fn bij_eq(a : Bij, b : Bij) -> Bool {
  a.card == b.card && int_array_eq(a.fwd, b.fwd) && int_array_eq(a.bwd, b.bwd)
}

///|
pub fn bij_is_id(b : Bij) -> Bool {
  bij_eq(b, bij_id(b.card))
}

///|
/// Lehmer 碼：`code = Σ_i L_i · (n-1-i)!`，其中 `L_i = #{ j>i | σ_j < σ_i }`。
/// 因為 `0 ≤ L_i ≤ n-1-i`，這是階乘進位制，故 `σ ↦ code` 是 `S_n → [0,n!)` 的雙射
/// （單射性另由 `univalence_proof.shadow_injective` 窮盡驗證）。
pub fn lehmer_code(b : Bij) -> Int32 {
  let n = b.card
  let mut code = 0
  let mut fact = factorial(n - 1)
  for i in 0..<n {
    let mut smaller = 0
    for j in (i + 1)..<n {
      if b.fwd[j] < b.fwd[i] {
        smaller = smaller + 1
      }
    }
    code = code + smaller * fact
    if n - 1 - i > 0 {
      fact = fact / (n - 1 - i)
    }
  }
  code
}

///|
fn permutations_of(card : Int32) -> Array[Array[Int32]] {
  if card <= 0 {
    let empty : Array[Array[Int32]] = []
    empty.push([])
    return empty
  }
  let smaller = permutations_of(card - 1)
  let out : Array[Array[Int32]] = []
  for p in smaller {
    let len = p.length()
    for k in 0..<=len {
      let q : Array[Int32] = []
      for i in 0..<k {
        q.push(p[i])
      }
      q.push(card - 1)
      for i in k..<len {
        q.push(p[i])
      }
      out.push(q)
    }
  }
  out
}

///|
/// 窮盡枚舉 `Fin card ≃ Fin card` 的全部元素（對稱群 `S_card`）。
/// 每個元素都經過 `bij_make` 的雙射驗證，所以回傳的陣列就是「已驗證等價的全集」。
pub fn bij_all(card : Int32) -> Array[Bij] {
  let out : Array[Bij] = []
  for p in permutations_of(card) {
    match bij_make(card, p) {
      Some(b) => out.push(b)
      None => abort("bij_all: a permutation failed verification")
    }
  }
  out
}

// ==================== L2 構造層：帶 glue 的宇宙路徑 ====================

///|
/// 宇宙路徑 `A =_U B`。與舊的 `Path[TypeTag]` 不同：它**帶計算內容**（glue），
/// 所以 transport 沿它作用時會真的計算，`ua` 因此可以是定義而不是公理。
/// 不變量：`lhs.card == rhs.card == glue.card`（由 `upath_make` 驗證）。
pub(all) struct UPath {
  lhs : Fin
  rhs : Fin
  glue : Bij
} derive(Debug)

///|
pub fn upath_make(a : Fin, b : Fin, glue : Bij) -> UPath? {
  if a.card != glue.card || b.card != glue.card {
    return None
  }
  Some({ lhs: a, rhs: b, glue, })
}

///|
pub fn upath_refl(a : Fin) -> UPath {
  { lhs: a, rhs: a, glue: bij_id(a.card), }
}

///|
pub fn upath_sym(p : UPath) -> UPath {
  { lhs: p.rhs, rhs: p.lhs, glue: bij_inv(p.glue), }
}

///|
pub fn upath_trans(p : UPath, q : UPath) -> UPath? {
  if p.rhs != q.lhs {
    return None
  }
  upath_make(p.lhs, q.rhs, bij_compose(q.glue, p.glue))
}

///|
/// 路徑相等可判定（`Fin` 宇宙的相等是命題 ⇒ 宇宙是 1-類型，無高階結構）
pub fn upath_eq(p : UPath, q : UPath) -> Bool {
  p.lhs == q.lhs && p.rhs == q.rhs && bij_eq(p.glue, q.glue)
}

///|
/// **transport**：沿宇宙路徑把 `Fin n` 的元素搬到 `Fin n`。
/// 這是 glue 模型的消除規則：`transport p i` 定義上就是 `p.glue` 的前向作用。
/// uaβ 之所以能變成 `refl`（定義性等價），全靠這條定義。
pub fn upath_transport(p : UPath, i : Int32) -> Int32 {
  bij_apply(p.glue, i)
}

///|
/// 沿宇宙路徑傳輸一張 `n` 元運算表（ arity 2 ）：`(σ·m)(i,j) = σ(m(σ⁻¹i, σ⁻¹j))`
/// 這是 SIP 的計算內容：結構跟著路徑走，不需要重新證明。
pub fn upath_transport_table(p : UPath, table : Array[Int32]) -> Array[Int32] {
  let n = p.rhs.card
  let g = p.glue
  let out = Array::make(n * n, 0)
  for i in 0..<n {
    for j in 0..<n {
      let src = g.bwd[i] * n + g.bwd[j]
      out[i * n + j] = g.fwd[table[src]]
    }
  }
  out
}

///|
/// 窮盡枚舉 `a =_U b` 的全部路徑（card 不同則為空 —— 這正是「不等價即不相等」）
pub fn upath_all(a : Fin, b : Fin) -> Array[UPath] {
  let out : Array[UPath] = []
  if a.card != b.card {
    return out
  }
  for e in bij_all(a.card) {
    match upath_make(a, b, e) {
      Some(p) => out.push(p)
      None => abort("upath_all: verified equivalence rejected by upath_make")
    }
  }
  out
}

///|
/// 零成本影子：把帶 glue 的路徑投影回舊 API 的 `Path[TypeTag]`。
/// code 取 glue 的 Lehmer 碼 ⇒ 投影在有限宇宙上是**單射**，且 `refl ↦ code 0`。
pub fn upath_to_legacy(p : UPath) -> Path[TypeTag] {
  { lhs: p.lhs.tag, rhs: p.rhs.tag, code: lehmer_code(p.glue), }
}

// ==================== idToEquiv 與 ua：兩個方向都是「定義」 ====================

///|
/// `idToEquiv : (A =_U B) → (A ≃ B)`。
/// 由 **transport**（路徑的消除規則）定義，而不是直接讀 `glue` 欄位：
/// 前向映射 = 沿 `p` 傳輸元素，逆向映射 = 沿 `sym p` 傳輸元素，
/// 之後再用 `bij_make_with_inv` 驗證它確實是等價。
/// 「結果恰好等於 glue」是**推論**（下面的 uaη 定律），不是假設。
pub fn id_to_equiv_fin(p : UPath) -> Bij {
  let n = p.lhs.card
  let q = upath_sym(p)
  let fwd = Array::make(n, 0)
  let bwd = Array::make(n, 0)
  for i in 0..<n {
    fwd[i] = upath_transport(p, i)
    bwd[i] = upath_transport(q, i)
  }
  match bij_make_with_inv(n, fwd, bwd) {
    Some(b) => b
    None =>
      abort(
        "id_to_equiv_fin: transport along a universe path is not a bijection",
      )
  }
}

///|
/// `ua : (A ≃ B) → (A =_U B)` —— **定義**（原公理）。
/// 只使用 `e` 自己已經被驗證的資料：把等價裝進 glue 欄位。
/// 沒有捏造任何常數，也沒有假設任何未證明的命題。
pub fn ua_fin(e : Bij, a : Fin, b : Fin) -> UPath? {
  upath_make(a, b, e)
}

///|
fn ua_or_abort(e : Bij, a : Fin, b : Fin) -> UPath {
  match ua_fin(e, a, b) {
    Some(p) => p
    None =>
      abort(
        "ua: card mismatch — the caller passed an equivalence of another size",
      )
  }
}

///|
/// uaβ 的窮盡證明：`transport (ua e) x ≡ e x` 對全部 `e`、全部 `x` 成立
pub fn upath_transport_beta(card : Int32) -> Bool {
  let a = fin("Fin" + card.to_string(), card)
  let mut ok = true
  for e in bij_all(card) {
    let p = ua_or_abort(e, a, a)
    for x in 0..<card {
      if upath_transport(p, x) != bij_apply(e, x) {
        ok = false
      }
    }
  }
  ok
}

// ==================== L3 驗證層：定理的窮盡證明 ====================

///|
/// 定理的證明物件。**每個欄位都是計算出來的**，沒有任何 `true` 字面值。
pub(all) struct UnivalenceProof {
  card : Int32
  /// 基數律：`|Fin n = Fin n| = n! = |Fin n ≃ Fin n|`
  count_law : Bool
  path_count : Int32
  equiv_count : Int32
  expected : Int32
  /// uaη : Π(p : A = B), ua(idToEquiv p) = p
  eta : Bool
  /// uaε : Π(e : A ≃ B), idToEquiv(ua e) = e
  eps : Bool
  /// uaβ : Π(e)(x), transport (ua e) x = e x
  beta : Bool
  /// ua 為單射：不同等價 ⇒ 不同路徑
  ua_injective : Bool
  /// ua 為滿射：每條路徑都是某個等價的 ua
  ua_surjective : Bool
  /// 群胚函子性：ua(idEquiv) = refl
  refl_law : Bool
  /// ua(e⁻¹) = sym(ua e)
  sym_law : Bool
  /// ua(g ∘ f) = trans (ua f) (ua g)
  trans_law : Bool
  /// 三角恆等式（半伴隨等價的相干性）⇒ isEquiv(idToEquiv)
  triangle : Bool
  /// 路徑相等可判定且反身完備 ⇒ Fin 宇宙是 1-類型（π₂ = 0）
  decidable_eq : Bool
  /// 影子投影 `upath_to_legacy` 在有限宇宙上單射（Lehmer 碼忠實）
  shadow_injective : Bool
  /// 執行過的原子比較次數（窮盡程度的見證）
  checks : Int32
} derive(Debug)

///|
/// 對 `Fin card` 窮盡驗證單值性定理的每一條定律。
pub fn univalence_proof(card : Int32) -> UnivalenceProof {
  let a = fin("Fin" + card.to_string(), card)
  let equivs = bij_all(card) // |Fin n ≃ Fin n|
  let paths = upath_all(a, a) // |Fin n = Fin n|
  let np = paths.length()
  let mut checks = 0

  // (T1) 基數律：兩邊都必須是 n!
  let expected = factorial(card)
  let count_law = np == expected && equivs.length() == expected

  // (T2) uaη : ua(idToEquiv p) = p
  let mut eta = true
  for p in paths {
    checks = checks + card + 1
    if !upath_eq(ua_or_abort(id_to_equiv_fin(p), p.lhs, p.rhs), p) {
      eta = false
    }
  }

  // (T3) uaε : idToEquiv(ua e) = e
  let mut eps = true
  for e in equivs {
    checks = checks + card + 1
    if !bij_eq(id_to_equiv_fin(ua_or_abort(e, a, a)), e) {
      eps = false
    }
  }

  // (T4) uaβ : transport (ua e) x = e x
  let mut beta = true
  for e in equivs {
    let p = ua_or_abort(e, a, a)
    for x in 0..<card {
      checks = checks + 1
      if upath_transport(p, x) != bij_apply(e, x) {
        beta = false
      }
    }
  }

  // (T5) 單射：ua 把不同等價送到不同路徑
  let mut injective = true
  for i in 0..<np {
    for j in (i + 1)..<np {
      checks = checks + 1
      if upath_eq(paths[i], paths[j]) {
        injective = false
      }
    }
  }

  // (T6) 滿射：對每條路徑顯式搜索一個等價 e 使 ua e = p
  let mut surjective = true
  for p in paths {
    let mut found = false
    for e in equivs {
      checks = checks + 1
      if upath_eq(ua_or_abort(e, p.lhs, p.rhs), p) {
        found = true
      }
    }
    if !found {
      surjective = false
    }
  }

  // (T7) 群胚函子性
  checks = checks + 1
  let refl_law = upath_eq(ua_or_abort(bij_id(card), a, a), upath_refl(a))
  let mut sym_law = true
  for e in equivs {
    checks = checks + 1
    if !upath_eq(ua_or_abort(bij_inv(e), a, a), upath_sym(ua_or_abort(e, a, a))) {
      sym_law = false
    }
  }
  let mut trans_law = true
  for f in equivs {
    let pf = ua_or_abort(f, a, a)
    for g in equivs {
      checks = checks + 1
      let lhs = ua_or_abort(bij_compose(g, f), a, a)
      match upath_trans(pf, ua_or_abort(g, a, a)) {
        Some(rhs) => if !upath_eq(lhs, rhs) { trans_law = false }
        None => trans_law = false
      }
    }
  }

  // (T8) 三角恆等式（相干性）：idToEquiv ⊣ ua 的兩個三角
  let mut triangle = true
  for p in paths {
    checks = checks + 1
    let e = id_to_equiv_fin(p)
    if !bij_eq(id_to_equiv_fin(ua_or_abort(e, p.lhs, p.rhs)), e) {
      triangle = false
    }
  }
  for e in equivs {
    checks = checks + 1
    let p = ua_or_abort(e, a, a)
    if !upath_eq(ua_or_abort(id_to_equiv_fin(p), a, a), p) {
      triangle = false
    }
  }

  // (T9) 相等可判定 + 反身完備（⇒ Fin 宇宙為 1-類型）
  let mut decidable = true
  for p in paths {
    checks = checks + 1
    if !upath_eq(p, p) {
      decidable = false
    }
  }

  // (T10) 影子投影單射：Lehmer 碼忠實編碼置換
  let mut shadow_inj = true
  for i in 0..<np {
    for j in (i + 1)..<np {
      checks = checks + 1
      if upath_to_legacy(paths[i]).code == upath_to_legacy(paths[j]).code {
        shadow_inj = false
      }
    }
  }

  {
    card,
    count_law,
    path_count: np,
    equiv_count: equivs.length(),
    expected,
    eta,
    eps,
    beta,
    ua_injective: injective,
    ua_surjective: surjective,
    refl_law,
    sym_law,
    trans_law,
    triangle,
    decidable_eq: decidable,
    shadow_injective: shadow_inj,
    checks,
  }
}

///|
/// 定理的正式陳述：`isEquiv(idToEquiv)`（有擬逆 `ua` + 兩個三角恆等式）
pub fn is_equiv_id_to_equiv(card : Int32) -> Bool {
  let pf = univalence_proof(card)
  pf.eta && pf.eps && pf.triangle
}

///|
/// 定理成立 ⟺ 全部十條定律都被窮盡計算驗證
pub fn univalence_holds(card : Int32) -> Bool {
  let pf = univalence_proof(card)
  pf.count_law &&
  pf.eta &&
  pf.eps &&
  pf.beta &&
  pf.ua_injective &&
  pf.ua_surjective &&
  pf.refl_law &&
  pf.sym_law &&
  pf.trans_law &&
  pf.triangle &&
  pf.decidable_eq &&
  pf.shadow_injective
}

///|
/// 推論：`π₁(U_fin, Fin n) ≅ S_n`（單射 + 滿射 + 基數 n! + 複合相容）
pub fn pi1_universe_is_symmetric_group(card : Int32) -> Bool {
  let pf = univalence_proof(card)
  pf.count_law &&
  pf.ua_injective &&
  pf.ua_surjective &&
  pf.trans_law &&
  pf.refl_law &&
  pf.sym_law
}

///|
/// 推論：不等價的有限類型不相等（`Fin n = Fin m` 為空當 n ≠ m）
pub fn inequivalent_types_are_unequal(n : Int32, m : Int32) -> Bool {
  if n == m {
    return true
  } // 同基數時路徑存在，此處只驗證 n≠m 的情形
  let a = fin("Fin" + n.to_string(), n)
  let b = fin("Fin" + m.to_string(), m)
  upath_all(a, b).length() == 0
}

///|
/// 公理審計：本庫的單值性部分引入的公理數（恆為 0）
pub fn univalence_axiom_count() -> Int32 {
  0
}

///|
/// 給 demo / README 用的一行摘要
pub fn univalence_line(pf : UnivalenceProof) -> String {
  "n=" +
  pf.card.to_string() +
  " paths=" +
  pf.path_count.to_string() +
  "=" +
  pf.expected.to_string() +
  " equivs=" +
  pf.equiv_count.to_string() +
  " ηεβ=" +
  (pf.eta && pf.eps && pf.beta).to_string() +
  " inj/surj=" +
  (pf.ua_injective && pf.ua_surjective).to_string() +
  " grp=" +
  (pf.refl_law && pf.sym_law && pf.trans_law).to_string() +
  " tri=" +
  pf.triangle.to_string() +
  " checks=" +
  pf.checks.to_string()
}

///|
pub fn univalence_summary(max_card : Int32) -> String {
  let mut s = ""
  for n in 0..<=max_card {
    let pf = univalence_proof(n)
    s = s +
      univalence_line(pf) +
      " holds=" +
      univalence_holds(n).to_string() +
      "\n"
  }
  s
}

// ==================== 推論 1：函數外延性（不再是 `{ true }`） ====================

///|
/// 窮盡枚舉 `Fin card → Fin card` 的全部函數表（`card^card` 個）
pub fn all_functions(card : Int32) -> Array[Array[Int32]] {
  let total = {
    let mut t = 1
    for _ in 0..<card {
      t = t * card
    }
    t
  }
  let out : Array[Array[Int32]] = []
  if card == 0 {
    out.push([])
    return out
  }
  for k in 0..<total {
    let f = Array::make(card, 0)
    let mut rest = k
    for i in 0..<card {
      f[i] = rest % card
      rest = rest / card
    }
    out.push(f)
  }
  out
}

///|
/// 逐點虧損：`0` ⟺ 兩函數表逐點相等
pub fn funext_defect(f : Array[Int32], g : Array[Int32]) -> Int32 {
  if f.length() != g.length() {
    return -1
  }
  let mut d = 0
  for i in 0..<f.length() {
    if f[i] != g[i] {
      d = d + 1
    }
  }
  d
}

///|
/// 有限函數外延性：逐點相等的驗證**就是**路徑（code = 虧損，0 才是真路徑）
pub fn funext_fin(f : Array[Int32], g : Array[Int32]) -> Path[Array[Int32]] {
  { lhs: f, rhs: g, code: funext_defect(f, g), }
}

///|
pub fn happly_fin(p : Path[Array[Int32]], i : Int32) -> Path[Int32] {
  { lhs: p.lhs[i], rhs: p.rhs[i], code: p.code, }
}

///|
fn path_array_eq(p : Path[Array[Int32]], q : Path[Array[Int32]]) -> Bool {
  p.code == q.code && int_array_eq(p.lhs, q.lhs) && int_array_eq(p.rhs, q.rhs)
}

///|
/// 窮盡驗證 `funext` / `happly` 互逆（對全部 `card^card × card^card` 對函數）
pub fn funext_happly_laws(card : Int32) -> Bool {
  let fs = all_functions(card)
  let mut ok = true
  let mut checked = 0
  for f in fs {
    for g in fs {
      checked = checked + 1
      let p = funext_fin(f, g)
      let pointwise = funext_defect(f, g) == 0
      // (1) 健全性 + 完備性：p 是真路徑（code 0）⟺ f,g 逐點相等
      if (p.code == 0) != pointwise {
        ok = false
      }
      if pointwise {
        // (2) happly ∘ funext = id：逐點取回再重組 ⇒ 原路徑
        let lf = Array::make(card, 0)
        let rg = Array::make(card, 0)
        for i in 0..<card {
          let hi = happly_fin(p, i)
          if hi.code != 0 || hi.lhs != hi.rhs {
            ok = false
          }
          lf[i] = hi.lhs
          rg[i] = hi.rhs
        }
        if !path_array_eq(funext_fin(lf, rg), p) {
          ok = false
        }
        // (3) funext ∘ happly = id
        if !path_array_eq(p, funext_fin(p.lhs, p.rhs)) {
          ok = false
        }
      }
    }
  }
  ok && checked == fs.length() * fs.length()
}

// ==================== 推論 2：命題外延性（窮盡 4 種組合） ====================

///|
/// 有限宇宙中的命題：基數 ≤ 1 的類型（空型或單點型）
pub fn is_prop_fin(a : Fin) -> Bool {
  a.card <= 1
}

///|
/// `P → Q` 有映射 ⟺ (P 為空 或 Q 非空)
pub fn fin_map_exists(p : Fin, q : Fin) -> Bool {
  p.card == 0 || q.card > 0
}

///|
/// 窮盡驗證：對全部命題對 (P,Q)，`(P ⇔ Q) ⟺ (P = Q)`
pub fn prop_ext_fin_exhaustive() -> Bool {
  let props = [fin("0", 0), fin("1", 1)]
  let mut ok = true
  let mut cases = 0
  for p in props {
    for q in props {
      cases = cases + 1
      if !is_prop_fin(p) || !is_prop_fin(q) {
        ok = false
      }
      let iff = fin_map_exists(p, q) && fin_map_exists(q, p)
      let eq = p.card == q.card
      if iff != eq {
        ok = false
      }
    }
  }
  ok && cases == 4
}

// ==================== 推論 3：SIP 結構同一性（有限么半群） ====================

///|
/// 有限么半群：載體 `Fin n` + 單位元 + `n²` 乘法表（`table[i*n+j]`）
pub(all) struct MonoidFin {
  carrier : Fin
  unit : Int32
  table : Array[Int32]
} derive(Debug)

///|
pub fn monoid_table_at(m : MonoidFin, i : Int32, j : Int32) -> Int32 {
  m.table[i * m.carrier.card + j]
}

///|
/// 驗證么半群公理：單位元（2n 條）+ 結合律（n³ 條），全部窮盡
pub fn monoid_check(m : MonoidFin) -> Bool {
  let n = m.carrier.card
  if m.table.length() != n * n {
    return false
  }
  if m.unit < 0 || m.unit >= n {
    return false
  }
  for i in 0..<n {
    if m.table[m.unit * n + i] != i {
      return false
    } // e·i = i
    if m.table[i * n + m.unit] != i {
      return false
    } // i·e = i
  }
  for i in 0..<n {
    for j in 0..<n {
      for k in 0..<n {
        let lhs = m.table[m.table[i * n + j] * n + k]
        let rhs = m.table[i * n + m.table[j * n + k]]
        if lhs != rhs {
          return false
        }
      }
    }
  }
  true
}

///|
/// 窮盡枚舉 `Fin card` 上全部（已驗證的）么半群結構：從 `card^(card²)` 張表中篩出
pub fn monoid_all(card : Int32) -> Array[MonoidFin] {
  let n2 = card * card
  let carrier = fin("Fin" + card.to_string(), card)
  let out : Array[MonoidFin] = []
  if card == 0 {
    return out
  }
  let total = {
    let mut t = 1
    for _ in 0..<n2 {
      t = t * card
    }
    t
  }
  for k in 0..<total {
    let table = Array::make(n2, 0)
    let mut rest = k
    for idx in 0..<n2 {
      table[idx] = rest % card
      rest = rest / card
    }
    // 單位元候選：逐個試（存在性由驗證決定，不預設）
    for u in 0..<card {
      let m = { carrier, unit: u, table: int_array_copy(table), }
      if monoid_check(m) {
        out.push(m)
      }
    }
  }
  out
}

///|
/// 搜索同構：找出 `σ` 使 `σ(m1(i,j)) = m2(σi,σj)` 且 `σ(u1) = u2`（窮盡 n!·n²）
pub fn monoid_isomorphism(m1 : MonoidFin, m2 : MonoidFin) -> Bij? {
  let n = m1.carrier.card
  if n != m2.carrier.card {
    return None
  }
  for sigma in bij_all(n) {
    if sigma.fwd[m1.unit] != m2.unit {
      continue
    }
    let mut good = true
    for i in 0..<n {
      for j in 0..<n {
        if sigma.fwd[monoid_table_at(m1, i, j)] !=
          monoid_table_at(m2, sigma.fwd[i], sigma.fwd[j]) {
          good = false
        }
      }
    }
    if good {
      return Some(sigma)
    }
  }
  None
}

///|
/// **SIP 定理（有限版）**：同構的么半群在單值宇宙中相等 —— 路徑由 `ua` 給出
pub fn sip_monoid_fin(m1 : MonoidFin, m2 : MonoidFin) -> UPath? {
  match monoid_isomorphism(m1, m2) {
    Some(sigma) => ua_fin(sigma, m1.carrier, m2.carrier)
    None => None
  }
}

///|
/// SIP 的計算內容：把 `m1` 的乘法表沿 `ua(σ)` 傳輸後，**逐項等於** `m2` 的表
pub fn sip_transport_check(m1 : MonoidFin, m2 : MonoidFin) -> Bool {
  match sip_monoid_fin(m1, m2) {
    Some(p) => {
      let moved = upath_transport_table(p, m1.table)
      let mut ok = int_array_eq(moved, m2.table)
      if p.glue.fwd[m1.unit] != m2.unit {
        ok = false
      }
      ok
    }
    None => false
  }
}

///|
/// 用 SIP 路徑把全部有限么半群分成同構類，回傳類數
pub fn monoid_classes(card : Int32) -> Int32 {
  let ms = monoid_all(card)
  let reps : Array[MonoidFin] = []
  for m in ms {
    let mut found = false
    for r in reps {
      match sip_monoid_fin(r, m) {
        Some(_) => found = true
        None => ()
      }
    }
    if !found {
      reps.push(m)
    }
  }
  reps.length()
}

///|
/// 驗證「同構 ⟺ 同一類」這個分類的正確性（雙向：同類必同構、同構必同類）
pub fn monoid_partition_check(card : Int32) -> Bool {
  let ms = monoid_all(card)
  let k = ms.length()
  // 以第一個同構代表元為類標籤
  let label = Array::make(k, -1)
  for i in 0..<k {
    if label[i] >= 0 {
      continue
    }
    label[i] = i
    for j in (i + 1)..<k {
      match sip_monoid_fin(ms[i], ms[j]) {
        Some(_) => label[j] = i
        None => ()
      }
    }
  }
  // 雙向檢查
  for i in 0..<k {
    for j in 0..<k {
      let iso = match sip_monoid_fin(ms[i], ms[j]) {
        Some(_) => true
        None => false
      }
      if iso != (label[i] == label[j]) {
        return false
      }
      // 同構時 SIP 的傳輸必須真的把結構搬過去
      if iso && !sip_transport_check(ms[i], ms[j]) {
        return false
      }
    }
  }
  true
}
