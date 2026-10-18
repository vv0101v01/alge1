///|
/// @file univalence_theorem_test.mbt
/// # 單值性定理的可執行證明
///
/// 對應 `hott_univalence_theorem.mbt`。這裡沒有任何 `assert_true(true)`：
/// 每個布林值都由 `univalence_proof` / `funext_happly_laws` / `monoid_partition_check`
/// 等函數在「有限宇宙 + glue 路徑」模型上**窮盡計算**得出。
/// 命令：`moon test -f univalence_theorem_test.mbt`
test "U0 公理審計：單值性引入的公理數 = 0" {
  assert_eq(@univalence.univalence_axiom_count(), 0)
}

///|
test "U1 定理主體：n = 0..5 的十條定律全部窮盡成立" {
  for n in 0..<=5 {
    let pf = @univalence.univalence_proof(n)
    // 基數律：|Fin n = Fin n| = n! = |Fin n ≃ Fin n|
    assert_eq(pf.path_count, pf.expected)
    assert_eq(pf.equiv_count, pf.expected)
    assert_eq(pf.expected, @univalence.factorial(n))
    assert_true(pf.count_law)
    // uaη : ua(idToEquiv p) = p ；uaε : idToEquiv(ua e) = e ；uaβ : transport(ua e) x = e x
    assert_true(pf.eta)
    assert_true(pf.eps)
    assert_true(pf.beta)
    // ua 為雙射（單射 + 滿射）
    assert_true(pf.ua_injective)
    assert_true(pf.ua_surjective)
    // 群胚函子性：ua 保 refl / sym / trans
    assert_true(pf.refl_law)
    assert_true(pf.sym_law)
    assert_true(pf.trans_law)
    // 三角恆等式（相干性）⇒ isEquiv(idToEquiv)，這就是單值性定理本身
    assert_true(pf.triangle)
    assert_true(@univalence.is_equiv_id_to_equiv(n))
    // 相等可判定 ⇒ Fin 宇宙是 1-類型；Lehmer 影子投影單射
    assert_true(pf.decidable_eq)
    assert_true(pf.shadow_injective)
    assert_true(@univalence.univalence_holds(n))
  }
}

///|
test "U2 定理主體：n = 6 窮盡（720 條路徑，> 1.5M 次原子比較）" {
  let pf = @univalence.univalence_proof(6)
  assert_eq(pf.path_count, 720)
  assert_eq(pf.equiv_count, 720)
  assert_true(pf.checks > 1500000)
  assert_true(@univalence.univalence_holds(6))
  assert_true(@univalence.pi1_universe_is_symmetric_group(6))
}

///|
test "U3 推論：π₁(U_fin, Fin n) ≅ S_n" {
  for n in 0..<=5 {
    assert_true(@univalence.pi1_universe_is_symmetric_group(n))
  }
}

///|
test "U4 Lehmer 影子投影：S_n → [0,n!) 是雙射，且 refl ↦ code 0" {
  for n in 1..<=4 {
    let total = @univalence.factorial(n)
    let seen : Array[Int32] = Array::make(total, 0)
    for sigma in @univalence.bij_all(n) {
      let c = @univalence.lehmer_code(sigma)
      assert_true(c >= 0 && c < total)
      assert_eq(seen[c], 0) // 單射
      seen[c] = 1
    }
    for c in 0..<total {
      assert_eq(seen[c], 1) // 滿射 ⇒ 雙射
    }
  }
  let a = @univalence.fin("Fin3", 3)
  assert_eq(@univalence.upath_to_legacy(@univalence.upath_refl(a)).code, 0)
}

///|
test "U5 ua 的定義域：只接受已驗證的等價，且 uaβ/η 在具體置換上成立" {
  let a = @univalence.fin("Fin3", 3)
  // σ = (0 1 2) 三元循環
  let sigma = match @univalence.bij_make(3, [1, 2, 0]) {
    Some(s) => s
    None => abort("test: (0 1 2) should be a verified bijection")
  }
  let p = match @univalence.ua_fin(sigma, a, a) {
    Some(p0) => p0
    None => abort("test: ua rejected a verified equivalence")
  }
  // uaβ：transport along ua(σ) 就是 σ 本身
  assert_eq(@univalence.upath_transport(p, 0), 1)
  assert_eq(@univalence.upath_transport(p, 1), 2)
  assert_eq(@univalence.upath_transport(p, 2), 0)
  // uaε：idToEquiv(ua σ) = σ
  assert_true(@univalence.bij_eq(@univalence.id_to_equiv_fin(p), sigma))
  // uaη：ua(idToEquiv p) = p
  let p2 = match @univalence.ua_fin(@univalence.id_to_equiv_fin(p), a, a) {
    Some(q) => q
    None => abort("test: ua rejected idToEquiv of a path")
  }
  assert_true(@univalence.upath_eq(p2, p))
  // sym / trans 對應 逆置換 / 複合
  assert_eq(@univalence.upath_transport(@univalence.upath_sym(p), 1), 0)
  let pp = match @univalence.upath_trans(p, p) {
    Some(q) => q
    None => abort("test: trans of two endo-paths must exist")
  }
  assert_eq(@univalence.upath_transport(pp, 0), 2) // σ² = (0 2 1)
  // 非雙射的函數表被 bij_make 拒絕 ⇒ ua 沒有「未驗證」的輸入
  match @univalence.bij_make(3, [0, 0, 1]) {
    Some(_) => abort("test: a non-injective map must not become an equivalence")
    None => ()
  }
  match @univalence.bij_make(3, [0, 1, 3]) {
    Some(_) => abort("test: an out-of-range map must not become an equivalence")
    None => ()
  }
}

///|
test "U6 不等價 ⇒ 不相等；等價 ⇒ 相等（與名字無關）" {
  assert_true(@univalence.inequivalent_types_are_unequal(2, 3))
  assert_true(@univalence.inequivalent_types_are_unequal(0, 5))
  let a = @univalence.fin("Fin2", 2)
  let b = @univalence.fin("Fin3", 3)
  assert_eq(@univalence.upath_all(a, b).length(), 0)
  // 基數相同但名字不同：路徑仍然存在（單值性的要點：等價即相等）
  let renamed = @univalence.fin("Fin2-alias", 2)
  assert_eq(@univalence.upath_all(a, renamed).length(), 2)
}

///|
test "C1 推論：函數外延性 funext/happly 互逆（窮盡 nⁿ × nⁿ 對函數）" {
  assert_true(@univalence.funext_happly_laws(1))
  assert_true(@univalence.funext_happly_laws(2))
  assert_true(@univalence.funext_happly_laws(3))
  assert_true(@univalence.funext_happly_laws(4)) // 256² = 65536 對
  assert_true(@univalence.funext_happly_is_equiv())
  // 虧損碼語義：逐點相等 ⟺ code 0（真路徑）
  assert_eq(@univalence.funext_defect([0, 1, 2], [0, 1, 2]), 0)
  assert_eq(@univalence.funext_defect([0, 1, 2], [0, 2, 1]), 2)
  assert_eq(@univalence.funext_fin([0, 1], [0, 1]).code, 0)
  assert_eq(@univalence.funext_fin([0, 1], [1, 0]).code, 2)
  assert_eq(@univalence.all_functions(3).length(), 27)
}

///|
test "C2 推論：命題外延性 (P ⇔ Q) ⟺ (P = Q)（4 種組合窮盡）" {
  assert_true(@univalence.prop_ext_fin_exhaustive())
  assert_true(@univalence.prop_ext_is_theorem())
  assert_true(@univalence.is_prop_fin(@univalence.fin("0", 0)))
  assert_true(@univalence.is_prop_fin(@univalence.fin("1", 1)))
  assert_true(!@univalence.is_prop_fin(@univalence.fin("2", 2)))
  // 空型 → 任何類型有映射；非空型 → 空型無映射
  assert_true(@univalence.fin_map_exists(@univalence.fin("0", 0), @univalence.fin("1", 1)))
  assert_true(!@univalence.fin_map_exists(@univalence.fin("1", 1), @univalence.fin("0", 0)))
}

///|
test "C3 推論：SIP — 同構的么半群在單值宇宙中相等" {
  // 已標號么半群數 1, 4, 33（n = 1, 2, 3）— 對照 OEIS A058153
  assert_eq(@univalence.monoid_all(1).length(), 1)
  assert_eq(@univalence.monoid_all(2).length(), 4)
  assert_eq(@univalence.monoid_all(3).length(), 33)
  // 同構類數 1, 2, 7 — 對照 OEIS A058129
  assert_eq(@univalence.monoid_classes(1), 1)
  assert_eq(@univalence.monoid_classes(2), 2)
  assert_eq(@univalence.monoid_classes(3), 7)
  // 分類正確性：同構 ⟺ 同一類；且同構時沿 ua(σ) 傳輸後乘法表逐項相等
  assert_true(@univalence.monoid_partition_check(2))
  assert_true(@univalence.monoid_partition_check(3))
  assert_true(@univalence.sip_is_theorem(3))
}

///|
test "C4 推論：uaβ 窮盡證明 + 舊 API 的 uaη" {
  assert_true(@univalence.ua_beta_is_theorem(4))
  assert_true(@univalence.ua_beta_is_theorem(5))
  assert_true(
    @hott_core.ua_eta_legacy(
      fn(x : Int32) -> Int32 { x },
      fn(x : Int32) -> Int32 { x },
      @hott_core.TypeTag("A"),
    ),
  )
  // 虧損非 0 的假等價：uaβ 的見證 code 也非 0，可被檢測（不會被誤當成 refl）
  let bad : @hott_core.Equiv[Int32, Int32] = {
    to: fn(x) { x },
    from: fn(x) { x },
    left_inv_code: 1,
    right_inv_code: 2,
  }
  assert_eq(
    @univalence.ua_beta(bad, @hott_core.TypeTag("A"), @hott_core.TypeTag("B"), 5).code,
    3,
  )
}

///|
test "C5 有限宇宙是 1-類型（相等可判定 ⇒ 無高階結構）" {
  assert_eq(@univalence.fin_universe_hlevel(3), @hott_core.GroupoidLevel)
  assert_eq(
    @univalence.hlevel_preserved_by_univalence(@hott_core.GroupoidLevel),
    @hott_core.GroupoidLevel,
  )
  for n in 0..<=4 {
    assert_true(@univalence.univalence_proof(n).decidable_eq)
  }
}

test "hott: equiv and ua (定理化：ua 不再是公理)" {
  let e = @hott_core.Equiv::make(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x })
  assert_eq(e.is_equiv(), true)
  let tagA = @hott_core.TypeTag("A")
  let tagB = @hott_core.TypeTag("B")
  let pathAB = @hott_core.ua(e, tagA, tagB)
  // 舊實作憑空加了常數 10（公理）；現在 code = 等價自身的虧損碼，已驗證等價 ⇒ 0（原子路徑）
  assert_eq(pathAB.code, @hott_core.equiv_defect(e))
  assert_eq(pathAB.code, 0)
  // uaη：ua(idToEquiv(refl A)) 結構上就是 refl A
  assert_true(@hott_core.ua_eta_legacy(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x }, tagA))
  // uaβ：transport along ua(e) 定義上就是 e.to（glue 消除規則），見證為 refl
  let beta = @univalence.ua_beta(e, tagA, tagB, 7)
  assert_eq(beta.lhs, 7)
  assert_eq(beta.rhs, 7)
  assert_eq(beta.code, 0)
  // 虧損非 0 的「假等價」不會被當成合法路徑（code > 0 可被檢測出來）
  let bad : @hott_core.Equiv[Int, Int] = { to: fn(x) { x }, from: fn(x) { x }, left_inv_code: 3, right_inv_code: 4 }
  assert_eq(@hott_core.ua(bad, tagA, tagB).code, 7)
  assert_eq(@univalence.ua_beta(bad, tagA, tagB, 1).code, 7)
  // 完整的窮盡證明見 univalence_theorem_test.mbt
  assert_eq(@univalence.univalence_axiom_count(), 0)
  assert_true(@univalence.univalence_holds(3))
}
