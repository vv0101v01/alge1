///|
/// @file univalence_theorem_test.mbt
/// # 單值性定理的可執行證明
///
/// 對應 `hott_univalence_theorem.mbt`。這裡沒有任何 `assert_true(true)`：
/// 每個布林值都由 `univalence_proof` / `funext_happly_laws` / `monoid_partition_check`
/// 等函數在「有限宇宙 + glue 路徑」模型上**窮盡計算**得出。
/// 命令：`moon test -f univalence_theorem_test.mbt`
test "U0 公理審計：單值性引入的公理數 = 0" {
  assert_eq(@axiom.univalence_axiom_count(), 0)
}

///|
test "U1 定理主體：n = 0..5 的十條定律全部窮盡成立" {
  for n in 0..<=5 {
    let pf = @axiom.univalence_proof(n)
    // 基數律：|Fin n = Fin n| = n! = |Fin n ≃ Fin n|
    assert_eq(pf.path_count, pf.expected)
    assert_eq(pf.equiv_count, pf.expected)
    assert_eq(pf.expected, @axiom.factorial(n))
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
    assert_true(@axiom.is_equiv_id_to_equiv(n))
    // 相等可判定 ⇒ Fin 宇宙是 1-類型；Lehmer 影子投影單射
    assert_true(pf.decidable_eq)
    assert_true(pf.shadow_injective)
    assert_true(@axiom.univalence_holds(n))
  }
}

///|
test "U2 定理主體：n = 6 窮盡（720 條路徑，> 1.5M 次原子比較）" {
  let pf = @axiom.univalence_proof(6)
  assert_eq(pf.path_count, 720)
  assert_eq(pf.equiv_count, 720)
  assert_true(pf.checks > 1500000)
  assert_true(@axiom.univalence_holds(6))
  assert_true(@axiom.pi1_universe_is_symmetric_group(6))
}

///|
test "U3 推論：π₁(U_fin, Fin n) ≅ S_n" {
  for n in 0..<=5 {
    assert_true(@axiom.pi1_universe_is_symmetric_group(n))
  }
}

///|
test "U4 Lehmer 影子投影：S_n → [0,n!) 是雙射，且 refl ↦ code 0" {
  for n in 1..<=4 {
    let total = @axiom.factorial(n)
    let seen : Array[Int32] = Array::make(total, 0)
    for sigma in @axiom.bij_all(n) {
      let c = @axiom.lehmer_code(sigma)
      assert_true(c >= 0 && c < total)
      assert_eq(seen[c], 0) // 單射
      seen[c] = 1
    }
    for c in 0..<total {
      assert_eq(seen[c], 1) // 滿射 ⇒ 雙射
    }
  }
  let a = @axiom.fin("Fin3", 3)
  assert_eq(@axiom.upath_to_legacy(@axiom.upath_refl(a)).code, 0)
}

///|
test "U5 ua 的定義域：只接受已驗證的等價，且 uaβ/η 在具體置換上成立" {
  let a = @axiom.fin("Fin3", 3)
  // σ = (0 1 2) 三元循環
  let sigma = match @axiom.bij_make(3, [1, 2, 0]) {
    Some(s) => s
    None => abort("test: (0 1 2) should be a verified bijection")
  }
  let p = match @axiom.ua_fin(sigma, a, a) {
    Some(p0) => p0
    None => abort("test: ua rejected a verified equivalence")
  }
  // uaβ：transport along ua(σ) 就是 σ 本身
  assert_eq(@axiom.upath_transport(p, 0), 1)
  assert_eq(@axiom.upath_transport(p, 1), 2)
  assert_eq(@axiom.upath_transport(p, 2), 0)
  // uaε：idToEquiv(ua σ) = σ
  assert_true(@axiom.bij_eq(@axiom.id_to_equiv_fin(p), sigma))
  // uaη：ua(idToEquiv p) = p
  let p2 = match @axiom.ua_fin(@axiom.id_to_equiv_fin(p), a, a) {
    Some(q) => q
    None => abort("test: ua rejected idToEquiv of a path")
  }
  assert_true(@axiom.upath_eq(p2, p))
  // sym / trans 對應 逆置換 / 複合
  assert_eq(@axiom.upath_transport(@axiom.upath_sym(p), 1), 0)
  let pp = match @axiom.upath_trans(p, p) {
    Some(q) => q
    None => abort("test: trans of two endo-paths must exist")
  }
  assert_eq(@axiom.upath_transport(pp, 0), 2) // σ² = (0 2 1)
  // 非雙射的函數表被 bij_make 拒絕 ⇒ ua 沒有「未驗證」的輸入
  match @axiom.bij_make(3, [0, 0, 1]) {
    Some(_) => abort("test: a non-injective map must not become an equivalence")
    None => ()
  }
  match @axiom.bij_make(3, [0, 1, 3]) {
    Some(_) => abort("test: an out-of-range map must not become an equivalence")
    None => ()
  }
}

///|
test "U6 不等價 ⇒ 不相等；等價 ⇒ 相等（與名字無關）" {
  assert_true(@axiom.inequivalent_types_are_unequal(2, 3))
  assert_true(@axiom.inequivalent_types_are_unequal(0, 5))
  let a = @axiom.fin("Fin2", 2)
  let b = @axiom.fin("Fin3", 3)
  assert_eq(@axiom.upath_all(a, b).length(), 0)
  // 基數相同但名字不同：路徑仍然存在（單值性的要點：等價即相等）
  let renamed = @axiom.fin("Fin2-alias", 2)
  assert_eq(@axiom.upath_all(a, renamed).length(), 2)
}

///|
test "C1 推論：函數外延性 funext/happly 互逆（窮盡 nⁿ × nⁿ 對函數）" {
  assert_true(@axiom.funext_happly_laws(1))
  assert_true(@axiom.funext_happly_laws(2))
  assert_true(@axiom.funext_happly_laws(3))
  assert_true(@axiom.funext_happly_laws(4)) // 256² = 65536 對
  assert_true(@axiom.funext_happly_is_equiv())
  // 虧損碼語義：逐點相等 ⟺ code 0（真路徑）
  assert_eq(@axiom.funext_defect([0, 1, 2], [0, 1, 2]), 0)
  assert_eq(@axiom.funext_defect([0, 1, 2], [0, 2, 1]), 2)
  assert_eq(@axiom.funext_fin([0, 1], [0, 1]).code, 0)
  assert_eq(@axiom.funext_fin([0, 1], [1, 0]).code, 2)
  assert_eq(@axiom.all_functions(3).length(), 27)
}

///|
test "C2 推論：命題外延性 (P ⇔ Q) ⟺ (P = Q)（4 種組合窮盡）" {
  assert_true(@axiom.prop_ext_fin_exhaustive())
  assert_true(@axiom.prop_ext_is_theorem())
  assert_true(@axiom.is_prop_fin(@axiom.fin("0", 0)))
  assert_true(@axiom.is_prop_fin(@axiom.fin("1", 1)))
  assert_true(!@axiom.is_prop_fin(@axiom.fin("2", 2)))
  // 空型 → 任何類型有映射；非空型 → 空型無映射
  assert_true(@axiom.fin_map_exists(@axiom.fin("0", 0), @axiom.fin("1", 1)))
  assert_true(!@axiom.fin_map_exists(@axiom.fin("1", 1), @axiom.fin("0", 0)))
}

///|
test "C3 推論：SIP — 同構的么半群在單值宇宙中相等" {
  // 已標號么半群數 1, 4, 33（n = 1, 2, 3）— 對照 OEIS A058153
  assert_eq(@axiom.monoid_all(1).length(), 1)
  assert_eq(@axiom.monoid_all(2).length(), 4)
  assert_eq(@axiom.monoid_all(3).length(), 33)
  // 同構類數 1, 2, 7 — 對照 OEIS A058129
  assert_eq(@axiom.monoid_classes(1), 1)
  assert_eq(@axiom.monoid_classes(2), 2)
  assert_eq(@axiom.monoid_classes(3), 7)
  // 分類正確性：同構 ⟺ 同一類；且同構時沿 ua(σ) 傳輸後乘法表逐項相等
  assert_true(@axiom.monoid_partition_check(2))
  assert_true(@axiom.monoid_partition_check(3))
  assert_true(@axiom.sip_is_theorem(3))
}

///|
test "C4 推論：uaβ 窮盡證明 + 舊 API 的 uaη" {
  assert_true(@axiom.ua_beta_is_theorem(4))
  assert_true(@axiom.ua_beta_is_theorem(5))
  assert_true(
    @axiom.ua_eta_legacy(
      fn(x : Int32) -> Int32 { x },
      fn(x : Int32) -> Int32 { x },
      @axiom.TypeTag("A"),
    ),
  )
  // 虧損非 0 的假等價：uaβ 的見證 code 也非 0，可被檢測（不會被誤當成 refl）
  let bad : @axiom.Equiv[Int32, Int32] = {
    to: fn(x) { x },
    from: fn(x) { x },
    left_inv_code: 1,
    right_inv_code: 2,
  }
  assert_eq(
    @axiom.ua_beta(bad, @axiom.TypeTag("A"), @axiom.TypeTag("B"), 5).code,
    3,
  )
}

///|
test "C5 有限宇宙是 1-類型（相等可判定 ⇒ 無高階結構）" {
  assert_eq(@axiom.fin_universe_hlevel(3), @axiom.GroupoidLevel)
  assert_eq(
    @axiom.hlevel_preserved_by_univalence(@axiom.GroupoidLevel),
    @axiom.GroupoidLevel,
  )
  for n in 0..<=4 {
    assert_true(@axiom.univalence_proof(n).decidable_eq)
  }
}

///|
test "U7 demo 輸出：公理數 0、定理成立、SIP 分類 7" {
  let s = @axiom.univalence_theorem_demo()
  assert_true(s.contains("univalence_thm: axioms=0"))
  assert_true(s.contains("holds=true"))
  assert_true(s.contains("pi1_S3=true"))
  assert_true(s.contains("ua_beta=true"))
  assert_true(s.contains("funext=true"))
  assert_true(s.contains("prop_ext=true"))
  assert_true(s.contains("sip_classes=7"))
  // 摘要逐行可讀（供 README / docs 引用）
  let summary = @axiom.univalence_summary(4)
  assert_true(summary.contains("n=3 paths=6=6 equivs=6"))
  assert_true(summary.contains("holds=true"))
}
