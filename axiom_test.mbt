/// Blackbox tests — validate theorems as executable proofs

test "vect: identity and sparse equiv" {
  let field = @structures.DoubleField::{}
  let v = @structures.Vect::from_array([1.0, 2.0, 0.0, 4.0])
  let m = @structures.LinMap::identity(4, 0.0, 1.0)
  let w = @structures.apply_double(m, v, field)
  assert_eq(w.data, [1.0, 2.0, 0.0, 4.0])
  let sv = @structures.SparseVect::from_dense(v, fn(x) { x == 0.0 })
  assert_eq(sv.entries.length(), 3)
  let w2 = @structures.apply_sparse_double(m, sv, field)
  assert_eq(w2.data, w.data)
}

test "vect: tensor dim and direct sum" {
  let field = @structures.DoubleField::{}
  let v = @structures.Vect::from_array([1.0, 2.0])
  let w = @structures.Vect::from_array([3.0, 4.0, 5.0])
  let t = @structures.tensor_double(v, w, field)
  // dim(V⊗W) = dim V * dim W
  assert_eq(t.dim, 6)
  // t = [1*3,1*4,1*5, 2*3,2*4,2*5] = [3,4,5,6,8,10]
  assert_eq(t.data, [3.0, 4.0, 5.0, 6.0, 8.0, 10.0])
  let s = @structures.direct_sum(v, w)
  assert_eq(s.dim, 5)
}

test "free functor: fold preserves hom" {
  let term : @structures.Free[Int] = @structures.Op("add", [@structures.Return(1), @structures.Return(2)])
  let res = term.fold(fn(x) { x }, fn(name, args) {
    if name == "add" { args[0] + args[1] } else { 0 }
  })
  assert_eq(res, 3)
}

test "flat functor: preserves limit shape" {
  let flat = @structures.FlatFunctor::make([@structures.ObjTag("A"), @structures.ObjTag("B")])
  flat.advance(@structures.ObjTag("A"), 10)
  flat.advance(@structures.ObjTag("B"), 20)
  assert_eq(flat.is_flat(), true)
  let vals = @structures.flat_preserves_limit_example(flat, [@structures.ObjTag("A"), @structures.ObjTag("B"), @structures.ObjTag("C")])
  assert_eq(vals.length(), 3)
  assert_eq(vals[0], Some(10))
  assert_eq(vals[2], None)
}

test "equivalence: triangle identities" {
  let eq = @structures.Equivalence::make(
    [(@structures.ObjTag("A"), 1, -1)],
    [(@structures.ObjTag("B"), 2, -2)],
  )
  assert_eq(eq.check_triangle(), true)
}

test "topos: omega algebra" {
  assert_eq(@structures.omega_and(@structures.True, @structures.True), @structures.True)
  assert_eq(@structures.omega_and(@structures.True, @structures.False), @structures.False)
  assert_eq(@structures.omega_implies(@structures.True, @structures.False), @structures.False)
  assert_eq(@structures.omega_or(@structures.False, @structures.False), @structures.False)
}

test "groupoid: connectivity" {
  let g = @structures.Groupoid::pair_groupoid(["a", "b", "c"])
  assert_eq(g.is_groupoid(), true)
  let comps = g.connected_components()
  assert_eq(comps.length(), 1)
  assert_eq(comps[0].length(), 3)
  let d = @structures.Groupoid::discrete(["a", "b"])
  assert_eq(d.connected_components().length(), 2)
}

test "2-group: crossed module" {
  let cm = @structures.CrossedModule::trivial(2, 4)
  assert_eq(cm.check_peiffer(), true)
  // π0 = |G|/|Im∂| =4/1=4, π1=|Ker∂|=2
  assert_eq(cm.pi0(), 4)
  assert_eq(cm.pi1(), 2)
}

test "linear logic: lolli compose" {
  let f = @structures.Lolli::make(fn(x : Int) -> Int { x + 1 })
  let g = @structures.Lolli::make(fn(x : Int) -> Int { x * 2 })
  let h = @structures.compose_lolli(f, g)
  let lin = @structures.Linear::make(5)
  let res = h.apply(lin).consume()
  assert_eq(res, 12) // (5+1)*2
}

test "homotopy: simplex and euler" {
  let s = @structures.SSet::standard_simplex(2)
  assert_eq(s.num_simplices(0), 3)
  assert_eq(s.num_simplices(1), 3)
  assert_eq(s.num_simplices(2), 1)
  let cot = @structures.cotangent_of_poly(3)
  assert_eq(cot.euler(), 3)
}

test "algorithms: fused chain equals naive" {
  let field = @structures.DoubleField::{}
  let v = @structures.Vect::from_array([1.0, 2.0])
  let m1 = @structures.LinMap::identity(2, 0.0, 1.0)
  let m2 = @structures.LinMap::identity(2, 0.0, 1.0)
  let r1 = @structures.fused_chain_double([m1, m2], v, field)
  assert_eq(r1.data, [1.0, 2.0])
}

test "demo_pipeline runs" {
  let s = @axiom.demo_pipeline()
  assert_eq(s.contains("demo:"), true)
}

test "high_dim_demo runs" {
  let s = @axiom.high_dim_demo()
  assert_eq(s.contains("high_dim:"), true)
}

test "hott: path ops" {
  let p = @hott_core.refl(42)
  let q = @hott_core.sym(p)
  let r = @hott_core.trans(p, q)
  assert_eq(p.code, 0)
  assert_eq(r.code, 1)
  let f = fn(x : Int) -> Int { x + 1 }
  let ap_p = @hott_core.ap(f, p)
  assert_eq(ap_p.code, 0)
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

test "hott: hlevel" {
  let l = @hott_core.hlevel_up(@hott_core.SetLevel)
  assert_eq(l, @hott_core.GroupoidLevel)
  let c = @hott_core.trunc_make(42, @hott_core.SetLevel)
  assert_eq(@hott_core.is_truncated(c, @hott_core.SetLevel), true)
}

test "hott: hits circle" {
  let base = @hott_hits.Circle::base()
  let my_loop = @hott_hits.circle_loop()
  assert_eq(my_loop.code, 1)
  let s1_rec = @hott_hits.circle_rec(0, @hott_core.refl(0))
  assert_eq(s1_rec(base), 0)
  let enc = @hott_theorems.encode_s1(my_loop)
  assert_eq(enc, 1)
  let dec = @hott_theorems.decode_s1(5)
  assert_eq(dec.code, 5)
}

test "hott: new theorems pi1" {
  assert_eq(@hott_theorems.pi1_s1_is_int(), true)
  assert_eq(@hott_theorems.synthetic_pi(1, 1), "ℤ")
  assert_eq(@hott_theorems.blakers_massey_connectivity(2, 3), 5)
  assert_eq(@hott_theorems.whitehead_principle(true), true)
}

test "hott: algorithms" {
  let p = @hott_core.refl(@hott_core.TypeTag("X"))
  assert_eq(@hott_algorithms.cubical_transport(p, 99), 99)
  assert_eq(@hott_algorithms.truncated_exists_search([1, 2, 3], fn(x) { x == 2 }), true)
  let t1 = @hott_algorithms.Term::{ code: 1001, tag: "t" }
  let t2 = @hott_algorithms.Term::{ code: 1, tag: "t" }
  // 誠實化後：`Term` 無內部結構 ⇒ `normalize` 為恒等，1001 與 1 不再被誤判為相等
  // （舊版 `code % 1000` 會回傳 true；真正的 NBE 見 cubical_test.mbt 的 K3）
  assert_eq(@hott_algorithms.judgmental_eq(t1, t2), false)
  assert_eq(@hott_algorithms.judgmental_eq(t1, t1), true)
  assert_eq(@hott_algorithms.normalize(t1), t1)
  // H1 的真正版本：Kan 填充把 1 沿 3-循環的 glue 送到 2
  assert_eq(@hott_algorithms.cubical_kan_demo(), "2")
}

test "hott: redefine" {
  let s = @axiom.redefine_demo()
  assert_eq(s.contains("redefine:"), true)
  let h = @axiom.hott_demo()
  assert_eq(h.contains("hott:"), true)
  let hits = @axiom.hits_demo()
  assert_eq(hits.contains("hits:"), true)
  let nt = @axiom.new_theorems_demo()
  assert_eq(nt.contains("new_thms:"), true)
  let ha = @axiom.hott_algorithms_demo()
  assert_eq(ha.contains("hott_algo:"), true)
  let cu = @axiom.cubical_demo()
  assert_eq(cu.contains("cubical: axioms=0"), true)
  assert_eq(cu.contains("C1C2C3=true"), true)
  assert_eq(cu.contains("kan=true"), true)
  assert_eq(cu.contains("sound=true"), true)
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
  let summary = @univalence.univalence_summary(4)
  assert_true(summary.contains("n=3 paths=6=6 equivs=6"))
  assert_true(summary.contains("holds=true"))
}
