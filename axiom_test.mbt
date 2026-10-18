/// Blackbox tests — validate theorems as executable proofs

test "vect: identity and sparse equiv" {
  let field = @axiom.DoubleField::{}
  let v = @axiom.Vect::from_array([1.0, 2.0, 0.0, 4.0])
  let m = @axiom.LinMap::identity(4, 0.0, 1.0)
  let w = @axiom.apply_double(m, v, field)
  assert_eq(w.data, [1.0, 2.0, 0.0, 4.0])
  let sv = @axiom.SparseVect::from_dense(v, fn(x) { x == 0.0 })
  assert_eq(sv.entries.length(), 3)
  let w2 = @axiom.apply_sparse_double(m, sv, field)
  assert_eq(w2.data, w.data)
}

test "vect: tensor dim and direct sum" {
  let field = @axiom.DoubleField::{}
  let v = @axiom.Vect::from_array([1.0, 2.0])
  let w = @axiom.Vect::from_array([3.0, 4.0, 5.0])
  let t = @axiom.tensor_double(v, w, field)
  // dim(V⊗W) = dim V * dim W
  assert_eq(t.dim, 6)
  // t = [1*3,1*4,1*5, 2*3,2*4,2*5] = [3,4,5,6,8,10]
  assert_eq(t.data, [3.0, 4.0, 5.0, 6.0, 8.0, 10.0])
  let s = @axiom.direct_sum(v, w)
  assert_eq(s.dim, 5)
}

test "free functor: fold preserves hom" {
  let term : @axiom.Free[Int] = @axiom.Op("add", [@axiom.Return(1), @axiom.Return(2)])
  let res = term.fold(fn(x) { x }, fn(name, args) {
    if name == "add" { args[0] + args[1] } else { 0 }
  })
  assert_eq(res, 3)
}

test "flat functor: preserves limit shape" {
  let flat = @axiom.FlatFunctor::make([@axiom.ObjTag("A"), @axiom.ObjTag("B")])
  flat.advance(@axiom.ObjTag("A"), 10)
  flat.advance(@axiom.ObjTag("B"), 20)
  assert_eq(flat.is_flat(), true)
  let vals = @axiom.flat_preserves_limit_example(flat, [@axiom.ObjTag("A"), @axiom.ObjTag("B"), @axiom.ObjTag("C")])
  assert_eq(vals.length(), 3)
  assert_eq(vals[0], Some(10))
  assert_eq(vals[2], None)
}

test "equivalence: triangle identities" {
  let eq = @axiom.Equivalence::make(
    [(@axiom.ObjTag("A"), 1, -1)],
    [(@axiom.ObjTag("B"), 2, -2)],
  )
  assert_eq(eq.check_triangle(), true)
}

test "topos: omega algebra" {
  assert_eq(@axiom.omega_and(@axiom.True, @axiom.True), @axiom.True)
  assert_eq(@axiom.omega_and(@axiom.True, @axiom.False), @axiom.False)
  assert_eq(@axiom.omega_implies(@axiom.True, @axiom.False), @axiom.False)
  assert_eq(@axiom.omega_or(@axiom.False, @axiom.False), @axiom.False)
}

test "groupoid: connectivity" {
  let g = @axiom.Groupoid::pair_groupoid(["a", "b", "c"])
  assert_eq(g.is_groupoid(), true)
  let comps = g.connected_components()
  assert_eq(comps.length(), 1)
  assert_eq(comps[0].length(), 3)
  let d = @axiom.Groupoid::discrete(["a", "b"])
  assert_eq(d.connected_components().length(), 2)
}

test "2-group: crossed module" {
  let cm = @axiom.CrossedModule::trivial(2, 4)
  assert_eq(cm.check_peiffer(), true)
  // π0 = |G|/|Im∂| =4/1=4, π1=|Ker∂|=2
  assert_eq(cm.pi0(), 4)
  assert_eq(cm.pi1(), 2)
}

test "linear logic: lolli compose" {
  let f = @axiom.Lolli::make(fn(x : Int) -> Int { x + 1 })
  let g = @axiom.Lolli::make(fn(x : Int) -> Int { x * 2 })
  let h = @axiom.compose_lolli(f, g)
  let lin = @axiom.Linear::make(5)
  let res = h.apply(lin).consume()
  assert_eq(res, 12) // (5+1)*2
}

test "homotopy: simplex and euler" {
  let s = @axiom.SSet::standard_simplex(2)
  assert_eq(s.num_simplices(0), 3)
  assert_eq(s.num_simplices(1), 3)
  assert_eq(s.num_simplices(2), 1)
  let cot = @axiom.cotangent_of_poly(3)
  assert_eq(cot.euler(), 3)
}

test "algorithms: fused chain equals naive" {
  let field = @axiom.DoubleField::{}
  let v = @axiom.Vect::from_array([1.0, 2.0])
  let m1 = @axiom.LinMap::identity(2, 0.0, 1.0)
  let m2 = @axiom.LinMap::identity(2, 0.0, 1.0)
  let r1 = @axiom.fused_chain_double([m1, m2], v, field)
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
  let p = @axiom.refl(42)
  let q = @axiom.sym(p)
  let r = @axiom.trans(p, q)
  assert_eq(p.code, 0)
  assert_eq(r.code, 1)
  let f = fn(x : Int) -> Int { x + 1 }
  let ap_p = @axiom.ap(f, p)
  assert_eq(ap_p.code, 0)
}

test "hott: equiv and ua (定理化：ua 不再是公理)" {
  let e = @axiom.Equiv::make(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x })
  assert_eq(e.is_equiv(), true)
  let tagA = @axiom.TypeTag("A")
  let tagB = @axiom.TypeTag("B")
  let pathAB = @axiom.ua(e, tagA, tagB)
  // 舊實作憑空加了常數 10（公理）；現在 code = 等價自身的虧損碼，已驗證等價 ⇒ 0（原子路徑）
  assert_eq(pathAB.code, @axiom.equiv_defect(e))
  assert_eq(pathAB.code, 0)
  // uaη：ua(idToEquiv(refl A)) 結構上就是 refl A
  assert_true(@axiom.ua_eta_legacy(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x }, tagA))
  // uaβ：transport along ua(e) 定義上就是 e.to（glue 消除規則），見證為 refl
  let beta = @axiom.ua_beta(e, tagA, tagB, 7)
  assert_eq(beta.lhs, 7)
  assert_eq(beta.rhs, 7)
  assert_eq(beta.code, 0)
  // 虧損非 0 的「假等價」不會被當成合法路徑（code > 0 可被檢測出來）
  let bad : @axiom.Equiv[Int, Int] = { to: fn(x) { x }, from: fn(x) { x }, left_inv_code: 3, right_inv_code: 4 }
  assert_eq(@axiom.ua(bad, tagA, tagB).code, 7)
  assert_eq(@axiom.ua_beta(bad, tagA, tagB, 1).code, 7)
  // 完整的窮盡證明見 univalence_theorem_test.mbt
  assert_eq(@axiom.univalence_axiom_count(), 0)
  assert_true(@axiom.univalence_holds(3))
}

test "hott: hlevel" {
  let l = @axiom.hlevel_up(@axiom.SetLevel)
  assert_eq(l, @axiom.GroupoidLevel)
  let c = @axiom.trunc_make(42, @axiom.SetLevel)
  assert_eq(@axiom.is_truncated(c, @axiom.SetLevel), true)
}

test "hott: hits circle" {
  let base = @axiom.Circle::base()
  let my_loop = @axiom.circle_loop()
  assert_eq(my_loop.code, 1)
  let s1_rec = @axiom.circle_rec(0, @axiom.refl(0))
  assert_eq(s1_rec(base), 0)
  let enc = @axiom.encode_s1(my_loop)
  assert_eq(enc, 1)
  let dec = @axiom.decode_s1(5)
  assert_eq(dec.code, 5)
}

test "hott: new theorems pi1" {
  assert_eq(@axiom.pi1_s1_is_int(), true)
  assert_eq(@axiom.synthetic_pi(1, 1), "ℤ")
  assert_eq(@axiom.blakers_massey_connectivity(2, 3), 5)
  assert_eq(@axiom.whitehead_principle(true), true)
}

test "hott: algorithms" {
  let p = @axiom.refl(@axiom.TypeTag("X"))
  assert_eq(@axiom.cubical_transport(p, 99), 99)
  assert_eq(@axiom.truncated_exists_search([1, 2, 3], fn(x) { x == 2 }), true)
  let t1 = @axiom.Term::{ code: 1001, tag: "t" }
  let t2 = @axiom.Term::{ code: 1, tag: "t" }
  // 誠實化後：`Term` 無內部結構 ⇒ `normalize` 為恒等，1001 與 1 不再被誤判為相等
  // （舊版 `code % 1000` 會回傳 true；真正的 NBE 見 cubical_test.mbt 的 K3）
  assert_eq(@axiom.judgmental_eq(t1, t2), false)
  assert_eq(@axiom.judgmental_eq(t1, t1), true)
  assert_eq(@axiom.normalize(t1), t1)
  // H1 的真正版本：Kan 填充把 1 沿 3-循環的 glue 送到 2
  assert_eq(@axiom.cubical_kan_demo(), "2")
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
