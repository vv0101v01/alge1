///|
/// @file structures_test.mbt
/// # 原有數學結構的黑盒測試（範疇/函子/Vectₖ/Topos/線性邏輯/同倫/群胚/A1-A10）
///
/// 對應 package `axiom/axiom/structures`。白盒不變量測試見 `structures_wbtest.mbt`。

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
