/// Whitebox tests — validate internal invariants

test "free rewrite batch shares" {
  let terms : Array[Free[Int]] = [Return(1), Op("f", [Return(1)]), Return(1)]
  let out = free_rewrite_batch(terms, fn(t) { t })
  assert_eq(out.length(), 3)
}

test "sliding flat" {
  let flat = FlatFunctor::make([ObjTag("A")])
  let stream : Array[(ObjTag, Int)] = [(ObjTag("A"), 1), (ObjTag("B"), 2), (ObjTag("A"), 3)]
  let res = sliding_flat_eval(flat, stream, 2)
  assert_eq(res.length(), 3)
}

test "sheaf query" {
  let site = Site::make([ObjTag("U")])
  let r = sheaf_query_optimized(site, ObjTag("U"), [[ObjTag("U")]])
  assert_true(r)
}

test "hocolim" {
  let s = SSet::empty()
  let t = hocolim_parallel(s, 1)
  assert_eq(t.simplices.length(), 0)
}

test "orbit reduction" {
  let cm = CrossedModule::trivial(2, 2)
  let elems : Array[TwoGroupElem] = [{ g: 0, h: 0 }, { g: 1, h: 1 }]
  let n = two_group_orbit_count(cm, elems)
  assert_true(n >= 1)
}

test "tensor_2group" {
  let cm = CrossedModule::trivial(4, 4)
  let a = { g: 1, h: 2 }
  let b = { g: 2, h: 1 }
  let c = tensor_2group(a, b, cm)
  assert_eq(c.g, 3)
}
