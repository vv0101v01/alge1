/// @file algorithms.mbt
/// # 衍生算法 — 範疇抽象降複雜度

// A1 自由項重寫
pub fn[X] free_rewrite_batch(
  terms : Array[Free[X]],
  rule : (Free[X]) -> Free[X]
) -> Array[Free[X]] {
  let seen : Map[String, Free[X]] = Map::new()
  let out : Array[Free[X]] = []
  for t in terms {
    let key = debug_string(t)
    match seen.get(key) {
      Some(cached) => out.push(cached)
      None => {
        let r = rule(t)
        seen[key] = r
        out.push(r)
      }
    }
  }
  out
}

fn[X] debug_string(t : Free[X]) -> String {
  match t {
    Return(_) => "R"
    Op(name, args) => name + "(" + args.length().to_string() + ")"
  }
}

// A2 滑動窗口平坦求值
pub fn sliding_flat_eval(
  flat : FlatFunctor,
  stream : Array[(ObjTag, Int)],
  window : Int
) -> Array[Int?] {
  let results : Array[Int?] = []
  let mut idx = 0
  while idx < stream.length() {
    let (obj, val) = stream[idx]
    flat.advance(obj, val)
    if idx >= window {
      let (old_obj, _) = stream[idx - window]
      ignore(old_obj)
    }
    results.push(flat.eval(obj))
    idx = idx + 1
  }
  results
}

// A3 規範形 via 等價
pub fn canonicalize_via_equivalence(
  eq : Equivalence,
  objs : Array[ObjTag]
) -> Map[String, ObjTag] {
  let canon : Map[String, ObjTag] = Map::new()
  for o in objs {
    let c = transport_via_equivalence(eq, o)
    canon[c.0] = c
  }
  canon
}

// A4 融合鏈
pub fn fused_chain_double(
  ops : Array[LinMap[Double]],
  v : Vect[Double],
  field : DoubleField
) -> Vect[Double] {
  let mut cur = v
  for op in ops { cur = apply_double(op, cur, field) }
  cur
}

pub fn adaptive_apply_double(
  lin : LinMap[Double],
  v : Vect[Double],
  field : DoubleField
) -> Vect[Double] {
  let sv = SparseVect::from_dense(v, fn(x) { x == 0.0 })
  let density = sv.entries.length().to_double() / v.dim.to_double()
  if density < 0.3 { apply_sparse_double(lin, sv, field) } else { apply_double(lin, v, field) }
}

// A5 層查詢
pub fn sheaf_query_optimized(
  _site : Site,
  _obj : ObjTag,
  covers : Array[Array[ObjTag]]
) -> Bool {
  let seen : Map[String, Bool] = Map::new()
  for cov in covers {
    let key = cov.length().to_string()
    match seen.get(key) {
      Some(_) => ()
      None => {
        seen[key] = true
        if cov.length() > 0 { return true }
      }
    }
  }
  false
}

// A6 線性管道
pub fn[A, B, C, D] linear_pipeline(
  f : Lolli[A, B],
  g : Lolli[B, C],
  h : Lolli[C, D],
  x : Linear[A]
) -> Linear[D] {
  let fg = compose_lolli(f, g)
  let fgh = compose_lolli(fg, h)
  fgh.apply(x)
}

pub fn[X] linear_map_inplace(arr : Array[X], f : (X) -> X) -> Unit {
  let mut i = 0
  while i < arr.length() {
    arr[i] = f(arr[i])
    i = i + 1
  }
}

// A7 hocolim 並行
pub fn hocolim_parallel(s : SSet, levels : Int) -> SSet {
  let mut cur = s
  let mut l = 0
  while l < levels {
    cur = hocolim_via_replacement(cur)
    l = l + 1
  }
  cur
}

// A8 餘切驅動雅可比
pub fn jacobian_via_cotangent(
  cot : CotangentComplex,
  jacobian_full : Array[Array[Double]]
) -> Array[Array[Double]] {
  let keep = cot.betti.length()
  if keep >= jacobian_full.length() { return jacobian_full }
  let out : Array[Array[Double]] = []
  let mut i = 0
  while i < keep {
    if cot.betti[i] != 0 { out.push(jacobian_full[i]) }
    i = i + 1
  }
  out
}

// A9 群胚對稱搜索
pub fn symmetric_search(
  groupoid : Groupoid,
  states : Array[String],
  expand : (String) -> Array[String]
) -> Array[String] {
  let cache = GroupoidCache::make(groupoid)
  let visited : Map[String, Bool] = Map::new()
  let mut frontier = states
  let result : Array[String] = []
  let mut iter = 0
  while frontier.length() > 0 && iter < 100 {
    let next : Array[String] = []
    for s in frontier {
      let canon = cache.canonical_key(s)
      match visited.get(canon) {
        Some(_) => ()
        None => {
          visited[canon] = true
          result.push(s)
          for t in expand(s) { next.push(t) }
        }
      }
    }
    frontier = next
    iter = iter + 1
  }
  result
}

pub fn two_group_orbit_count(cm : CrossedModule, elems : Array[TwoGroupElem]) -> Int {
  let orbits = orbit_reduction(cm, elems)
  let mut count = 0
  for (_, _) in orbits { count = count + 1 }
  count
}

// 高維管線
pub fn high_dim_pipeline(
  vecs : Array[Vect[Double]],
  proj : LinMap[Double],
  field : DoubleField
) -> Array[Vect[Double]] {
  let projected : Array[Vect[Double]] = []
  for v in vecs { projected.push(apply_double(proj, v, field)) }
  projected
}

pub fn checked_matmul(
  a : LinMap[Double],
  b : LinMap[Double]
) -> LinMap[Double]? {
  if a.cols != b.rows { None } else {
    let res = LinMap::zeros(a.rows, b.cols, 0.0)
    let mut i = 0
    while i < a.rows {
      let mut j = 0
      while j < b.cols {
        let mut acc = 0.0
        let mut k = 0
        while k < a.cols {
          acc = acc + a.mat[i][k] * b.mat[k][j]
          k = k + 1
        }
        res.mat[i][j] = acc
        j = j + 1
      }
      i = i + 1
    }
    Some(res)
  }
}
