/// @file homotopy.mbt
/// # 同倫代數 & 導出代數幾何

pub(all) struct Simplex { dim : Int } derive(Eq, Debug)

pub(all) enum SimplicialOp {
  Face(Int)
  Degeneracy(Int)
} derive(Debug)

pub(all) struct SSet { simplices : Array[Array[Int]] }

pub fn SSet::empty() -> SSet { { simplices: [] } }

pub fn SSet::standard_simplex(n : Int) -> SSet {
  let levels : Array[Array[Int]] = []
  let mut k = 0
  while k <= n {
    let cnt = binomial(n + 1, k + 1)
    let arr : Array[Int] = []
    let mut i = 0
    while i < cnt { arr.push(i); i = i + 1 }
    levels.push(arr)
    k = k + 1
  }
  { simplices: levels }
}

fn binomial(n : Int, k : Int) -> Int {
  if k < 0 || k > n { return 0 }
  if k == 0 || k == n { return 1 }
  let mut res = 1
  let mut i = 0
  while i < k {
    res = res * (n - i) / (i + 1)
    i = i + 1
  }
  res
}

pub fn SSet::num_simplices(self : SSet, dim : Int) -> Int {
  if dim < 0 || dim >= self.simplices.length() { 0 } else { self.simplices[dim].length() }
}

pub(all) enum ModelLabel {
  WeakEquiv
  Cofibration
  Fibration
  TrivCof
  TrivFib
  Any
} derive(Eq, Debug)

pub(all) struct ModelCat {
  weaks : Array[(Int, Int)]
  cofs : Array[(Int, Int)]
  fibs : Array[(Int, Int)]
}

pub fn ModelCat::is_weak_equiv(self : ModelCat, f : (Int, Int)) -> Bool {
  for w in self.weaks { if w == f { return true } }
  false
}

pub fn two_of_three(
  weaks : Array[(Int, Int)],
  f : (Int, Int),
  g : (Int, Int),
  comp : (Int, Int)
) -> Bool {
  let wf = contains_pair(weaks, f)
  let wg = contains_pair(weaks, g)
  let wc = contains_pair(weaks, comp)
  let cnt = (if wf { 1 } else { 0 }) + (if wg { 1 } else { 0 }) + (if wc { 1 } else { 0 })
  cnt != 2 || (wf && wg && wc)
}

fn contains_pair(arr : Array[(Int, Int)], x : (Int, Int)) -> Bool {
  for y in arr { if y == x { return true } }
  false
}

pub(all) struct HomotopyGroup { n : Int; rank : Int }

pub fn pi_n(s : SSet, n : Int) -> HomotopyGroup {
  let e = euler_characteristic(s)
  { n, rank: if n == 0 { s.num_simplices(0) } else { e % (n + 2) } }
}

fn euler_characteristic(s : SSet) -> Int {
  let mut chi = 0
  let mut d = 0
  while d < s.simplices.length() {
    let c = s.simplices[d].length()
    if d % 2 == 0 { chi = chi + c } else { chi = chi - c }
    d = d + 1
  }
  chi
}

pub(all) struct AnimatedRing {
  base : String
  trunc : Int
  levels : Array[Int]
}

pub fn AnimatedRing::polynomial(base : String, vars : Int) -> AnimatedRing {
  { base, trunc: 0, levels: [vars] }
}

pub fn AnimatedRing::tensor_product(a : AnimatedRing, b : AnimatedRing) -> AnimatedRing {
  let m = if a.levels.length() > b.levels.length() { a.levels.length() } else { b.levels.length() }
  let lv : Array[Int] = []
  let mut i = 0
  while i < m {
    let av = if i < a.levels.length() { a.levels[i] } else { 0 }
    let bv = if i < b.levels.length() { b.levels[i] } else { 0 }
    lv.push(av + bv)
    i = i + 1
  }
  { base: a.base + "⊗^L" + b.base, trunc: max_int(a.trunc, b.trunc), levels: lv }
}

fn max_int(a : Int, b : Int) -> Int { if a > b { a } else { b } }

pub(all) struct CotangentComplex {
  ring : AnimatedRing
  betti : Array[Int]
}

pub fn cotangent_of_poly(vars : Int) -> CotangentComplex {
  { ring: AnimatedRing::polynomial("k", vars), betti: [vars] }
}

pub fn CotangentComplex::euler(self : CotangentComplex) -> Int {
  let mut s = 0
  let mut i = 0
  while i < self.betti.length() {
    if i % 2 == 0 { s = s + self.betti[i] } else { s = s - self.betti[i] }
    i = i + 1
  }
  s
}

pub fn deformation_obstruction(cot : CotangentComplex) -> String {
  let e = cot.euler()
  if e == 0 { "unobstructed (光滑)" } else { "obstruction rank " + e.to_string() }
}

pub fn hocolim_via_replacement(s : SSet) -> SSet {
  let new_levels : Array[Array[Int]] = []
  for lvl in s.simplices {
    let nl : Array[Int] = []
    for x in lvl { nl.push(x); nl.push(x + 1000) }
    new_levels.push(nl)
  }
  { simplices: new_levels }
}
