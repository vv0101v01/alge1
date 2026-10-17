/// @file functor.mbt
/// # 三大函子：等價 / 自由 / 平坦

// ------------------------------------------------------------
// 等價函子
// ------------------------------------------------------------
pub(all) struct Equivalence {
  // η 與 ε 以互逆整數對模擬
  unit : Array[(ObjTag, Int, Int)]
  counit : Array[(ObjTag, Int, Int)]
}

pub fn Equivalence::make(
  unit : Array[(ObjTag, Int, Int)],
  counit : Array[(ObjTag, Int, Int)]
) -> Equivalence {
  { unit, counit }
}

pub fn Equivalence::check_triangle(self : Equivalence) -> Bool {
  for (_, eta, eta_inv) in self.unit {
    if eta + eta_inv != 0 { return false }
  }
  for (_, eps, eps_inv) in self.counit {
    if eps + eps_inv != 0 { return false }
  }
  true
}

pub fn[X] transport_via_equivalence(_eq : Equivalence, x : X) -> X { x }

// ------------------------------------------------------------
// 自由函子 Free ⊣ Forgetful
// ------------------------------------------------------------
pub(all) enum Free[X] {
  Return(X)
  Op(String, Array[Free[X]])
} derive(Debug)

pub fn[X, A] Free::fold(self : Free[X], ret : (X) -> A, op : (String, Array[A]) -> A) -> A {
  match self {
    Return(x) => ret(x)
    Op(name, args) => {
      let mapped = args.map(fn(a) { a.fold(ret, op) })
      op(name, mapped)
    }
  }
}

pub(all) struct FreeTrie[X] {
  trie : Map[String, Free[X]]
}

pub fn[X] FreeTrie::empty() -> FreeTrie[X] {
  let m : Map[String, Free[X]] = Map::new()
  { trie: m }
}

pub fn[X] FreeTrie::insert(self : FreeTrie[X], key : String, v : Free[X]) -> Unit {
  self.trie[key] = v
}

pub fn[X] FreeTrie::lookup(self : FreeTrie[X], key : String) -> Free[X]? {
  self.trie.get(key)
}

pub fn[X] concat_free(a : Array[X], b : Array[X]) -> Array[X] {
  let res : Array[X] = []
  for x in a { res.push(x) }
  for x in b { res.push(x) }
  res
}

// ------------------------------------------------------------
// 平坦函子 — 保有限極限 = 濾餘極限
// ------------------------------------------------------------
pub(all) struct FlatFunctor {
  active : Array[ObjTag]
  cocone : Map[String, Int]
}

pub fn FlatFunctor::make(active : Array[ObjTag]) -> FlatFunctor {
  let m : Map[String, Int] = Map::new()
  { active, cocone: m }
}

pub fn FlatFunctor::is_flat(self : FlatFunctor) -> Bool { self.active.length() > 0 }

pub fn FlatFunctor::advance(self : FlatFunctor, obj : ObjTag, val : Int) -> Unit {
  let key = obj.0
  self.cocone[key] = val
  let mut found = false
  for a in self.active { if a == obj { found = true } }
  if !found { self.active.push(obj) }
}

pub fn FlatFunctor::eval(self : FlatFunctor, obj : ObjTag) -> Int? {
  self.cocone.get(obj.0)
}

pub fn flat_preserves_limit_example(
  flat : FlatFunctor,
  objs : Array[ObjTag]
) -> Array[Int?] {
  objs.map(fn(o) { flat.eval(o) })
}
