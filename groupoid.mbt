/// @file groupoid.mbt
/// # 群胚 & 2-群

pub(all) struct Morph {
  src : String
  dst : String
  label : String
  inv_label : String
} derive(Eq, Debug)

pub(all) struct Groupoid {
  objects : Array[String]
  morphs : Array[Morph]
}

pub fn Groupoid::discrete(objs : Array[String]) -> Groupoid {
  let ms : Array[Morph] = []
  for o in objs { ms.push({ src: o, dst: o, label: "id_" + o, inv_label: "id_" + o }) }
  { objects: objs, morphs: ms }
}

pub fn Groupoid::pair_groupoid(objs : Array[String]) -> Groupoid {
  let ms : Array[Morph] = []
  for a in objs {
    for b in objs { ms.push({ src: a, dst: b, label: a + "→" + b, inv_label: b + "→" + a }) }
  }
  { objects: objs, morphs: ms }
}

pub fn Groupoid::is_groupoid(self : Groupoid) -> Bool {
  for m in self.morphs {
    let mut has_inv = false
    for n in self.morphs {
      if n.src == m.dst && n.dst == m.src && n.label == m.inv_label { has_inv = true }
    }
    if !has_inv { return false }
  }
  true
}

pub fn Groupoid::connected_components(self : Groupoid) -> Array[Array[String]] {
  let parent : Map[String, String] = Map::new()
  for o in self.objects { parent[o] = o }
  fn find(x : String, parent : Map[String, String]) -> String {
    match parent.get(x) {
      Some(v) => if v == x { x } else { let r = find(v, parent); parent[x] = r; r }
      None => x
    }
  }
  for m in self.morphs {
    let ra = find(m.src, parent)
    let rb = find(m.dst, parent)
    if ra != rb { parent[ra] = rb }
  }
  let comps : Map[String, Array[String]] = Map::new()
  for o in self.objects {
    let r = find(o, parent)
    match comps.get(r) {
      Some(arr) => arr.push(o)
      None => comps[r] = [o]
    }
  }
  let out : Array[Array[String]] = []
  for (_, v) in comps { out.push(v) }
  out
}

pub fn compose_paths(a : Morph, b : Morph) -> Morph? {
  if a.dst != b.src { None } else { Some({ src: a.src, dst: b.dst, label: a.label + "·" + b.label, inv_label: b.inv_label + "·" + a.inv_label }) }
}

pub(all) struct CrossedModule {
  h_order : Int
  g_order : Int
  boundary : Array[Int]
  action : Array[Array[Int]]
}

pub fn CrossedModule::trivial(h : Int, g : Int) -> CrossedModule {
  let b : Array[Int] = []
  let mut i = 0
  while i < h { b.push(0); i = i + 1 }
  let act : Array[Array[Int]] = []
  let mut gi = 0
  while gi < g {
    let row : Array[Int] = []
    let mut hi = 0
    while hi < h { row.push(hi); hi = hi + 1 }
    act.push(row)
    gi = gi + 1
  }
  { h_order: h, g_order: g, boundary: b, action: act }
}

pub fn CrossedModule::check_peiffer(self : CrossedModule) -> Bool {
  for gi in 0..<self.g_order {
    for hi in 0..<self.h_order {
      let acted = self.action[gi][hi]
      let lhs = self.boundary[acted]
      let rhs = self.boundary[hi]
      if lhs != rhs { return false }
    }
  }
  true
}

pub fn CrossedModule::pi0(self : CrossedModule) -> Int {
  let seen : Map[Int, Bool] = Map::new()
  let mut im_size = 0
  for v in self.boundary {
    match seen.get(v) {
      Some(_) => ()
      None => { seen[v] = true; im_size = im_size + 1 }
    }
  }
  if im_size == 0 { self.g_order } else { self.g_order / im_size }
}

pub fn CrossedModule::pi1(self : CrossedModule) -> Int {
  let mut ker = 0
  for v in self.boundary { if v == 0 { ker = ker + 1 } }
  ker
}

pub(all) struct TwoGroupElem { g : Int; h : Int }

pub fn tensor_2group(a : TwoGroupElem, b : TwoGroupElem, cm : CrossedModule) -> TwoGroupElem {
  let g = (a.g + b.g) % cm.g_order
  let acted = cm.action[a.g % cm.g_order][b.h % cm.h_order]
  let h = (a.h + acted) % cm.h_order
  { g, h }
}

fn max_int2(a : Int, b : Int) -> Int { if a > b { a } else { b } }

pub fn orbit_reduction(cm : CrossedModule, states : Array[TwoGroupElem]) -> Map[String, Array[TwoGroupElem]] {
  let orbits : Map[String, Array[TwoGroupElem]] = Map::new()
  for s in states {
    let key = (s.g % cm.pi0()).to_string() + ":" + (s.h % max_int2(1, cm.pi1())).to_string()
    match orbits.get(key) {
      Some(arr) => arr.push(s)
      None => orbits[key] = [s]
    }
  }
  orbits
}

pub(all) struct GroupoidCache[V] {
  store : Map[String, V]
  groupoid : Groupoid
}

pub fn[V] GroupoidCache::make(g : Groupoid) -> GroupoidCache[V] { { store: Map::new(), groupoid: g } }

pub fn[V] GroupoidCache::canonical_key(self : GroupoidCache[V], obj : String) -> String {
  for comp in self.groupoid.connected_components() {
    for x in comp { if x == obj { return comp[0] } }
  }
  obj
}
