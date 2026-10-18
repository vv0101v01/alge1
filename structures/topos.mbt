/// @file topos.mbt
/// # Top / Topos — 空間與層
///
/// Top: 對象 (X,τ), 態射連續映射
/// Topos: 有限極限 + 指數 + Ω

pub(all) struct Topology {
  points : Array[String]
  opens : Array[Array[String]]
}

pub fn Topology::discrete(points : Array[String]) -> Topology {
  let opens : Array[Array[String]] = [[]]
  for p in points { opens.push([p]) }
  opens.push(points)
  { points, opens }
}

pub fn Topology::indiscrete(points : Array[String]) -> Topology {
  { points, opens: [[], points] }
}

pub fn Topology::is_open(self : Topology, s : Array[String]) -> Bool {
  for o in self.opens { if arrays_equal(o, s) { return true } }
  false
}

fn arrays_equal(a : Array[String], b : Array[String]) -> Bool {
  if a.length() != b.length() { return false }
  let mut i = 0
  while i < a.length() {
    if a[i] != b[i] { return false }
    i = i + 1
  }
  true
}

pub(all) struct ContinuousMap {
  domain : Topology
  codomain : Topology
  mapping : Map[String, String]
}

pub fn ContinuousMap::is_continuous(self : ContinuousMap) -> Bool {
  for v_open in self.codomain.opens {
    let pre : Array[String] = []
    for p in self.domain.points {
      match self.mapping.get(p) {
        Some(qv) => { for x in v_open { if x == qv { pre.push(p) } } }
        None => ()
      }
    }
    if !self.domain.is_open(pre) { return false }
  }
  true
}

pub fn contractible_reduction(topo : Topology) -> Topology {
  if topo.points.length() <= 1 { topo } else { Topology::indiscrete(["⋆"]) }
}

// Sheaf part
pub(all) struct Site {
  pub objects : Array[ObjTag]
  pub covers : Map[String, Array[Array[ObjTag]]]
}

pub fn Site::make(objects : Array[ObjTag]) -> Site {
  let covers : Map[String, Array[Array[ObjTag]]] = Map::new()
  { objects, covers }
}

pub(all) struct Sheaf[F] {
  site : Site
  functor : F
  gluing_witness : Array[Bool]
}

pub fn[F] Sheaf::make(site : Site, functor : F) -> Sheaf[F] {
  { site, functor, gluing_witness: [] }
}

pub(all) enum Omega {
  False
  True
} derive(Eq, Debug)

pub fn omega_and(a : Omega, b : Omega) -> Omega {
  match (a, b) { (True, True) => True; _ => False }
}

pub fn omega_or(a : Omega, b : Omega) -> Omega {
  match (a, b) { (False, False) => False; _ => True }
}

pub fn omega_implies(a : Omega, b : Omega) -> Omega {
  match (a, b) { (True, False) => False; _ => True }
}

pub fn[S] characteristic(_set : Array[S], pred : (S) -> Bool, x : S) -> Omega {
  if pred(x) { True } else { False }
}

pub fn[A] power_object(a : Array[A]) -> Array[Array[A]] { [[], a] }

pub(all) struct Presheaf[P] { data : P }

pub fn[P] sheafify(psh : Presheaf[P]) -> Presheaf[P] { psh }

pub(all) struct GeometricMorphism[FStar, FStar2] {
  inverse_image : FStar
  direct_image : FStar2
}

pub fn mitchell_benabou_eval(formula : Omega, _ctx : Map[String, Omega]) -> Omega { formula }
