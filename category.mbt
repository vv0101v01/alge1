/// @file category.mbt
/// # 範疇論核心 — Category / Functor / NatTrans
///
/// 定義 1 — 範疇 C : Ob, Hom, id, ∘ 滿足結合與單位
/// 定理 1 — 函子保同構
/// 零成本：以類型 witness + 單態化內聯，無虛表

pub(all) struct ObjTag(String) derive(Eq, Debug)

pub(open) trait Category {
  fn cat_id(Self, ObjTag) -> Int
  fn cat_compose(Self, Int, Int) -> Int
  fn cat_dom(Self, Int) -> ObjTag
  fn cat_cod(Self, Int) -> ObjTag
}

pub(all) struct TerminalCat {}

impl Category for TerminalCat with fn cat_id(self : TerminalCat, _obj : ObjTag) -> Int { 0 }
impl Category for TerminalCat with fn cat_dom(self : TerminalCat, _m : Int) -> ObjTag { ObjTag("⋆") }
impl Category for TerminalCat with fn cat_cod(self : TerminalCat, _m : Int) -> ObjTag { ObjTag("⋆") }
impl Category for TerminalCat with fn cat_compose(self : TerminalCat, _g : Int, _f : Int) -> Int { 0 }

pub(all) struct DiscreteCat {
  objs : Array[ObjTag]
}

pub fn DiscreteCat::make(objs : Array[ObjTag]) -> DiscreteCat { { objs } }

impl Category for DiscreteCat with fn cat_id(self : DiscreteCat, obj : ObjTag) -> Int {
  let mut idx = 0
  while idx < self.objs.length() {
    if self.objs[idx] == obj { return idx }
    idx = idx + 1
  }
  -1
}

impl Category for DiscreteCat with fn cat_compose(self : DiscreteCat, g : Int, f : Int) -> Int {
  if g == f { g } else { -1 }
}

impl Category for DiscreteCat with fn cat_dom(self : DiscreteCat, m : Int) -> ObjTag {
  self.objs[m]
}

impl Category for DiscreteCat with fn cat_cod(self : DiscreteCat, m : Int) -> ObjTag {
  self.objs[m]
}

/// 函子 witness trait — 保恆等與複合
pub(open) trait Functor {
  fn map_obj(Self, ObjTag) -> ObjTag
  fn map_mor(Self, Int) -> Int
}

pub(all) struct IdFunctor {}

impl Functor for IdFunctor with fn map_obj(self : IdFunctor, obj : ObjTag) -> ObjTag { obj }
impl Functor for IdFunctor with fn map_mor(self : IdFunctor, mor : Int) -> Int { mor }

/// 自然變換 α : F ⇒ G  滿足自然性方塊 G(f)∘α_A = α_B∘F(f)
pub(all) struct NatTrans {
  components : Array[(ObjTag, Int)]
}

pub fn NatTrans::make(comps : Array[(ObjTag, Int)]) -> NatTrans { { components: comps } }

pub fn NatTrans::component(self : NatTrans, obj : ObjTag) -> Int? {
  for (o, m) in self.components {
    if o == obj { return Some(m) }
  }
  None
}

pub fn is_natural_square(
  nt : NatTrans,
  f_dom : ObjTag,
  f_cod : ObjTag,
  f_image : Int,
  g_image : Int
) -> Bool {
  match (nt.component(f_dom), nt.component(f_cod)) {
    (Some(aa), Some(bb)) => (g_image + aa) == (bb + f_image)
    _ => false
  }
}

/// Yoneda: Hom(A, -)
pub(all) struct HomFunctor {
  source : ObjTag
}

pub fn HomFunctor::make(source : ObjTag) -> HomFunctor { { source } }

pub fn HomFunctor::hom_set(self : HomFunctor, target : ObjTag) -> Array[Int] {
  if self.source == target { [0] } else { [] }
}
