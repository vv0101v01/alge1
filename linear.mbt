/// @file linear.mbt
/// # 線性邏輯 — 資源敏感
///
/// A⊗B, A⊸B, A&B, A⊕B, !A, ?A
/// Girard: A→B = !A ⊸ B

pub(all) struct Linear[X] {
  val : X
  mut consumed : Bool
}

pub fn[X] Linear::make(x : X) -> Linear[X] { { val: x, consumed: false } }

pub fn[X] Linear::consume(self : Linear[X]) -> X {
  if self.consumed { panic() }
  self.consumed = true
  self.val
}

// Ensure linear consumption is compile-time checked in real usage;
// this runtime panic is only fallback for dynamic cases

pub(all) struct Lolli[A, B] { func : (A) -> B }

pub fn[A, B] Lolli::make(f : (A) -> B) -> Lolli[A, B] { { func: f } }

pub fn[A, B] Lolli::apply(self : Lolli[A, B], x : Linear[A]) -> Linear[B] {
  Linear::make((self.func)(x.consume()))
}

pub(all) struct Tensor[A, B] {
  left : A
  right : B
}

pub fn[A, B] Tensor::make(a : A, b : B) -> Tensor[A, B] { { left: a, right: b } }

pub fn[A, B] Tensor::split(self : Tensor[A, B]) -> (A, B) { (self.left, self.right) }

pub(all) enum With[A, B] {
  Fst(A)
  Snd(B)
} derive(Debug)

pub(all) enum Plus[A, B] {
  Inl(A)
  Inr(B)
} derive(Debug)

pub(all) struct Bang[A] { val : A }

pub fn[A] Bang::make(x : A) -> Bang[A] { { val: x } }

pub fn[A] Bang::derelict(self : Bang[A]) -> A { self.val }

pub fn[A] Bang::duplicate(self : Bang[A]) -> Tensor[Bang[A], Bang[A]] {
  Tensor::make(Bang::make(self.val), Bang::make(self.val))
}

pub trait Clone {
  fn clone(Self) -> Self
}

impl Clone for Int with fn clone(self : Int) -> Int { self }
impl Clone for String with fn clone(self : String) -> String { self }
impl Clone for Double with fn clone(self : Double) -> Double { self }

pub(all) struct Dual[A] { lolli : Lolli[A, Unit] }

pub fn[A, B, C] compose_lolli(f : Lolli[A, B], g : Lolli[B, C]) -> Lolli[A, C] {
  Lolli::make(fn(x) { (g.func)((f.func)(x)) })
}

pub fn[A] linear_batch(arr : Array[Linear[A]]) -> Array[A] {
  let out : Array[A] = []
  for lin in arr { out.push(lin.consume()) }
  out
}

pub(all) struct ProofNet {
  nodes : Array[String]
  axiom_links : Array[(Int, Int)]
}

pub fn ProofNet::is_correct(self : ProofNet) -> Bool {
  for (a, b) in self.axiom_links { if a == b { return false } }
  true
}
