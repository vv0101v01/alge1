/// @file vect.mbt
/// # Vect_k — k-向量空間範疇與零成本線性代數
///
/// 定義：Vect_k 對象為 k-向量空間，態射線性映射
/// 結構：(⊗, k) 單子範疇，直和 ⊕ 雙積，Hom(V,W) ≅ V*⊗W

pub(open) trait FieldOps {
  fn f_zero(Self) -> Double
  fn f_one(Self) -> Double
  fn f_add(Self, Double, Double) -> Double
  fn f_sub(Self, Double, Double) -> Double
  fn f_mul(Self, Double, Double) -> Double
  fn f_div(Self, Double, Double) -> Double
  fn f_neg(Self, Double) -> Double
  fn f_eq(Self, Double, Double) -> Bool
}

pub(all) struct DoubleField {}

impl FieldOps for DoubleField with fn f_zero(self : DoubleField) -> Double { 0.0 }
impl FieldOps for DoubleField with fn f_one(self : DoubleField) -> Double { 1.0 }
impl FieldOps for DoubleField with fn f_add(self : DoubleField, a : Double, b : Double) -> Double { a + b }
impl FieldOps for DoubleField with fn f_sub(self : DoubleField, a : Double, b : Double) -> Double { a - b }
impl FieldOps for DoubleField with fn f_mul(self : DoubleField, a : Double, b : Double) -> Double { a * b }
impl FieldOps for DoubleField with fn f_div(self : DoubleField, a : Double, b : Double) -> Double { a / b }
impl FieldOps for DoubleField with fn f_neg(self : DoubleField, a : Double) -> Double { 0.0 - a }
impl FieldOps for DoubleField with fn f_eq(self : DoubleField, a : Double, b : Double) -> Bool { a == b }

pub(all) struct IntModField { modulus : Int }

pub fn IntModField::make(m : Int) -> IntModField { { modulus: m } }

pub(all) struct Vect[K] {
  dim : Int
  data : Array[K]
} derive(Debug)

pub fn[K] Vect::zeros(dim : Int, zero : K) -> Vect[K] {
  Vect::{ dim, data: Array::make(dim, zero) }
}

pub fn[K] Vect::from_array(arr : Array[K]) -> Vect[K] {
  Vect::{ dim: arr.length(), data: arr }
}

pub(all) struct SparseVect[K] {
  dim : Int
  entries : Array[(Int, K)]
}

pub fn[K] SparseVect::from_dense(v : Vect[K], is_zero : (K) -> Bool) -> SparseVect[K] {
  let es : Array[(Int, K)] = []
  let mut i = 0
  while i < v.data.length() {
    if !is_zero(v.data[i]) { es.push((i, v.data[i])) }
    i = i + 1
  }
  { dim: v.dim, entries: es }
}

pub fn[K] SparseVect::to_dense(self : SparseVect[K], zero : K) -> Vect[K] {
  let arr = Array::make(self.dim, zero)
  for (idx, val) in self.entries { arr[idx] = val }
  Vect::{ dim: self.dim, data: arr }
}

pub(all) struct LinMap[K] {
  rows : Int
  cols : Int
  mat : Array[Array[K]]
}

pub fn[K] LinMap::zeros(rows : Int, cols : Int, zero : K) -> LinMap[K] {
  let m : Array[Array[K]] = []
  let mut i = 0
  while i < rows {
    m.push(Array::make(cols, zero))
    i = i + 1
  }
  { rows, cols, mat: m }
}

pub fn[K] LinMap::identity(n : Int, zero : K, one : K) -> LinMap[K] {
  let m = LinMap::zeros(n, n, zero)
  let mut i = 0
  while i < n {
    m.mat[i][i] = one
    i = i + 1
  }
  m
}

// 稠密矩陣-向量乘 O(n·m)
pub fn apply_double(lin : LinMap[Double], v : Vect[Double], field : DoubleField) -> Vect[Double] {
  assert_eq(lin.cols, v.dim)
  let res = Vect::zeros(lin.rows, FieldOps::f_zero(field))
  let mut i = 0
  while i < lin.rows {
    let mut acc = FieldOps::f_zero(field)
    let mut j = 0
    while j < lin.cols {
      acc = FieldOps::f_add(field, acc, FieldOps::f_mul(field, lin.mat[i][j], v.data[j]))
      j = j + 1
    }
    res.data[i] = acc
    i = i + 1
  }
  res
}

// 稀疏加速
pub fn apply_sparse_double(
  lin : LinMap[Double],
  sv : SparseVect[Double],
  field : DoubleField
) -> Vect[Double] {
  let res = Vect::zeros(lin.rows, FieldOps::f_zero(field))
  let mut i = 0
  while i < lin.rows {
    let mut acc = FieldOps::f_zero(field)
    for (j, val) in sv.entries {
      acc = FieldOps::f_add(field, acc, FieldOps::f_mul(field, lin.mat[i][j], val))
    }
    res.data[i] = acc
    i = i + 1
  }
  res
}

fn assert_eq(a : Int, b : Int) -> Unit {
  if a != b { panic() }
}

// 張量積 dim = dimV*dimW
pub fn tensor_double(v : Vect[Double], w : Vect[Double], field : DoubleField) -> Vect[Double] {
  let n = v.dim * w.dim
  let data : Array[Double] = []
  for x in v.data {
    for y in w.data { data.push(FieldOps::f_mul(field, x, y)) }
  }
  Vect::{ dim: n, data }
}

pub fn[K] direct_sum(a : Vect[K], b : Vect[K]) -> Vect[K] {
  Vect::{ dim: a.dim + b.dim, data: concat_free(a.data, b.data) }
}

pub fn pairing_double(cov : Vect[Double], v : Vect[Double], field : DoubleField) -> Double {
  assert_eq(cov.dim, v.dim)
  let mut acc = FieldOps::f_zero(field)
  let mut i = 0
  while i < cov.dim {
    acc = FieldOps::f_add(field, acc, FieldOps::f_mul(field, cov.data[i], v.data[i]))
    i = i + 1
  }
  acc
}

// Johnson–Lindenstrauss 隨機投影
pub fn random_projection(dim_in : Int, dim_out : Int, seed : Int) -> LinMap[Double] {
  let m = LinMap::zeros(dim_out, dim_in, 0.0)
  let mut i = 0
  while i < dim_out {
    let mut j = 0
    while j < dim_in {
      let h = ((i * 73856093) ^ (j * 19349663) ^ (seed * 83492791)) % 3
      let v = if h == 0 { 0.0 } else if h == 1 { 1.0 } else { -1.0 }
      let scale = dim_out.to_double().sqrt()
      m.mat[i][j] = v / scale
      j = j + 1
    }
    i = i + 1
  }
  m
}
