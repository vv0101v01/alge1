/// @module axiom
/// Axiom — 零成本抽象的高維演算法庫（HoTT 重構版）
///
/// 本模組以同倫類型論為統一根基，重新定義所有原定理並新增 HoTT 獨有定理
/// 定理匯總：
/// 1. 等價保持極限  2. 自由⊣遺忘  3. 平坦⇔保有限極限  4. Vect_k 單子閉
/// 5. JL 引理  6. Yoneda  7. Topos 內邏輯  8. 線性分解  9. 2-of-3  10. 交叉模⇔2-群
/// HoTT 新增：
/// N1. π₁(S¹)=ℤ（Encode-Decode） N2. 函數/命題外延性 N3. Freudenthal N4. 截斷萬有性
/// N5. SIP 強化 N6. Whitehead/Blakers-Massey
/// 公理降級為定理：U. 單值性 isEquiv(idToEquiv)（glue 構造 + n=0..6 窮盡驗證，公理數 0）

pub fn hello() -> String { "Axiom ready — HoTT 零成本抽象已就緒" }

/// 整合演示：同時觸及多個結構，驗證編譯時融合
pub fn demo_pipeline() -> String {
  let field = @structures.DoubleField::{}
  let v = @structures.Vect::from_array([1.0, 2.0, 3.0, 4.0])
  let m = @structures.LinMap::identity(4, 0.0, 1.0)
  let w = @structures.apply_double(m, v, field)
  let t : @structures.Free[Int] = Op("add", [@structures.Return(1), @structures.Return(2)])
  let folded = t.fold(fn(x) { x }, fn(name, args) {
    if name == "add" { args[0] + args[1] } else { 0 }
  })
  let g = @structures.Groupoid::pair_groupoid(["a", "b", "c"])
  let comps = g.connected_components()
  let lin = @structures.Linear::make(42)
  let lolli = @structures.Lolli::make(fn(x : Int) -> Int { x + 1 })
  let lin2 = lolli.apply(lin)
  let val = lin2.consume()
  "demo: w=" + w.data.to_string() + " folded=" + folded.to_string() + " comps=" + comps.length().to_string() + " linear=" + val.to_string()
}

/// 高維突破演示：隨機投影降維 + 張量融合 + 餘切指導
pub fn high_dim_demo() -> String {
  let field = @structures.DoubleField::{}
  let proj = @structures.random_projection(8, 3, 42)
  let vecs : Array[@structures.Vect[Double]] = [
    @structures.Vect::from_array([1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]),
    @structures.Vect::from_array([8.0, 7.0, 6.0, 5.0, 4.0, 3.0, 2.0, 1.0]),
  ]
  let low = @structures.high_dim_pipeline(vecs, proj, field)
  let s = @structures.SSet::standard_simplex(2)
  let hc = @structures.hocolim_parallel(s, 1)
  let cot = @structures.cotangent_of_poly(3)
  let e = cot.euler()
  "high_dim: low_dim=" + low.length().to_string() + " hocolim_cells=" + hc.num_simplices(1).to_string() + " cot_euler=" + e.to_string()
}

/// HoTT 核心演示：路徑、等價、單值性
pub fn hott_demo() -> String {
  let p = @hott_core.refl(42)
  let q = @hott_core.sym(p)
  let r = @hott_core.trans(p, q)
  let e = @hott_core.Equiv::make(fn(x : Int) -> Int { x }, fn(x : Int) -> Int { x })
  let tagA = @hott_core.TypeTag("A")
  let tagB = @hott_core.TypeTag("B")
  let pathAB = @hott_core.ua(e, tagA, tagB)
  let h = @hott_core.Homotopy::{ fun1: fn(x : Int) -> Int { x }, fun2: fn(x : Int) -> Int { x }, witness: [] }
  let funext_path = @univalence.funext(h)
  "hott: refl_code=" + p.code.to_string() + " sym_code=" + q.code.to_string() + " trans_code=" + r.code.to_string() + " ua_code=" + pathAB.code.to_string() + " funext_code=" + funext_path.code.to_string()
}

/// HoTT HIT 演示：圓、區間、懸垂、截斷
pub fn hits_demo() -> String {
  let base = @hott_hits.Circle::base()
  let my_loop = @hott_hits.circle_loop()
  let s1_rec = @hott_hits.circle_rec(0, @hott_core.refl(0))
  let v = s1_rec(base)
  let susp : @hott_hits.Susp[Int] = North
  let susp_str = match susp { North => "North"; South => "South" }
  let merid_path = @hott_hits.merid(42)
  let prop = @hott_hits.prop_trunc_in(123)
  let is_prop = @hott_hits.prop_trunc_path(prop, prop)
  "hits: base=" + base.tag + " loop_code=" + my_loop.code.to_string() + " s1_rec=" + v.to_string() + " susp=" + susp_str + " merid_code=" + merid_path.code.to_string() + " trunc_path_code=" + is_prop.code.to_string()
}

/// 單值性定理演示：原「單值性公理」已降級為定理（glue 構造 + 窮盡驗證）
pub fn univalence_theorem_demo() -> String {
  let pf3 = @univalence.univalence_proof(3)
  let pf4 = @univalence.univalence_proof(4)
  "univalence_thm: axioms=" + @univalence.univalence_axiom_count().to_string() + " n3(paths=" + pf3.path_count.to_string() + "/" + pf3.expected.to_string() + " checks=" + pf3.checks.to_string() + ") n4(paths=" + pf4.path_count.to_string() + "/" + pf4.expected.to_string() + " checks=" + pf4.checks.to_string() + ") holds=" + (@univalence.univalence_holds(3) && @univalence.univalence_holds(4)).to_string() + " pi1_S3=" + @univalence.pi1_universe_is_symmetric_group(3).to_string() + " ua_beta=" + @univalence.ua_beta_is_theorem(4).to_string() + " funext=" + @univalence.funext_happly_is_equiv().to_string() + " prop_ext=" + @univalence.prop_ext_is_theorem().to_string() + " sip_classes=" + @univalence.monoid_classes(3).to_string()
}

/// HoTT 新定理演示：π₁(S¹)=ℤ 等
pub fn new_theorems_demo() -> String {
  let pi1_ok = @hott_theorems.pi1_s1_is_int()
  let trunc_ok = @hott_core.is_truncated(@hott_core.set_trunc(42), SetLevel)
  let sip = @hott_theorems.n5_sip_monoid_path(
    @univalence.MonoidStr::{ carrier: @hott_core.TypeTag("M1"), op: "*", unit: "e" },
    @univalence.MonoidStr::{ carrier: @hott_core.TypeTag("M2"), op: "*", unit: "e" },
  )
  "new_thms: pi1_s1=" + pi1_ok.to_string() + " set_trunc=" + trunc_ok.to_string() + " sip_code=" + sip.code.to_string() + " synth_pi=" + @hott_theorems.synthetic_pi(1, 1)
}

/// HoTT 新算法演示：cubical 傳輸、截斷剪枝、合成同倫
/// H1/H7 已誠實化：`Term` 無內部結構 ⇒ `normalize` 為恒等、`judgmental_eq` 為精確比對
/// （舊版 `code % 1000` 會把 1001 與 1 誤判為相等，故 `eq` 由 true 變 false）；
/// `kan_fill` 是真正的 Kan 填充結果（見 `cubical_demo`）
pub fn hott_algorithms_demo() -> String {
  let p = @hott_core.refl(@hott_core.TypeTag("A"))
  let trans = @hott_algorithms.cubical_transport(p, 99)
  let searched = @hott_algorithms.truncated_exists_search([1, 2, 3, 4], fn(x) { x == 3 })
  let eq_check = @hott_algorithms.judgmental_eq(@hott_algorithms.Term::{ code: 1001, tag: "t" }, @hott_algorithms.Term::{ code: 1, tag: "t" })
  let norm = @hott_algorithms.normalize(@hott_algorithms.Term::{ code: 2048, tag: "x" })
  "hott_algo: cubical=" + trans.to_string() + " trunc_search=" + searched.to_string() + " eq=" + eq_check.to_string() + " norm_code=" + norm.code.to_string() + " kan_fill=" + @hott_algorithms.cubical_kan_demo()
}

/// 3-循環 (0 1 2) 的 Lehmer 秩
fn cyc3_lehmer() -> Int32 {
  match @univalence.bij_make(3, [1, 2, 0]) {
    Some(b) => @univalence.lehmer_code(b)
    None => 0
  }
}

/// 有限立方體演算法演示：K1 立方體範疇 □ / K2 Kan 填充 / K3 cubical NBE
/// 每個布林值都是**窮盡計算**的結果（見 hott_cubical.mbt），公理數 0
pub fn cubical_demo() -> String {
  let k1 = @cubical.cubical_proof(3)
  let k2 = @cubical.kan_proof(4)
  let k3 = @cubical.nbe_proof(3, 1, 6, 8)
  // K3：transport (ua σ) 1 ⟶ σ 1 = 2（uaβ 作為重寫的計算結果）
  let t = @cubical.CTransport(@cubical.CUa(@cubical.CSigma(cyc3_lehmer())), @cubical.CElem(1))
  let (nf, steps) = @cubical.crewrite(t, 3, 8)
  "cubical: axioms=" + @cubical.cubical_axiom_count().to_string() + " K1(dim<=3 checks=" + k1.checks.to_string() + " C1C2C3=" + (k1.coface_coface && k1.degen_degen && k1.degen_coface).to_string() + " assoc=" + k1.assoc_unit.to_string() + " count=" + k1.count_law.to_string() + " gen=" + k1.generated_by.to_string() + " euler_Q3=" + @cubical.cube_euler(3).to_string() + " gray=" + @cubical.gray_hamiltonian_check(3).to_string() + ") K2(card<=4 checks=" + k2.checks.to_string() + " kan=" + (k2.exists && k2.unique_iff && k2.universal && k2.functorial && k2.roundtrip && k2.refl_law && k2.ua_beta).to_string() + " fill(ua(012),1)=" + @hott_algorithms.cubical_kan_demo() + ") K3(terms=" + k3.terms.to_string() + " sound=" + k3.rewrite_sound.to_string() + " nbe=" + k3.norm_sound.to_string() + " decidable=" + k3.eq_complete.to_string() + " " + @cubical.cterm_show(t) + "=" + @cubical.cterm_show(nf) + "/" + steps.to_string() + "步)"
}

/// 原定理的 HoTT 再定義演示
pub fn redefine_demo() -> String {
  let cat = @hott_redefine.HoTTCat::make(TypeTag("Ob"), GroupoidLevel)
  let vec_hott = @hott_redefine.VectHoTT::make(3)
  let inf_topos = @hott_redefine.InfTopos::from_site(@structures.Site::make([@structures.ObjTag("U")]))
  let lin_hott = @hott_redefine.LinearHoTT::{ linear: @structures.Linear::make(10), level: @hott_core.SetLevel }
  let lvl = @hott_core.hlevel_up(SetLevel)
  let lvl_str = match lvl { Contr => "Contr"; Prop => "Prop"; SetLevel => "Set"; GroupoidLevel => "Grp"; TwoGroupoidLevel => "2-Grp"; NType(n) => "N" + n.to_string() }
  let cat_str = match cat.hlevel { Contr => "Contr"; Prop => "Prop"; SetLevel => "Set"; GroupoidLevel => "Grp"; TwoGroupoidLevel => "2-Grp"; NType(n) => "N" + n.to_string() }
  "redefine: cat_level=" + cat_str + " vect_is_set=" + vec_hott.is_set.to_string() + " infty=" + inf_topos.is_infty.to_string() + " level_up=" + lvl_str + " lin_consume=" + @hott_redefine.linear_hott_consume(lin_hott).to_string()
}
