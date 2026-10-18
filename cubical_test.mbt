///|
/// @file cubical_test.mbt
/// # 有限立方體演算法的可執行證明
///
/// 對應 `hott_cubical.mbt`。這裡沒有任何 `assert_true(true)`：每個布林值都由
/// `cubical_proof` / `kan_proof` / `nbe_proof` / `cube_euler_enum_check` 等函數
/// 在有限模型上**窮盡計算**得出（維度上限：K1 dim≤4、K2 card≤5、K3 depth≤2）。
/// 命令：`moon test`

/// 3-循環 (0 1 2)：b(0)=1, b(1)=2, b(2)=0
fn cyc3() -> @axiom.Bij {
  match @axiom.bij_make(3, [1, 2, 0]) {
    Some(b) => b
    None => abort("cyc3: not a bijection")
  }
}

///|
test "K1a 立方體範疇公理：dim ≤ 3 全部窮盡成立" {
  let pf = @axiom.cubical_proof(3)
  assert_true(pf.faithful) // 忠实性：結構複合 = 逐點複合
  assert_true(pf.coface_coface) // C1 ∂_{j+1,δ}∂_{i,ε} = ∂_{i,ε}∂_{j,δ}
  assert_true(pf.degen_degen) // C2 σ_i σ_j = σ_{j-1} σ_i
  assert_true(pf.degen_coface) // C3 σ_j ∂_{i,ε} 的三段式
  assert_true(pf.assoc_unit) // 結合律 + 單位律
  assert_true(pf.count_law) // |Hom| = Σ_k C(n,k)C(m,k)2^(n-k)
  assert_true(pf.variant_counts) // □ ⊂ □^swap ⊂ □^conn
  assert_true(pf.generated_by) // 每個態射都是 face/degen 的複合
  assert_true(pf.sound_eq) // 結構相等 ⟺ 外延相等
  assert_true(pf.checks > 90000) // 檢查數由計算得出，不是寫死的
  assert_true(@axiom.cubical_holds(4))
}

///|
test "K1b 面映射/退化映射的具體計算" {
  // ∂_{0,1} : [2] → [3] = [Const 1, Var0, Var1]
  let f = {
    match @axiom.face_map(2, 0, 1) {
      Some(m) => m
      None => abort("face_map")
    }
  }
  assert_eq(f.dom, 2)
  assert_eq(f.cod, 3)
  let fv = @axiom.cubemap_apply(f, [1, 0])
  assert_eq(fv.length(), 3)
  assert_eq(fv[0], 1)
  assert_eq(fv[1], 1)
  assert_eq(fv[2], 0)
  // σ_1 : [3] → [2] 忘掉第 1 個座標
  let g = {
    match @axiom.degen_map(2, 1) {
      Some(m) => m
      None => abort("degen_map")
    }
  }
  let gv = @axiom.cubemap_apply(g, [1, 0, 1])
  assert_eq(gv.length(), 2)
  assert_eq(gv[0], 1)
  assert_eq(gv[1], 1)
  // 外延相等與結構相等一致
  assert_true(@axiom.cubemap_eq_points(f, f))
  assert_true(@axiom.cubemap_eq(f, f))
}

///|
test "K1c Hom 計數公式與枚舉一致（三層 cube 範疇）" {
  // 標準 □（Kan / CCHM coarse cube category）
  assert_eq(@axiom.cube_hom_count_standard(2, 2), 13)
  assert_eq(@axiom.cube_hom_count_standard(1, 2), 8)
  assert_eq(@axiom.cube_hom_count_standard(3, 2), 19)
  assert_eq(@axiom.cube_hom_count_standard(2, 3), 38)
  assert_eq(@axiom.cube_hom_count_standard(3, 3), 63)
  // cartesian □（加 swap 生成元）
  assert_eq(@axiom.cube_hom_count_swaps(2, 2), 14)
  // 最大 cube 範疇（加 connections）
  assert_eq(@axiom.cube_hom_count_full(2, 2), 16)
  // 枚舉 = 公式
  assert_eq(@axiom.cubemap_all_standard(2, 2).length(), 13)
  assert_eq(@axiom.cubemap_all_with_swaps(2, 2).length(), 14)
  assert_eq(@axiom.cubemap_all_full(2, 2).length(), 16)
  // 生成律：BFS 閉包（id + face + degen）= 標準 □
  assert_eq(@axiom.cubemap_generated(3, 2).length(), 19)
  assert_eq(@axiom.cubemap_generated(2, 2).length(), 13)
}

///|
test "K1d n-立方體面格、Euler 特徵數、Gray 碼 Hamiltonian 圈" {
  // k 維面數 C(n,k)·2^(n-k)：Q³ 的 頂點/邊/面/體 = 8/12/6/1
  assert_eq(@axiom.cube_face_count(3, 0), 8)
  assert_eq(@axiom.cube_face_count(3, 1), 12)
  assert_eq(@axiom.cube_face_count(3, 2), 6)
  assert_eq(@axiom.cube_face_count(3, 3), 1)
  assert_eq(@axiom.cube_face_count(4, 2), 24)
  // χ(Q^n) = (2-1)^n = 1（n-立方體可縮）；**枚舉**重算也是 1
  assert_eq(@axiom.cube_euler(3), 1)
  assert_eq(@axiom.cube_euler(5), 1)
  for n in 0..=5 {
    assert_true(@axiom.cube_euler_enum_check(n))
    assert_true(@axiom.gray_hamiltonian_check(n))
  }
  assert_eq(@axiom.cube_points_gray(3).length(), 8)
}

///|
test "K2a Kan 填充：card ≤ 5 的七條定律全部窮盡成立" {
  for card in 0..=5 {
    let pf = @axiom.kan_proof(card)
    assert_true(pf.exists) // 上邊缺失的盒恆有填充體
    assert_true(pf.unique_iff) // 可填 ⟺ top = transport path bottom（盒條件）
    assert_true(pf.universal) // 填充體 = glue 的消除 = transport
    assert_true(pf.functorial) // transport (q∘p) x = transport q (transport p x)
    assert_true(pf.roundtrip) // transport (sym p) (transport p x) = x
    assert_true(pf.refl_law) // transport refl x = x
    assert_true(pf.ua_beta) // **uaβ**：transport (ua e) x = e x
    assert_true(@axiom.kan_holds(card))
    if card >= 1 {
      assert_true(pf.checks > 0) // card = 0 時沒有元素可檢查，checks = 0 是正常的
    }
  }
}

///|
test "K2b 不相容的盒沒有填充體" {
  let a = @axiom.fin("Fin3", 3)
  let paths = @axiom.upath_all(a, a)
  assert_eq(paths.length(), 6) // |Fin3 = Fin3| = 3! = 6
  let p = paths[1] // 非 refl 的路徑
  let x = 0
  let good = @axiom.upath_transport(p, x)
  // 正確的上邊 ⇒ 可填；錯誤的上邊 ⇒ None（無填充體）
  let ok = @axiom.kan_fill_el({ path: p, bottom: x, top: Some(good) })
  match ok {
    Some(f) => {
      assert_eq(f.top, good)
      assert_true(f.compatible)
    }
    None => abort("compatible box must be fillable")
  }
  let mut filled = 0
  for y in 0..<3 {
    if y != good {
      match @axiom.kan_fill_el({ path: p, bottom: x, top: Some(y) }) {
        Some(_) => abort("incompatible box must not be fillable")
        None => filled = filled + 1
      }
    }
  }
  assert_eq(filled, 2)
  // 越界元素 ⇒ 盒不成立
  match @axiom.kan_fill_el({ path: p, bottom: 9, top: None }) {
    Some(_) => abort("out-of-range element must not be fillable")
    None => ()
  }
}

///|
test "K2c Lehmer 排名/反排名是 S_n ≅ [0,n!) 的顯式雙射" {
  for card in 0..=5 {
    assert_true(@axiom.lehmer_bijection_check(card))
  }
  // 3-循環 (0 1 2) 的秩與反排名
  let r = @axiom.lehmer_code(cyc3())
  match @axiom.perm_from_lehmer(3, r) {
    Some(b) => assert_true(@axiom.bij_eq(b, cyc3()))
    None => abort("perm_from_lehmer")
  }
  match @axiom.perm_from_lehmer(3, 6) {
    Some(_) => abort("rank out of range")
    None => ()
  }
}

///|
test "K3a cubical NBE：全部定律窮盡成立" {
  let pf = @axiom.nbe_proof(3, 1, 6, 8)
  assert_true(pf.rewrite_sound) // 每步重寫都保語義
  assert_true(pf.norm_sound) // eval(norm t) = eval t
  assert_true(pf.agrees) // 重寫系統與 NBE 一致
  assert_true(pf.idempotent) // norm ∘ norm = norm
  assert_true(pf.normal_forms) // 範式是不動點
  assert_true(pf.terminated) // 全部項在 max_steps 內收斂
  assert_true(pf.measure_ok) // 勢函數 Φ=(size, sym 數) 每步嚴格遞減 ⇒ 強正規化
  assert_true(pf.reassoc_sound) // R8 重結合是語義 coherence（保語義、保大小）
  assert_true(pf.max_steps <= 8)
  assert_true(pf.equivalence) // judgmental_eq_ct 是等價關係
  assert_true(pf.eq_sound) // 判斷相等 ⇒ 語義相同
  assert_true(pf.eq_complete) // 語義相同 ⇒ 判斷相等
  assert_true(pf.terms > 200)
  assert_true(pf.checks > 1000)
  assert_true(@axiom.nbe_holds(2, 2, 2, 8))
}

///|
test "K3b 具體化簡：uaβ、glue、refl、sym" {
  let card = 3
  let sigma = @axiom.lehmer_code(cyc3())
  let x = 1
  // transport (ua σ) x → transport σ x → σ x（Kan 填充 / uaβ）
  let t = @axiom.CTransport(@axiom.CUa(@axiom.CSigma(sigma)), @axiom.CElem(x))
  let (nf, steps) = @axiom.crewrite(t, card, 8)
  assert_true(steps >= 1) // 重寫確實發生了
  assert_true(@axiom.cterm_eq(nf, @axiom.CElem(@axiom.bij_apply(cyc3(), x))))
  assert_eq(@axiom.bij_apply(cyc3(), x), 2)
  // ua(id) → refl
  let (nf2, _) = @axiom.crewrite(@axiom.CUa(@axiom.CSigma(0)), card, 8)
  assert_true(@axiom.cterm_eq(nf2, @axiom.CRefl))
  // transport refl x → x
  let (nf3, _) = @axiom.crewrite(@axiom.CTransport(@axiom.CRefl, @axiom.CElem(2)), card, 8)
  assert_true(@axiom.cterm_eq(nf3, @axiom.CElem(2)))
  // sym(sym p) → p
  let (nf4, _) = @axiom.crewrite(
    @axiom.CSym(@axiom.CSym(@axiom.CUa(@axiom.CSigma(1)))), card, 8,
  )
  assert_true(@axiom.cterm_eq(nf4, @axiom.CUa(@axiom.CSigma(1))))
  // trans 單位律
  let (nf5, _) = @axiom.crewrite(
    @axiom.CTrans(@axiom.CRefl, @axiom.CUa(@axiom.CSigma(1))), card, 8,
  )
  assert_true(@axiom.cterm_eq(nf5, @axiom.CUa(@axiom.CSigma(1))))
  // ua σ ∘ ua τ → ua (τ∘σ)
  let s1 = @axiom.lehmer_code(cyc3())
  let s2 = @axiom.lehmer_code(@axiom.bij_inv(cyc3()))
  let (nf6, _) = @axiom.crewrite(
    @axiom.CTrans(@axiom.CUa(@axiom.CSigma(s1)), @axiom.CUa(@axiom.CSigma(s2))), card, 8,
  )
  assert_true(@axiom.cterm_eq(nf6, @axiom.CRefl)) // σ⁻¹∘σ = id
  // 判斷相等：語義相同 ⇒ 相等；不同 ⇒ 不相等
  assert_true(@axiom.judgmental_eq_ct(t, @axiom.CElem(2), card))
  assert_false(
    @axiom.judgmental_eq_ct(
      @axiom.CTransport(@axiom.CRefl, @axiom.CElem(1)), @axiom.CElem(2), card,
    ),
  )
  assert_false(@axiom.judgmental_eq_ct(@axiom.CUa(@axiom.CSigma(1)), @axiom.CRefl, card))
  // 卡住的項（型別不合）保持原樣，不假裝成功
  let ill = @axiom.CElem(99)
  assert_true(@axiom.cterm_eq(@axiom.cnorm(ill, card), ill))
  match @axiom.ceval(ill, card) {
    Some(_) => abort("ill-typed term must not evaluate")
    None => ()
  }
}

///|
test "K3c 重寫守衛與勢函數：卡住的項不會被「修好」" {
  let card = 3
  // transport(refl, σ0)：第二個參數是**路徑**而非元素 ⇒ 盒不成立，求値卡住
  let ill = @axiom.CTransport(@axiom.CRefl, @axiom.CSigma(0))
  match @axiom.ceval(ill, card) {
    Some(_) => abort("ill-typed transport must not evaluate")
    None => ()
  }
  // 守衛前 R1 會把它改寫成 σ0（語義由「卡住」變「有値」= 不健全）；守衛後 0 步
  let (nf, steps) = @axiom.crewrite(ill, card, 8)
  assert_eq(steps, 0)
  assert_true(@axiom.cterm_eq(nf, ill))
  // 良型版本則確實化簡
  let ok = @axiom.CTransport(@axiom.CRefl, @axiom.CElem(1))
  assert_true(@axiom.cterm_eq(@axiom.crewrite(ok, card, 8).0, @axiom.CElem(1)))
  // R10：sym(ua σ) → ua σ⁻¹，size 3 → 2、sym 節點數 1 → 0（Φ 嚴格遞減）
  let s = @axiom.CSym(@axiom.CUa(@axiom.CSigma(1)))
  let (nf2, st2) = @axiom.crewrite(s, card, 8)
  assert_true(st2 >= 1)
  assert_eq(@axiom.cterm_size(s), 3)
  assert_eq(@axiom.cterm_size(nf2), 2)
  assert_true(@axiom.cterm_sym_count(nf2) < @axiom.cterm_sym_count(s))
  assert_true(@axiom.phi_lt(@axiom.cterm_phi(nf2), @axiom.cterm_phi(s)))
  // R8 重結合：保大小，且判斷相等（語義 coherence）
  let t3 = @axiom.CTrans(
    @axiom.CTrans(@axiom.CUa(@axiom.CSigma(1)), @axiom.CUa(@axiom.CSigma(2))),
    @axiom.CUa(@axiom.CSigma(3)),
  )
  assert_eq(@axiom.cterm_size(@axiom.creassoc(t3)), @axiom.cterm_size(t3))
  assert_true(@axiom.judgmental_eq_ct(t3, @axiom.creassoc(t3), card))
}

///|
test "K0 公理審計：有限立方體演算法引入的公理數 = 0" {
  assert_eq(@axiom.cubical_axiom_count(), 0)
  assert_eq(@axiom.univalence_axiom_count(), 0)
}

///|
test "H1 cubical_transport 在 refl 上是恒等（Kan 填充的 code 族特例）" {
  assert_eq(@axiom.kan_transport_code(0, 99), 99)
  assert_eq(@axiom.cubical_transport(@axiom.refl(99), 99), 99)
  // 加法直線族：code = c 的路徑把 v 平移 c
  assert_eq(@axiom.kan_transport_code(3, 10), 13)
  assert_eq(@axiom.cubical_transport({ lhs: 3, rhs: 7, code: 3 }, 10), 13)
}
