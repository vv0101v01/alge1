///|
/// @file axiom_test.mbt
/// # 入口 package 的黑盒測試：demo 管線的輸出契約
///
/// 各主題的定理/演算法測試已隨檔案分到對應 package：
/// `structures/` · `hott_core/` · `hott_hits/` · `hott_redefine/` · `univalence/` ·
/// `cubical/` · `hott_theorems/` · `hott_algorithms/`。
/// 這裡只檢查 root package 的 7 個 demo 函數輸出格式與關鍵數值。

test "demo_pipeline runs" {
  let s = @axiom.demo_pipeline()
  assert_eq(s.contains("demo:"), true)
}

test "high_dim_demo runs" {
  let s = @axiom.high_dim_demo()
  assert_eq(s.contains("high_dim:"), true)
}

test "hott: redefine" {
  let s = @axiom.redefine_demo()
  assert_eq(s.contains("redefine:"), true)
  let h = @axiom.hott_demo()
  assert_eq(h.contains("hott:"), true)
  let hits = @axiom.hits_demo()
  assert_eq(hits.contains("hits:"), true)
  let nt = @axiom.new_theorems_demo()
  assert_eq(nt.contains("new_thms:"), true)
  let ha = @axiom.hott_algorithms_demo()
  assert_eq(ha.contains("hott_algo:"), true)
  let cu = @axiom.cubical_demo()
  assert_eq(cu.contains("cubical: axioms=0"), true)
  assert_eq(cu.contains("C1C2C3=true"), true)
  assert_eq(cu.contains("kan=true"), true)
  assert_eq(cu.contains("sound=true"), true)
}

///|

test "U7 demo 輸出：公理數 0、定理成立、SIP 分類 7" {
  let s = @axiom.univalence_theorem_demo()
  assert_true(s.contains("univalence_thm: axioms=0"))
  assert_true(s.contains("holds=true"))
  assert_true(s.contains("pi1_S3=true"))
  assert_true(s.contains("ua_beta=true"))
  assert_true(s.contains("funext=true"))
  assert_true(s.contains("prop_ext=true"))
  assert_true(s.contains("sip_classes=7"))
  // 摘要逐行可讀（供 README / docs 引用）
  let summary = @univalence.univalence_summary(4)
  assert_true(summary.contains("n=3 paths=6=6 equivs=6"))
  assert_true(summary.contains("holds=true"))
}
