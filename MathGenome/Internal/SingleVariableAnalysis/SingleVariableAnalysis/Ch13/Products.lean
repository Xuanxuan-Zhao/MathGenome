import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Radius
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.CauchyProduct
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Geometric
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Products

/-! K03.13.products: absolute numerical Cauchy products at each interior
argument, followed by the radius dichotomy. The last two theorems verify
the strict-enlargement example for both scalar fields. -/
noncomputable section
namespace SingleVariableAnalysis
open scoped BigOperators ENNReal Topology

/-- Factoring the common power out of a finite convolution. -/
theorem cauchyProduct_monomials {K : Type*} [CommSemiring K]
    (a b : ℕ → K) (t : K) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (a k * t^k) * (b (n-k) * t^(n-k))) =
      (∑ k ∈ Finset.range (n+1), a k * b (n-k)) * t^n := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k + (n-k) = n := Nat.add_sub_of_le (by
    have := Finset.mem_range.mp hk
    omega)
  calc
    _ = (a k * b (n-k)) * (t^k * t^(n-k)) := by ring
    _ = _ := by rw [← pow_add, hkn]

theorem real_powerSeries_product_terms (a b : ℕ → ℝ) (c x : ℝ) :
    realCauchyProduct (realPowerSeriesTerm a c x) (realPowerSeriesTerm b c x) =
      realPowerSeriesTerm (realCauchyProduct a b) c x := by
  funext n
  exact cauchyProduct_monomials a b (x-c) n

theorem real_powerSeries_product_hasSum (a b : ℕ → ℝ) (c x : ℝ) (A B : ℝ)
    (h : ENNReal.ofReal |x-c| < min (realPowerSeriesRadius a) (realPowerSeriesRadius b))
    (hA : RealPowerSeriesHasSum a c x A) (hB : RealPowerSeriesHasSum b c x B) :
    RealPowerSeriesHasSum (realCauchyProduct a b) c x (A * B) := by
  have ha := real_powerSeries_radius_absolute a c x (lt_min_iff.mp h).1
  have hp := real_mertens _ _ A B ha hA hB
  rw [real_powerSeries_product_terms] at hp
  exact hp

theorem real_powerSeries_product_absolute (a b : ℕ → ℝ) (c x : ℝ)
    (h : ENNReal.ofReal |x-c| < min (realPowerSeriesRadius a) (realPowerSeriesRadius b)) :
    RealPowerSeriesAbsolutelyConverges (realCauchyProduct a b) c x := by
  have ha := real_powerSeries_radius_absolute a c x (lt_min_iff.mp h).1
  have hb := real_powerSeries_radius_absolute b c x (lt_min_iff.mp h).2
  have hp := real_cauchyProduct_absolute _ _ ha hb
  rw [real_powerSeries_product_terms] at hp
  exact hp

theorem real_powerSeries_product_radius (a b : ℕ → ℝ) :
    min (realPowerSeriesRadius a) (realPowerSeriesRadius b) ≤ realPowerSeriesRadius (realCauchyProduct a b) := by
  apply le_of_not_gt
  intro h
  obtain ⟨t, ht, hpt, htm⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  have hd : |t-0| = t := by simpa using abs_of_nonneg ht
  have hc := real_powerSeries_product_absolute a b 0 t (by rwa [hd])
  exact real_powerSeries_radius_diverges _ 0 t (by rwa [hd])
    (real_absolute_converges _ hc)

theorem complex_powerSeries_product_terms (a b : ℕ → ℂ) (c : ℝ) (x : ℂ) :
    complexCauchyProduct (complexPowerSeriesTerm a c x) (complexPowerSeriesTerm b c x) =
      complexPowerSeriesTerm (complexCauchyProduct a b) c x := by
  funext n
  exact cauchyProduct_monomials a b (x-(c : ℂ)) n

theorem complex_powerSeries_product_hasSum (a b : ℕ → ℂ) (c : ℝ) (x : ℂ) (A B : ℂ)
    (h : ENNReal.ofReal ‖x-(c : ℂ)‖ < min (complexPowerSeriesRadius a) (complexPowerSeriesRadius b))
    (hA : ComplexPowerSeriesHasSum a c x A) (hB : ComplexPowerSeriesHasSum b c x B) :
    ComplexPowerSeriesHasSum (complexCauchyProduct a b) c x (A * B) := by
  have ha := complex_powerSeries_radius_absolute a c x (lt_min_iff.mp h).1
  have hp := complex_mertens _ _ A B ha hA hB
  rw [complex_powerSeries_product_terms] at hp
  exact hp

theorem complex_powerSeries_product_absolute (a b : ℕ → ℂ) (c : ℝ) (x : ℂ)
    (h : ENNReal.ofReal ‖x-(c : ℂ)‖ < min (complexPowerSeriesRadius a) (complexPowerSeriesRadius b)) :
    ComplexPowerSeriesAbsolutelyConverges (complexCauchyProduct a b) c x := by
  have ha := complex_powerSeries_radius_absolute a c x (lt_min_iff.mp h).1
  have hb := complex_powerSeries_radius_absolute b c x (lt_min_iff.mp h).2
  have hp := complex_cauchyProduct_absolute _ _ ha hb
  rw [complex_powerSeries_product_terms] at hp
  exact hp

theorem complex_powerSeries_product_radius (a b : ℕ → ℂ) :
    min (complexPowerSeriesRadius a) (complexPowerSeriesRadius b) ≤ complexPowerSeriesRadius (complexCauchyProduct a b) := by
  apply le_of_not_gt
  intro h
  obtain ⟨t, ht, hpt, htm⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  have hd : ‖(t : ℂ)-(0 : ℝ)‖ = t := by
    simpa using (show ‖(t : ℂ)‖ = t by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht])
  have hc := complex_powerSeries_product_absolute a b 0 (t : ℂ) (by rwa [hd])
  exact complex_powerSeries_radius_diverges _ 0 (t : ℂ) (by rwa [hd])
    (complex_absolute_converges _ hc)

/-- The inclusive partial sum of the coefficient sequence of 1-X. -/
theorem sum_oneSubX_monomials {K : Type*} [Ring K] (t : K) (N : ℕ)
    (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range (N+1),
      (if n = 0 then 1 else if n = 1 then -1 else 0) * t^n) = 1-t := by
  calc
    _ = ∑ n ∈ Finset.range (N+1),
        ((if n = 0 then 1 else 0) - (if n = 1 then t else 0)) := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases h0 : n = 0
      · simp [h0]
      · by_cases h1 : n = 1
        · simp [h1]
        · simp [h0, h1]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp [show 1 < N+1 by omega]

/-- Finite coefficient cancellation in (1+X+X²+⋯)(1-X). -/
theorem cauchyProduct_geometric_oneSubX {K : Type*} [Ring K] (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (1 : K) *
      (if n-k = 0 then 1 else if n-k = 1 then -1 else 0)) =
      if n = 0 then 1 else 0 := by
  simp only [one_mul]
  by_cases hn : n = 0
  · simp [hn]
  · have hr := Finset.sum_range_reflect
      (fun k => (if k = 0 then (1 : K) else if k = 1 then -1 else 0)) (n+1)
    simp only [Nat.add_sub_cancel] at hr
    rw [hr]
    have hs := sum_oneSubX_monomials (1 : K) n (by omega)
    simpa [hn] using hs

theorem real_powerSeries_oneSubX_hasSum (x : ℝ) :
    RealPowerSeriesHasSum (fun n => if n = 0 then 1 else if n = 1 then -1 else 0) 0 x (1-x) := by
  intro ε hε
  refine ⟨1, fun N hN => ?_⟩
  simpa only [realPowerSeriesPartialSum, realPartialSum, realPowerSeriesTerm,
    sub_zero, sum_oneSubX_monomials x N hN,
    sub_self, abs_zero] using hε

theorem real_powerSeries_constant_hasSum (x : ℝ) :
    RealPowerSeriesHasSum (fun n => if n = 0 then 1 else 0) 0 x 1 := by
  intro ε hε
  refine ⟨0, fun N _ => ?_⟩
  simpa [realPowerSeriesPartialSum, realPartialSum, realPowerSeriesTerm, ite_mul] using hε

theorem complex_powerSeries_oneSubX_hasSum (x : ℂ) :
    ComplexPowerSeriesHasSum (fun n => if n = 0 then 1 else if n = 1 then -1 else 0) 0 x (1-x) := by
  intro ε hε
  refine ⟨1, fun N hN => ?_⟩
  simpa only [complexPowerSeriesPartialSum, complexPartialSum, complexPowerSeriesTerm,
    Complex.ofReal_zero, sub_zero, sum_oneSubX_monomials x N hN,
    sub_self, norm_zero] using hε

theorem complex_powerSeries_constant_hasSum (x : ℂ) :
    ComplexPowerSeriesHasSum (fun n => if n = 0 then 1 else 0) 0 x 1 := by
  intro ε hε
  refine ⟨0, fun N _ => ?_⟩
  simpa [complexPowerSeriesPartialSum, complexPartialSum, complexPowerSeriesTerm, ite_mul] using hε

private theorem nonnegativeRoot_one (n : ℕ) : nonnegativeRoot (n+1) 1 = 1 :=
  (nonnegativeRoot_unique (n+1) (Nat.succ_pos _) 1 zero_le_one 1 zero_le_one
    (one_pow _)).symm

theorem real_powerSeries_geometric_radius :
    realPowerSeriesRadius (fun _ => (1 : ℝ)) = 1 := by
  simp [realPowerSeriesRadius, realPowerSeriesRootGrowth, abs_one, nonnegativeRoot_one,
    Filter.limsup_const]

/-- An eventually zero coefficient sequence has infinite radius. -/
theorem real_powerSeries_finite_radius (a : ℕ → ℝ) (M : ℕ)
    (h : ∀ n ≥ M, a n = 0) : realPowerSeriesRadius a = ⊤ := by
  have hg : realPowerSeriesRootGrowth a = 0 := by
    unfold realPowerSeriesRootGrowth
    calc
      _ = Filter.limsup (fun _ : ℕ => (0 : ℝ≥0∞)) Filter.atTop := by
        apply Filter.limsup_congr
        apply Filter.eventually_atTop.mpr
        refine ⟨M, fun n hn => ?_⟩
        rw [h (n+1) (by omega)]
        simp only [abs_zero, nonnegativeRoot_zero _ (Nat.succ_pos _), ENNReal.ofReal_zero]
      _ = 0 := Filter.limsup_const _
  simp [realPowerSeriesRadius, hg]

theorem complex_powerSeries_geometric_radius :
    complexPowerSeriesRadius (fun _ => (1 : ℂ)) = 1 := by
  simp [complexPowerSeriesRadius, complexPowerSeriesRootGrowth, norm_one, nonnegativeRoot_one,
    Filter.limsup_const]

/-- An eventually zero coefficient sequence has infinite radius. -/
theorem complex_powerSeries_finite_radius (a : ℕ → ℂ) (M : ℕ)
    (h : ∀ n ≥ M, a n = 0) : complexPowerSeriesRadius a = ⊤ := by
  have hg : complexPowerSeriesRootGrowth a = 0 := by
    unfold complexPowerSeriesRootGrowth
    calc
      _ = Filter.limsup (fun _ : ℕ => (0 : ℝ≥0∞)) Filter.atTop := by
        apply Filter.limsup_congr
        apply Filter.eventually_atTop.mpr
        refine ⟨M, fun n hn => ?_⟩
        rw [h (n+1) (by omega)]
        simp only [norm_zero, nonnegativeRoot_zero _ (Nat.succ_pos _), ENNReal.ofReal_zero]
      _ = 0 := Filter.limsup_const _
  simp [complexPowerSeriesRadius, hg]

theorem real_powerSeries_product_enlargement :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => if n = 0 then 1 else if n = 1 then -1 else 0
    realPowerSeriesRadius a = 1 ∧
    realPowerSeriesRadius b = ⊤ ∧
    realCauchyProduct a b = (fun n => if n = 0 then 1 else 0) ∧
    realPowerSeriesRadius (realCauchyProduct a b) = ⊤ ∧
    min (realPowerSeriesRadius a) (realPowerSeriesRadius b) < realPowerSeriesRadius (realCauchyProduct a b) ∧
    ∀ x : ℝ, |x| < 1 →
      RealPowerSeriesHasSum a 0 x (1 / (1-x)) ∧
      RealPowerSeriesHasSum b 0 x (1-x) ∧
      RealPowerSeriesHasSum (realCauchyProduct a b) 0 x 1 ∧
      (1 / (1-x)) * (1-x) = 1 := by
  dsimp only
  have ha := real_powerSeries_geometric_radius
  have hb : realPowerSeriesRadius
      (fun n => if n = 0 then 1 else if n = 1 then -1 else 0) = ⊤ := by
    apply real_powerSeries_finite_radius _ 2
    intro n hn
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]
  have hc : realCauchyProduct (fun _ => 1)
      (fun n => if n = 0 then 1 else if n = 1 then -1 else 0) =
      (fun n => if n = 0 then 1 else 0) := by
    funext n
    exact cauchyProduct_geometric_oneSubX n
  have hr : realPowerSeriesRadius (fun n => if n = 0 then 1 else 0) = ⊤ := by
    apply real_powerSeries_finite_radius _ 1
    intro n hn
    simp [show n ≠ 0 by omega]
  refine ⟨ha, hb, hc, hc ▸ hr, ?_, ?_⟩
  · rw [ha, hb, hc, hr, min_eq_left le_top]
    exact ENNReal.one_lt_top
  · intro x hx
    have hne : (1 : ℝ) - x ≠ 0 := by
      intro he
      have heq : x = 1 := (sub_eq_zero.mp he).symm
      simp [heq] at hx
    refine ⟨?_, real_powerSeries_oneSubX_hasSum x, ?_, ?_⟩
    · change RealSeriesHasSum (fun n => (1 : ℝ) * (x-0)^n) (1 / (1-x))
      simpa only [one_mul, sub_zero] using real_geometric_series_hasSum x hx
    · rw [hc]
      exact real_powerSeries_constant_hasSum x
    · exact div_mul_cancel₀ 1 hne

theorem complex_powerSeries_product_enlargement :
    let a : ℕ → ℂ := fun _ => 1
    let b : ℕ → ℂ := fun n => if n = 0 then 1 else if n = 1 then -1 else 0
    complexPowerSeriesRadius a = 1 ∧
    complexPowerSeriesRadius b = ⊤ ∧
    complexCauchyProduct a b = (fun n => if n = 0 then 1 else 0) ∧
    complexPowerSeriesRadius (complexCauchyProduct a b) = ⊤ ∧
    min (complexPowerSeriesRadius a) (complexPowerSeriesRadius b) < complexPowerSeriesRadius (complexCauchyProduct a b) ∧
    ∀ x : ℂ, ‖x‖ < 1 →
      ComplexPowerSeriesHasSum a 0 x (1 / (1-x)) ∧
      ComplexPowerSeriesHasSum b 0 x (1-x) ∧
      ComplexPowerSeriesHasSum (complexCauchyProduct a b) 0 x 1 ∧
      (1 / (1-x)) * (1-x) = 1 := by
  dsimp only
  have ha := complex_powerSeries_geometric_radius
  have hb : complexPowerSeriesRadius
      (fun n => if n = 0 then 1 else if n = 1 then -1 else 0) = ⊤ := by
    apply complex_powerSeries_finite_radius _ 2
    intro n hn
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]
  have hc : complexCauchyProduct (fun _ => 1)
      (fun n => if n = 0 then 1 else if n = 1 then -1 else 0) =
      (fun n => if n = 0 then 1 else 0) := by
    funext n
    exact cauchyProduct_geometric_oneSubX n
  have hr : complexPowerSeriesRadius (fun n => if n = 0 then 1 else 0) = ⊤ := by
    apply complex_powerSeries_finite_radius _ 1
    intro n hn
    simp [show n ≠ 0 by omega]
  refine ⟨ha, hb, hc, hc ▸ hr, ?_, ?_⟩
  · rw [ha, hb, hc, hr, min_eq_left le_top]
    exact ENNReal.one_lt_top
  · intro x hx
    have hne : (1 : ℂ) - x ≠ 0 := by
      intro he
      have heq : x = 1 := (sub_eq_zero.mp he).symm
      simp [heq] at hx
    refine ⟨?_, complex_powerSeries_oneSubX_hasSum x, ?_, ?_⟩
    · change ComplexSeriesHasSum (fun n => (1 : ℂ) * (x-0)^n) (1 / (1-x))
      simpa only [one_mul, sub_zero] using complex_geometric_series_hasSum x hx
    · rw [hc]
      exact complex_powerSeries_constant_hasSum x
    · exact div_mul_cancel₀ 1 hne

end SingleVariableAnalysis
