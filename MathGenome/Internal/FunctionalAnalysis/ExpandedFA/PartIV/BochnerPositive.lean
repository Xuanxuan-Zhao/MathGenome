import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BochnerPositive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.BochnerGaussian
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExpandedFA.PartIV.BochnerPositive
open ExpandedFA.Fourier BochnerGaussian

lemma transform_eq_charFun {d : ℕ} (μ : Measure (Euclidean d)) (x : Euclidean d) :
    transform μ x = charFun μ ((2 * Real.pi) • x) := by
  unfold transform charFun
  congr 1
  funext ξ
  congr 1
  simp only [inner_smul_right, real_inner_comm ξ x, Complex.ofReal_mul]
  push_cast
  ring

lemma transform_native {d : ℕ} (μ : Measure (Euclidean d)) (t : Euclidean d) :
    charFun μ t = transform μ ((2 * Real.pi)⁻¹ • t) := by
  rw [transform_eq_charFun, smul_smul, mul_inv_cancel₀ (by positivity :
    (2 * Real.pi : ℝ) ≠ 0), one_smul]

lemma transform_ext {d : ℕ} {μ ν : Measure (Euclidean d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : transform μ = transform ν) : μ = ν := by
  apply Measure.ext_of_charFun
  funext t
  rw [transform_native, transform_native, h]

lemma continuous_transform {d : ℕ} (μ : Measure (Euclidean d)) [IsFiniteMeasure μ] :
    Continuous (transform μ) := by
  have heq : transform μ = fun x => charFun μ ((2 * Real.pi) • x) :=
    funext (transform_eq_charFun μ)
  rw [heq]
  apply continuous_charFun.comp
  fun_prop

lemma positiveDefinite_transform {d : ℕ} (μ : Measure (Euclidean d)) [IsFiniteMeasure μ] :
    PositiveDefiniteContinuity.Spec.PositiveDefinite (transform μ) := by
  apply positiveDefinite_integral μ (fun ξ x => character x ξ)
  · intro x
    exact Integrable.mono' (integrable_const (1 : ℝ))
      (continuous_character x).aestronglyMeasurable (by simp)
  · intro ξ
    have hone : PositiveDefiniteContinuity.Spec.PositiveDefinite (fun _ : Euclidean d => (1 : ℂ)) := by
      intro n x a
      have heq : (∑ j, ∑ k, starRingEnd ℂ (a j) * a k * (1 : ℂ)) =
          starRingEnd ℂ (∑ j, a j) * (∑ j, a j) := by
        simp only [mul_one, map_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      rw [heq]
      constructor
      · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      · simpa [Complex.mul_re, Complex.normSq_apply, pow_two] using Complex.normSq_nonneg (∑ j, a j)
    simpa using positiveDefinite_character_mul hone (fun x y => character_conj_mul x y ξ)

theorem converse : Spec.Converse := by
  intro d μ hμ
  let := hμ
  refine ⟨positiveDefinite_transform μ,
    PositiveDefiniteContinuity.uniformContinuous_of_continuousAt_zero
      (positiveDefinite_transform μ) (continuous_transform μ).continuousAt, ?_⟩
  simp [transform_eq_charFun]

/-- Tightness and compactness give a probability limit, rather than assuming one. -/
lemma exists_probability_of_charFun_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hc : ContinuousAt f 0)
    (hf : ∀ t, Tendsto (fun n => charFun (ν n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range (fun n => (ν n : Measure E))) ∧
      ∃ ρ : ProbabilityMeasure E, charFun ρ = f := by
  have ht := isTightMeasureSet_of_tendsto_charFun hc hf
  refine ⟨ht, ?_⟩
  have hcompact : IsCompact (closure (Set.range ν)) :=
    isCompact_closure_of_isTightMeasureSet (by
      convert ht using 1
      ext μ
      simp)
  obtain ⟨ρ, _, s, hs, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨ρ, funext fun t => ?_⟩
  have htest := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    (BoundedContinuousFunction.innerProbChar t)
  simp only [← charFun_eq_integral_innerProbChar] at htest
  exact tendsto_nhds_unique htest ((hf t).comp hs.tendsto_atTop)

/-- The finite-mass version of the probability compactness argument. -/
lemma exists_finite_of_charFun_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) [∀ n, IsFiniteMeasure (μ n)]
    {M : ℝ} (hM : 0 < M) (hmass : ∀ n, μ n Set.univ = ENNReal.ofReal M)
    (f : E → ℂ) (hc : ContinuousAt f 0)
    (hf : ∀ t, Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range μ) ∧
      ∃ ρ : Measure E, IsFiniteMeasure ρ ∧
        ρ Set.univ = ENNReal.ofReal M ∧ charFun ρ = f := by
  let c := ENNReal.ofReal M
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hM).ne'
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  let ν : ℕ → ProbabilityMeasure E := fun n => ⟨c⁻¹ • μ n, by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul, hmass]
    exact ENNReal.inv_mul_cancel hc0 hctop⟩
  have hback (n : ℕ) : μ n = c • (ν n : Measure E) := by
    change μ n = c • c⁻¹ • μ n
    rw [smul_smul, ENNReal.mul_inv_cancel hc0 hctop, one_smul]
  have hchar (n : ℕ) (t : E) : charFun (ν n) t = (M : ℂ)⁻¹ * charFun (μ n) t := by
    simp [ν, charFun, integral_smul_measure, c, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hM.le, Complex.real_smul]
  have hg : ContinuousAt (fun t => (M : ℂ)⁻¹ * f t) 0 := continuousAt_const.mul hc
  have hlim : ∀ t, Tendsto (fun n => charFun (ν n) t) atTop
      (𝓝 ((M : ℂ)⁻¹ * f t)) := by
    intro t
    simp_rw [hchar]
    exact tendsto_const_nhds.mul (hf t)
  obtain ⟨ht, ρ, hρ⟩ := exists_probability_of_charFun_limit ν _ hg hlim
  constructor
  · rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht ⊢
    intro ε hε
    obtain ⟨K, hK, hb⟩ := ht (ε / c) (ENNReal.div_pos hε.ne' hctop)
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [hback n, Measure.smul_apply, smul_eq_mul]
    calc c * (ν n : Measure E) Kᶜ ≤ c * (ε / c) :=
      mul_le_mul_right (hb _ (Set.mem_range_self n)) c
      _ = ε := ENNReal.mul_div_cancel hc0 hctop
  · refine ⟨c • (ρ : Measure E), ?_, ?_, ?_⟩
    · exact (ρ : Measure E).smul_finite hctop
    · simp [Measure.smul_apply, smul_eq_mul, c]
    · funext t
      simp only [charFun_apply, integral_smul_measure]
      change c.toReal • charFun (ρ : Measure E) t = f t
      rw [hρ]
      simp [c, ENNReal.toReal_ofReal hM.le, Complex.real_smul,
        Complex.ofReal_ne_zero.mpr hM.ne']

lemma tendsto_damped_sequence {d : ℕ} (φ : Euclidean d → ℂ) (x : Euclidean d) :
    Tendsto (fun n : ℕ => damped φ ((n + 1 : ℝ)⁻¹) x) atTop (𝓝 (φ x)) := by
  have hε : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc : Continuous (fun ε : ℝ => damped φ ε x) := by
    unfold damped gaussianFactor
    fun_prop
  simpa only [Function.comp_def, damped, gaussianFactor, mul_zero, zero_mul,
    neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one] using hc.continuousAt.tendsto.comp hε

/-- Apply finite-mass compactness to the particular Gaussian measures. -/
lemma gaussian_limit {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) (hcont : ContinuousAt φ 0) :
    IsTightMeasureSet (Set.range (fun n : ℕ => densityMeasure φ ((n + 1 : ℝ)⁻¹))) ∧
      ∃ μ : Measure (Euclidean d), IsFiniteMeasure μ ∧
        μ Set.univ = ENNReal.ofReal (φ 0).re ∧ transform μ = φ := by
  let μ : ℕ → Measure (Euclidean d) := fun n => densityMeasure φ ((n + 1 : ℝ)⁻¹)
  have heps (n : ℕ) : 0 < (n + 1 : ℝ)⁻¹ := by positivity
  have hprops (n : ℕ) := representation d φ hφ hcont _ (heps n)
  have hmass (n : ℕ) : μ n Set.univ = ENNReal.ofReal (φ 0).re := (hprops n).2.2.1
  have hfinite (n : ℕ) : IsFiniteMeasure (μ n) := (hprops n).1
  let := hfinite
  rcases (PositiveDefiniteContinuity.value_zero hφ).2.eq_or_lt with hz | hM
  · have hzero : φ 0 = 0 := by
      apply Complex.ext
      · simpa using hz.symm
      · simpa using (PositiveDefiniteContinuity.value_zero hφ).1
    have hφzero := PositiveDefiniteContinuity.eq_zero_of_value_zero hφ hzero
    have hμzero (n : ℕ) : μ n = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simp [hmass, hzero]
    constructor
    · have hrange : Set.range μ = {0} := by
        ext ν
        simp only [Set.mem_range, Set.mem_singleton_iff]
        constructor
        · rintro ⟨n, rfl⟩
          exact hμzero n
        · rintro rfl
          exact ⟨0, hμzero 0⟩
      change IsTightMeasureSet (Set.range μ)
      rw [hrange]
      exact isTightMeasureSet_singleton
    · refine ⟨0, inferInstance, by simp [hzero], ?_⟩
      funext x
      simp [hφzero, transform]
  · let f : Euclidean d → ℂ := fun t => φ ((2 * Real.pi)⁻¹ • t)
    have hscale : Continuous (fun t : Euclidean d => (2 * Real.pi)⁻¹ • t) := by fun_prop
    have hc : ContinuousAt f 0 := by
      have hh := hscale.continuousAt (x := (0 : Euclidean d))
      exact (show ContinuousAt φ ((2 * Real.pi)⁻¹ • (0 : Euclidean d)) by
        simpa only [smul_zero] using hcont).comp hh
    have hf (t : Euclidean d) :
        Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (f t)) := by
      have heq (n : ℕ) : charFun (μ n) t =
          damped φ ((n + 1 : ℝ)⁻¹) ((2 * Real.pi)⁻¹ • t) := by
        rw [transform_native]
        exact ((hprops n).2.2.2 _).symm
      simp_rw [heq]
      exact tendsto_damped_sequence φ _
    obtain ⟨ht, ρ, hρfinite, hρmass, hρ⟩ :=
      exists_finite_of_charFun_limit μ hM hmass f hc hf
    refine ⟨ht, ρ, hρfinite, hρmass, ?_⟩
    funext x
    rw [transform_eq_charFun, hρ]
    change φ ((2 * Real.pi)⁻¹ • ((2 * Real.pi) • x)) = φ x
    rw [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]

theorem gaussian_tightness : Spec.GaussianTightness := by
  intro d φ hφ hcont
  exact (gaussian_limit hφ hcont).1

theorem representation : Spec.Representation := by
  intro d φ hφ hcont
  obtain ⟨μ, hfinite, hmass, hrep⟩ := (gaussian_limit hφ hcont).2
  let := hfinite
  refine ⟨μ, ⟨hfinite, inferInstance, hmass, hrep⟩, ?_⟩
  rintro ν ⟨hνfinite, _, _, hνrep⟩
  let := hνfinite
  exact transform_ext (hνrep.trans hrep.symm)

end ExpandedFA.PartIV.BochnerPositive
