import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SpectralProductAndSumDomains
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.Definitions

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ExpandedFA.Unbounded.MeasurableSpectralCalculus
open MeasureTheory Set Filter
universe u v
variable {S : Type u} {K : Type v} [MeasurableSpace S]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : SpectralMeasure.ProjectionValuedMeasure S K} (C : BoundedRealization E)

theorem unbounded_lintegral_norm_sq {f : S → ℂ} (hf : Measurable f)
    (x : (measurableIntegral C f).domain) :
    (∫⁻ s, ENNReal.ofReal (‖f s‖ ^ 2) ∂C.measure x) =
      ENNReal.ofReal (‖measurableIntegral C f x‖ ^ 2) := by
  have hMCT : Tendsto
      (fun n => ∫⁻ s, ENNReal.ofReal (‖truncation f n s‖ ^ 2) ∂C.measure x)
      atTop (nhds (∫⁻ s, ENNReal.ofReal (‖f s‖ ^ 2) ∂C.measure x)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun n => (ENNReal.measurable_ofReal.comp
        ((measurable_truncation hf n).norm.pow_const 2)).aemeasurable
    · exact Eventually.of_forall (fun s n m hnm =>
        ENNReal.ofReal_le_ofReal (truncation_norm_sq_mono f s hnm))
    · exact Eventually.of_forall (fun s =>
        (ENNReal.continuous_ofReal.tendsto _).comp ((truncation_tendsto f s).norm.pow 2))
  have hnorm := (ENNReal.continuous_ofReal.tendsto _).comp
    ((measurableIntegral_tendsto C f x).norm.pow 2)
  simp only [C.lintegral_norm_sq _ (boundedMeasurable_truncation hf _) x] at hMCT
  exact tendsto_nhds_unique hMCT hnorm

theorem unbounded_integrable_norm_sq {f : S → ℂ} (hf : Measurable f)
    (x : (measurableIntegral C f).domain) :
    Integrable (fun s => ‖f s‖ ^ 2) (C.measure x) := by
  refine ⟨(hf.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => sq_nonneg ‖f s‖)).mpr
  rw [unbounded_lintegral_norm_sq C hf x]
  exact ENNReal.ofReal_lt_top

theorem unbounded_norm_sq {f : S → ℂ} (hf : Measurable f)
    (x : (measurableIntegral C f).domain) :
    ‖measurableIntegral C f x‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂C.measure x := by
  have hh := ofReal_integral_eq_lintegral_ofReal
    (unbounded_integrable_norm_sq C hf x)
    (Eventually.of_forall fun s => sq_nonneg ‖f s‖)
  rw [unbounded_lintegral_norm_sq C hf x] at hh
  have hhreal := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun s => sq_nonneg ‖f s‖),
    ENNReal.toReal_ofReal (sq_nonneg _)] using hhreal.symm

theorem norm_integral_truncation_le (C : BoundedRealization E)
    {f : S → ℂ} (hf : Measurable f)
    (y : (measurableIntegral C f).domain) (n : ℕ) :
    ‖C.integral (truncation f n) y‖ ≤ ‖measurableIntegral C f y‖ := by
  have hs : ‖C.integral (truncation f n) y‖ ^ 2 ≤
      ‖measurableIntegral C f y‖ ^ 2 := by
    rw [C.norm_sq _ (boundedMeasurable_truncation hf n) y, unbounded_norm_sq C hf y]
    apply integral_mono (C.integrable_norm_sq _ (boundedMeasurable_truncation hf n) y)
      (unbounded_integrable_norm_sq C hf y)
    intro s
    by_cases hsn : ‖f s‖ ≤ (n : ℝ)
    · simp [truncation, hsn]
    · simp [truncation, hsn]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs


end ExpandedFA.Unbounded.MeasurableSpectralCalculus


namespace ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus.SupportWork
open SpectralMeasure MeasurableSpectralCalculus
open UnboundedNormalSpectralTheorem.SpectralRepresentation
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_coercion (y v : H) (M ε : ℝ) (hε : 0 < ε)
    (hpos : 0 ≤ (inner ℂ y v).re)
    (hn : ‖v + (M : ℂ) • y‖ ≤ (M - ε) * ‖y‖) : y = 0 := by
  have hc := re_inner_le_norm (𝕜 := ℂ) y (v + (M : ℂ) • y)
  rw [inner_add_right, inner_smul_right] at hc
  change (inner ℂ y v + (M : ℂ) * inner ℂ y y).re ≤ _ at hc
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hc
  have hsq : (inner ℂ y y).re = ‖y‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  rw [hsq] at hc
  have hnn : ‖y‖ = 0 := by
    have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg y)
    by_contra hne
    have hs : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg y) (Ne.symm hne))
    have ht : 0 < ε * ‖y‖ ^ 2 := mul_pos hε hs
    nlinarith
  exact norm_eq_zero.mp hnn

/-- A bounded spectral interval strictly below zero is null for a nonnegative
coordinate integral. This uses no gap assumption on the entire operator. -/
theorem negative_band_null {E : SpectralMeasure.ProjectionValuedMeasure ℝ H}
    (C : BoundedRealization E)
    (hpos : ∀ x : (measurableIntegral C (fun t : ℝ => (t : ℂ))).domain,
      0 ≤ (inner ℂ (x : H) (measurableIntegral C (fun t : ℝ => (t : ℂ)) x)).re)
    (B : Set ℝ) (hB : MeasurableSet B) (M ε : ℝ)
    (hM : 0 ≤ M) (hε : 0 < ε) (hεM : ε ≤ M)
    (hlo : ∀ t ∈ B, -M ≤ t) (hhi : ∀ t ∈ B, t ≤ -ε) : E B = 0 := by
  let f : ℝ → ℂ := B.indicator (fun t : ℝ => (t : ℂ))
  let k : ℝ → ℂ := B.indicator (fun t : ℝ => ((t + M : ℝ) : ℂ))
  let p : ℝ → ℂ := B.indicator (fun _ : ℝ => (1 : ℂ))
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f := by
    refine ⟨Complex.measurable_ofReal.indicator hB, M, fun t => ?_⟩
    by_cases ht : t ∈ B
    · simp only [f, indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨hlo t ht, (hhi t ht).trans (by linarith)⟩
    · simp [f, ht, hM]
  have hkbound : ∀ t, ‖k t‖ ≤ M - ε := by
    intro t
    by_cases ht : t ∈ B
    · simp only [k, indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith [hlo t ht])]
      linarith [hhi t ht]
    · simp [k, ht, sub_nonneg.mpr hεM]
  have hk : SpectralMeasure.Spec.IsBoundedMeasurable k :=
    ⟨(Complex.measurable_ofReal.comp (measurable_id.add_const M)).indicator hB,
      M - ε, hkbound⟩
  have hp : SpectralMeasure.Spec.IsBoundedMeasurable p :=
    BorelNormSpectrum.bounded_indicator B hB (BorelNormSpectrum.bounded_const 1)
  have hkfun : k = f + (M : ℂ) • p := by
    funext t
    by_cases ht : t ∈ B <;> simp [k, f, p, ht, Complex.ofReal_add]
  have hkp : k * p = k := by
    funext t
    by_cases ht : t ∈ B <;> simp [k, p, ht]
  have hpi : C.integral p = E B := integral_indicator_one C B hB
  have hki : C.integral k = C.integral f + (M : ℂ) • E B := by
    rw [hkfun, C.add f _ hf (hp.smul (M : ℂ)), C.smul (M : ℂ) p hp, hpi]
  have hkq : C.integral k * E B = C.integral k := by
    rw [← hpi, ← C.mul k p hk hp, hkp]
  ext x
  let y := E B x
  obtain ⟨hy, hval⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp
    (localized_graph C Complex.measurable_ofReal hB (M := M)
      (fun t ht => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨hlo t ht, (hhi t ht).trans (by linarith)⟩) x)
  have hval' : measurableIntegral C (fun t : ℝ => (t : ℂ)) ⟨y, hy⟩ = C.integral f x := hval
  have hpos' : 0 ≤ (inner ℂ y (C.integral f x)).re := by
    rw [← hval']
    exact hpos ⟨y, hy⟩
  have hky : C.integral k y = C.integral k x := by
    exact congrArg (fun T : H →L[ℂ] H => T x) hkq
  have hkx : C.integral k x = C.integral f x + (M : ℂ) • y := by
    exact congrArg (fun T : H →L[ℂ] H => T x) hki
  have hn : ‖C.integral k x‖ ≤ (M - ε) * ‖y‖ := by
    rw [← hky]
    exact (C.integral k).le_opNorm y |>.trans
      (mul_le_mul_of_nonneg_right (C.bound k (M - ε) hk
        (sub_nonneg.mpr hεM) hkbound) (norm_nonneg y))
  have hy0 : y = 0 := norm_coercion y (C.integral f x) M ε hε hpos' (by
    rw [← hkx]
    exact hn)
  exact hy0

/-- A nonnegative coordinate integral has no negative spectral mass. -/
theorem negative_halfline_null {E : SpectralMeasure.ProjectionValuedMeasure ℝ H}
    (C : BoundedRealization E)
    (hpos : ∀ x : (measurableIntegral C (fun t : ℝ => (t : ℂ))).domain,
      0 ≤ (inner ℂ (x : H) (measurableIntegral C (fun t : ℝ => (t : ℂ)) x)).re) :
    E (Iio 0) = 0 := by
  let B (n : ℕ) : Set ℝ := Icc (-((n : ℝ) + 1)) (-((n : ℝ) + 1)⁻¹)
  have hnull (n : ℕ) : E (B n) = 0 := by
    apply negative_band_null C hpos (B n) measurableSet_Icc
      ((n : ℝ) + 1) (((n : ℝ) + 1)⁻¹) (by positivity) (by positivity)
    · have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      exact (inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr hn |>.trans hn
    · intro t ht; exact ht.1
    · intro t ht; exact ht.2
  have hcover : Iio (0 : ℝ) ⊆ ⋃ n, B n := by
    intro t ht
    have ha : 0 < -t := neg_pos.mpr ht
    obtain ⟨n, hn⟩ := exists_nat_ge (max (-t) (-t)⁻¹)
    have hlo : -t ≤ (n : ℝ) + 1 := (le_max_left _ _).trans (hn.trans (by linarith))
    have hhi : (-t)⁻¹ ≤ (n : ℝ) + 1 := (le_max_right _ _).trans (hn.trans (by linarith))
    have hinv : ((n : ℝ) + 1)⁻¹ ≤ -t :=
      (inv_le_comm₀ (by positivity : 0 < (n : ℝ) + 1) ha).mpr hhi
    exact mem_iUnion.mpr ⟨n, by constructor <;> linarith⟩
  ext x
  have hm : C.measure x (Iio 0) = 0 := measure_mono_null hcover
    (measure_iUnion_null_iff.mpr (fun n => by
      rw [C.measure_apply x (B n) measurableSet_Icc, hnull n]
      simp))
  rw [C.measure_apply x (Iio 0) measurableSet_Iio] at hm
  have hn : ‖E (Iio 0) x‖ = 0 := by
    have hh := ENNReal.ofReal_eq_zero.mp hm
    nlinarith [norm_nonneg (E (Iio 0) x)]
  exact norm_eq_zero.mp hn

/-- Spectral nonnegativity for any real-base resolution of the actual operator. -/
theorem realResolves_nonnegative_support (N : Operator ℂ H H)
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ H)
    (hE : UnboundedNormalSpectralTheorem.RealResolves N E)
    (hpos : ∀ x : N.domain, 0 ≤ (inner ℂ (x : H) (N x)).re) :
    E (Iio 0) = 0 := by
  obtain ⟨C, hC, _⟩ := hE
  apply negative_halfline_null C
  rw [hC]
  exact hpos

/-- Pushing a PVM along `toNNReal` preserves the coordinate integral once its
negative half-line is null. The zero spectral mode remains at zero. -/
theorem measurableIntegral_toNNReal_of_negative_null
    {E : SpectralMeasure.ProjectionValuedMeasure ℝ H} (C : BoundedRealization E)
    (hneg : E (Iio 0) = 0) :
    measurableIntegral (C.map Real.toNNReal measurable_real_toNNReal)
        (fun s : ℝ≥0 => ((s : ℝ) : ℂ)) =
      measurableIntegral C (fun t : ℝ => (t : ℂ)) := by
  rw [BoundedRealization.measurableIntegral_map]
  apply C.measurableIntegral_congr_ae
    (fun t : ℝ => (((Real.toNNReal t : ℝ≥0) : ℝ) : ℂ))
    (fun t : ℝ => (t : ℂ))
    (Complex.measurable_ofReal.comp
      (measurable_subtype_coe.comp measurable_real_toNNReal)) Complex.measurable_ofReal
  intro x
  have hm : C.measure x (Iio 0) = 0 := by
    rw [C.measure_apply x (Iio 0) measurableSet_Iio, hneg]
    simp
  have hpos : ∀ᵐ t ∂C.measure x, 0 ≤ t := by
    apply ae_iff.mpr
    simpa only [not_le, Iio_def] using hm
  filter_upwards [hpos] with t ht
  rw [Real.coe_toNNReal t ht]

/-- Rebase a nonnegative real-base resolution to the closed nonnegative
half-line, retaining a complete bounded realization and the exact domain. -/
theorem realResolves_nonnegative_rebase (N : Operator ℂ H H)
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ H)
    (hE : UnboundedNormalSpectralTheorem.RealResolves N E)
    (hpos : ∀ x : N.domain, 0 ≤ (inner ℂ (x : H) (N x)).re) :
    ∃ C : BoundedRealization (E.map Real.toNNReal measurable_real_toNNReal),
      measurableIntegral C (fun s : ℝ≥0 => ((s : ℝ) : ℂ)) = N ∧
      ∀ x : H, x ∈ N.domain ↔
        MeasurableSpectralCalculus.SquareIntegrable C
          (fun s : ℝ≥0 => ((s : ℝ) : ℂ)) x := by
  obtain ⟨C, hC, _⟩ := hE
  have hneg : E (Iio 0) = 0 := negative_halfline_null C (by rw [hC]; exact hpos)
  have heq := (measurableIntegral_toNNReal_of_negative_null C hneg).trans hC
  refine ⟨C.map Real.toNNReal measurable_real_toNNReal, heq, ?_⟩
  intro x
  rw [← heq]
  exact measurableIntegral_domain _
    (Complex.measurable_ofReal.comp measurable_subtype_coe) x

end ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus.SupportWork


namespace ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus.ComplexCalculus
open MeasurableSpectralCalculus
universe u v
variable {S : Type u} {K : Type v} [MeasurableSpace S]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : SpectralMeasure.ProjectionValuedMeasure S K}

/-- Quadratic growth of symbols gives inclusion of the maximal domains. -/
theorem domain_growth (C : BoundedRealization E) {f g : S → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (hb : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ s, ‖f s‖ ^ 2 ≤ a + b * ‖g s‖ ^ 2) :
    (measurableIntegral C g).domain ≤ (measurableIntegral C f).domain := by
  intro x hx
  letI := C.finite x
  have hig : Integrable (fun s => ‖g s‖ ^ 2) (C.measure x) := by
    refine ⟨(hg.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun s => sq_nonneg ‖g s‖)).mpr
      (squareIntegrable_of_mem_domain C hg ⟨x, hx⟩)
  obtain ⟨a, b, ha, hb, hbound⟩ := hb
  have hmajor : Integrable (fun s => a + b * ‖g s‖ ^ 2) (C.measure x) :=
    (integrable_const a).add (hig.const_mul b)
  have hif : Integrable (fun s => ‖f s‖ ^ 2) (C.measure x) := by
    apply hmajor.mono' (hf.norm.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f s‖)] using hbound s
  apply (measurableIntegral_domain C hf x).mpr
  exact (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun s => sq_nonneg ‖f s‖)).mp hif.hasFiniteIntegral

end ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus.ComplexCalculus

namespace ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus.PositivityWork
open SpectralMeasure MeasurableSpectralCalculus
universe u v
variable {S : Type u} [MeasurableSpace S]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positivity of a bounded real nonnegative spectral symbol follows by
factoring its bounded square root. -/
theorem bounded_integral_nonnegative
    {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)
    {f : S → ℂ} (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (hreal : ∀ s, (f s).im = 0) (hpos : ∀ s, 0 ≤ (f s).re) (x : H) :
    0 ≤ (inner ℂ x (C.integral f x)).re := by
  let g : S → ℂ := fun s => (Real.sqrt (f s).re : ℂ)
  obtain ⟨M, hM, hb⟩ := hf.nonneg_bound
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g := by
    refine ⟨Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (Complex.measurable_re.comp hf.1)), Real.sqrt M, fun s => ?_⟩
    simp only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((Complex.re_le_norm (f s)).trans (hb s))
  have hgg : g * g = f := by
    funext s
    apply Complex.ext
    · change Real.sqrt (f s).re * Real.sqrt (f s).re - 0 * 0 = (f s).re
      rw [mul_zero, sub_zero, ← pow_two, Real.sq_sqrt (hpos s)]
    · change Real.sqrt (f s).re * 0 + 0 * Real.sqrt (f s).re = (f s).im
      simp [hreal s]
  have hgs : star g = g := by
    funext s
    apply Complex.ext <;> simp [g]
  have hsa : (C.integral g).adjoint = C.integral g := by
    change star (C.integral g) = C.integral g
    rw [← C.map_star g hg, hgs]
  rw [← hgg, C.mul g g hg hg]
  change 0 ≤ (inner ℂ x (C.integral g (C.integral g x))).re
  have hi := (C.integral g).adjoint_inner_right x (C.integral g x)
  rw [hsa] at hi
  rw [hi]
  exact inner_self_nonneg (𝕜 := ℂ) (x := C.integral g x)

/-- Positivity passes from the bounded real truncations to the actual maximal
domain integral by norm convergence of the truncations. -/
theorem measurableIntegral_nonnegative
    {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)
    {f : S → ℂ} (hf : Measurable f)
    (hreal : ∀ s, (f s).im = 0) (hpos : ∀ s, 0 ≤ (f s).re)
    (x : (measurableIntegral C f).domain) :
    0 ≤ (inner ℂ (x : H) (measurableIntegral C f x)).re := by
  have hn (n : ℕ) : 0 ≤ (inner ℂ (x : H) (C.integral (MeasurableSpectralCalculus.truncation f n) x)).re := by
    apply bounded_integral_nonnegative C (boundedMeasurable_truncation hf n)
    · intro s
      by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [MeasurableSpectralCalculus.truncation, hs, hreal s]
    · intro s
      by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [MeasurableSpectralCalculus.truncation, hs, hpos s]
  have ht := measurableIntegral_tendsto C f x
  have hi : Tendsto
      (fun n => inner ℂ (x : H) (C.integral (MeasurableSpectralCalculus.truncation f n) x)) atTop
      (𝓝 (inner ℂ (x : H) (measurableIntegral C f x))) :=
    ((continuous_const.inner continuous_id).tendsto _).comp ht
  have hir := (Complex.continuous_re.tendsto _).comp hi
  exact ge_of_tendsto hir (Eventually.of_forall hn)

end ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus.PositivityWork




namespace ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
universe u

/-- External complexification. A fresh type prevents the sup product norm
from being confused with the Hilbert sum norm constructed below. -/
def Complexification (H : Type u) := H × H

namespace Complexification
variable {H : Type u}

def re (z : Complexification H) : H := z.1
def im (z : Complexification H) : H := z.2
def mk (x y : H) : Complexification H := (x, y)

@[ext] theorem ext {z w : Complexification H} (hr : z.re = w.re) (hi : z.im = w.im) :
    z = w := Prod.ext hr hi
@[simp] theorem re_mk (x y : H) : (mk x y).re = x := rfl
@[simp] theorem im_mk (x y : H) : (mk x y).im = y := rfl
variable [NormedAddCommGroup H]
instance : AddCommGroup (Complexification H) := inferInstanceAs (AddCommGroup (H × H))

@[simp] theorem re_add (z w : Complexification H) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : Complexification H) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_zero : (0 : Complexification H).re = 0 := rfl
@[simp] theorem im_zero : (0 : Complexification H).im = 0 := rfl
@[simp] theorem re_neg (z : Complexification H) : (-z).re = -z.re := rfl
@[simp] theorem im_neg (z : Complexification H) : (-z).im = -z.im := rfl

variable [InnerProductSpace ℝ H]

instance : SMul ℂ (Complexification H) :=
  ⟨fun a z => mk (a.re • z.re - a.im • z.im) (a.im • z.re + a.re • z.im)⟩

@[simp] theorem re_smul (a : ℂ) (z : Complexification H) :
    (a • z).re = a.re • z.re - a.im • z.im := rfl
@[simp] theorem im_smul (a : ℂ) (z : Complexification H) :
    (a • z).im = a.im • z.re + a.re • z.im := rfl

instance : Module ℂ (Complexification H) where
  one_smul z := by ext <;> simp
  mul_smul a b z := by
    ext <;> simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero a := by ext <;> simp
  smul_add a z w := by ext <;> simp only [re_smul, im_smul, re_add, im_add] <;> module
  add_smul a b z := by
    ext <;> simp only [re_smul, im_smul, re_add, im_add, Complex.add_re, Complex.add_im] <;> module
  zero_smul z := by ext <;> simp

/-- Conjugate-linear first, as in the manuscript. -/
def innerValue (z w : Complexification H) : ℂ :=
  ⟨inner ℝ z.re w.re + inner ℝ z.im w.im,
    inner ℝ z.re w.im - inner ℝ z.im w.re⟩

@[instance_reducible] def innerCore : InnerProductSpace.Core ℂ (Complexification H) where
  inner := innerValue
  conj_inner_symm z w := by
    apply Complex.ext <;> simp only [innerValue, Complex.conj_re, Complex.conj_im]
    · rw [real_inner_comm w.re z.re, real_inner_comm w.im z.im]
    · rw [real_inner_comm w.re z.im, real_inner_comm w.im z.re]; ring
  re_inner_nonneg z := add_nonneg (real_inner_self_nonneg) (real_inner_self_nonneg)
  add_left z w v := by
    apply Complex.ext <;> simp only [innerValue, re_add, im_add, inner_add_left,
      Complex.add_re, Complex.add_im] <;> ring
  smul_left z w a := by
    apply Complex.ext <;> simp only [innerValue, re_smul, im_smul,
      inner_sub_left, inner_add_left, real_inner_smul_left, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im] <;> ring
  definite z hz := by
    have h := congrArg Complex.re hz
    change inner ℝ z.re z.re + inner ℝ z.im z.im = 0 at h
    obtain ⟨hr, hi⟩ := (add_eq_zero_iff_of_nonneg real_inner_self_nonneg
      real_inner_self_nonneg).mp h
    ext <;> simpa only [re_zero, im_zero] using (inner_self_eq_zero.mp ‹_›)

instance : NormedAddCommGroup (Complexification H) := innerCore.toNormedAddCommGroup
instance : InnerProductSpace ℂ (Complexification H) := .ofCore { innerCore with }

@[simp] theorem inner_eq (z w : Complexification H) :
    inner ℂ z w = innerValue z w := rfl

theorem norm_sq (z : Complexification H) : ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change inner ℝ z.re z.re + inner ℝ z.im z.im = _
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The underlying real Hilbert space is the L² product. -/
def realEquiv : Complexification H ≃ₗᵢ[ℝ] WithLp 2 (H × H) where
  toFun z := WithLp.toLp 2 (z.re, z.im)
  invFun z := mk z.fst z.snd
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · change ((a : ℂ) • z).re = a • z.re
      simp only [re_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
    · change ((a : ℂ) • z).im = a • z.im
      simp only [im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, norm_sq]
    rfl

instance [CompleteSpace H] : CompleteSpace (Complexification H) :=
  realEquiv.toIsometryEquiv.completeSpace_iff.mpr inferInstance

/-- Coordinate homeomorphism; the target has its usual product topology. -/
def coordinates : Complexification H ≃L[ℝ] H × H :=
  realEquiv.toContinuousLinearEquiv.trans (WithLp.prodContinuousLinearEquiv 2 ℝ H H)

@[simp] theorem re_real_smul (a : ℝ) (z : Complexification H) :
    (a • z).re = a • z.re := by
  change ((a : ℂ) • z).re = _
  simp only [re_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
@[simp] theorem im_real_smul (a : ℝ) (z : Complexification H) :
    (a • z).im = a • z.im := by
  change ((a : ℂ) • z).im = _
  simp only [im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

theorem norm_re_le (z : Complexification H) : ‖z.re‖ ≤ ‖z‖ := by
  have h := norm_sq z
  nlinarith [norm_nonneg z, norm_nonneg z.re, sq_nonneg ‖z.im‖]
theorem norm_im_le (z : Complexification H) : ‖z.im‖ ≤ ‖z‖ := by
  have h := norm_sq z
  nlinarith [norm_nonneg z, norm_nonneg z.im, sq_nonneg ‖z.re‖]

/-- The canonical real isometric embedding. -/
def embedding : H →ₗᵢ[ℝ] Complexification H where
  toFun x := mk x 0
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖mk x 0‖ ^ 2 = ‖x‖ ^ 2
    simp only [norm_sq, re_mk, im_mk, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

@[simp] theorem embedding_re (x : H) : (embedding x).re = x := rfl
@[simp] theorem embedding_im (x : H) : (embedding x).im = 0 := rfl

/-- Natural conjugation of the external complexification. -/
def conjugation : Complexification H ≃ₗᵢ⋆[ℂ] Complexification H where
  toFun z := mk z.re (-z.im)
  invFun z := mk z.re (-z.im)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp only [re_mk, im_mk, re_add, im_add] <;> module
  map_smul' a z := by
    ext
    · change a.re • z.re - a.im • z.im =
        (starRingEnd ℂ a).re • z.re - (starRingEnd ℂ a).im • (-z.im)
      change a.re • z.re - a.im • z.im = a.re • z.re - (-a.im) • (-z.im)
      module
    · change -(a.im • z.re + a.re • z.im) =
        (starRingEnd ℂ a).im • z.re + (starRingEnd ℂ a).re • (-z.im)
      change -(a.im • z.re + a.re • z.im) = (-a.im) • z.re + a.re • (-z.im)
      module
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖mk z.re (-z.im)‖ ^ 2 = ‖z‖ ^ 2
    simp only [norm_sq, re_mk, im_mk, norm_neg]

@[simp] theorem conjugation_re (z : Complexification H) : (conjugation z).re = z.re := rfl
@[simp] theorem conjugation_im (z : Complexification H) : (conjugation z).im = -z.im := rfl
@[simp] theorem conjugation_conjugation (z : Complexification H) :
    conjugation (conjugation z) = z := by ext <;> simp
@[simp] theorem conjugation_embedding (x : H) : conjugation (embedding x) = embedding x := by
  ext <;> simp

theorem conjugation_eq_self_iff (z : Complexification H) : conjugation z = z ↔ z.im = 0 := by
  constructor
  · intro h
    have hh : -z.im = z.im := congrArg im h
    have hn : (2 : ℝ) • z.im = 0 := by rw [two_smul]; exact neg_eq_iff_add_eq_zero.mp hh
    exact (smul_eq_zero.mp hn).resolve_left (by norm_num)
  · intro h
    ext <;> simp [h]

theorem embedding_re_eq_iff (z : Complexification H) : embedding z.re = z ↔ z.im = 0 := by
  constructor
  · intro h
    exact (congrArg im h).symm
  · intro h
    ext <;> simp [h]

theorem decomposition (z : Complexification H) :
    embedding z.re + Complex.I • embedding z.im = z := by
  ext <;> simp

/-- The real restriction of a bounded complex operator. For operators commuting
with conjugation this is restriction to the conjugation-fixed vectors. -/
def restrictBounded (B : Complexification H →L[ℂ] Complexification H) : H →L[ℝ] H :=
  { toFun := fun x => (B (embedding x)).re
    map_add' x y := by simp
    map_smul' a x := by
      rw [embedding.map_smul]
      change (B ((a : ℂ) • embedding x)).re = a • (B (embedding x)).re
      rw [B.map_smul]
      exact re_real_smul a _
    cont := (continuous_fst.comp coordinates.continuous).comp
      (B.continuous.comp embedding.continuous) }

@[simp] theorem restrictBounded_apply (B : Complexification H →L[ℂ] Complexification H)
    (x : H) : restrictBounded B x = (B (embedding x)).re := rfl

theorem restrictBounded_norm_le (B : Complexification H →L[ℂ] Complexification H) :
    ‖restrictBounded B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (restrictBounded B) (norm_nonneg B)
  intro x
  exact (norm_re_le _).trans (by simpa only [embedding.norm_map] using B.le_opNorm (embedding x))

theorem restrictBounded_embedding (B : Complexification H →L[ℂ] Complexification H)
    (hB : ∀ z, B (conjugation z) = conjugation (B z)) (x : H) :
    embedding (restrictBounded B x) = B (embedding x) := by
  apply (embedding_re_eq_iff _).mpr
  apply (conjugation_eq_self_iff _).mp
  rw [← hB, conjugation_embedding]

theorem restrictBounded_one : restrictBounded (1 : Complexification H →L[ℂ] Complexification H) = 1 := by
  ext x
  rfl

theorem restrictBounded_add (B D : Complexification H →L[ℂ] Complexification H) :
    restrictBounded (B + D) = restrictBounded B + restrictBounded D := by
  ext x
  rfl

theorem restrictBounded_real_smul (a : ℝ)
    (B : Complexification H →L[ℂ] Complexification H) :
    restrictBounded (a • B) = a • restrictBounded B := by
  ext x
  exact re_real_smul a _

theorem restrictBounded_mul (B D : Complexification H →L[ℂ] Complexification H)
    (hD : ∀ z, D (conjugation z) = conjugation (D z)) :
    restrictBounded (B * D) = restrictBounded B * restrictBounded D := by
  ext x
  change (B (D (embedding x))).re = (B (embedding (restrictBounded D x))).re
  rw [restrictBounded_embedding D hD]

@[simp] theorem inner_embedding_left (x : H) (z : Complexification H) :
    (inner ℂ (embedding x) z).re = inner ℝ x z.re := by
  change inner ℝ x z.re + inner ℝ 0 z.im = _
  simp
@[simp] theorem inner_embedding_right (z : Complexification H) (x : H) :
    (inner ℂ z (embedding x)).re = inner ℝ z.re x := by
  change inner ℝ z.re x + inner ℝ z.im 0 = _
  simp

/-- Real compression respects adjoints, even before imposing conjugation
invariance. Conjugation invariance is needed for multiplicativity. -/
theorem restrictBounded_adjoint [CompleteSpace H]
    (B : Complexification H →L[ℂ] Complexification H) :
    ContinuousLinearMap.adjoint (restrictBounded B) =
      restrictBounded (ContinuousLinearMap.adjoint B) := by
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (B (embedding x)).re y =
    inner ℝ x ((ContinuousLinearMap.adjoint B) (embedding y)).re
  rw [← inner_embedding_right, ← inner_embedding_left,
    ContinuousLinearMap.adjoint_inner_right]

theorem restrictBounded_selfAdjoint [CompleteSpace H]
    (B : Complexification H →L[ℂ] Complexification H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (restrictBounded B) := by
  change ContinuousLinearMap.adjoint (restrictBounded B) = restrictBounded B
  rw [restrictBounded_adjoint, (ContinuousLinearMap.isSelfAdjoint_iff'.mp hB)]

/-- Restriction of a conjugation-invariant PVM. This is a construction from an
actual complex PVM, not an existence assertion for the operator under study. -/
def restrictPVM [CompleteSpace H]
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z)) :
    ProjectionValuedMeasure H where
  toFun B := restrictBounded (E B)
  univ := by rw [E.univ, restrictBounded_one]
  selfAdjoint B hB := restrictBounded_selfAdjoint _ (E.selfAdjoint B hB)
  inter B D hB hD := by
    rw [← restrictBounded_mul _ _ (hE D hD), E.inter B D hB hD]
  iUnion B hB hdis x := by
    have hh := (E.iUnion B hB hdis (embedding x)).mapL
      ((ContinuousLinearMap.fst ℝ H H).comp coordinates.toContinuousLinearMap)
    exact hh

@[simp] theorem re_sub (z w : Complexification H) : (z - w).re = z.re - w.re := rfl
@[simp] theorem im_sub (z w : Complexification H) : (z - w).im = z.im - w.im := rfl

theorem embedding_re_formula (z : Complexification H) :
    embedding z.re = (2 : ℝ)⁻¹ • (z + conjugation z) := by
  ext <;> simp only [embedding_re, embedding_im, re_real_smul, im_real_smul,
    re_add, im_add, conjugation_re, conjugation_im] <;> module

theorem embedding_im_formula (z : Complexification H) :
    embedding z.im = (2 : ℝ)⁻¹ • (-Complex.I • (z - conjugation z)) := by
  ext <;> simp only [embedding_re, embedding_im, re_real_smul, im_real_smul,
    re_smul, im_smul, re_sub, im_sub, conjugation_re, conjugation_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] <;> module

/-- Invariance of the whole graph, including its domain, under conjugation. -/
def ConjugationInvariant (B : Operator ℂ (Complexification H) (Complexification H)) : Prop :=
  ∀ z : B.domain, (conjugation (z : Complexification H), conjugation (B z)) ∈ B.graph

/-- Real vectors in the exact complex domain form the restriction domain. -/
def restrictionDomain (B : Operator ℂ (Complexification H) (Complexification H)) : Submodule ℝ H where
  carrier := {x | embedding x ∈ B.domain}
  zero_mem' := by
    change embedding (0 : H) ∈ B.domain
    rw [embedding.map_zero]
    exact B.domain.zero_mem
  add_mem' {x y} hx hy := by
    change embedding (x + y) ∈ B.domain
    rw [embedding.map_add]
    exact B.domain.add_mem hx hy
  smul_mem' a x hx := by
    change embedding (a • x) ∈ B.domain
    rw [embedding.map_smul]
    exact B.domain.smul_mem (a : ℂ) hx

def restrictOperator (B : Operator ℂ (Complexification H) (Complexification H)) : Operator ℝ H H where
  domain := restrictionDomain B
  toFun :=
    { toFun := fun x => (B ⟨embedding x, x.property⟩).re
      map_add' x y := by
        have he : (⟨embedding (x + y), (x + y).property⟩ : B.domain) =
            (⟨embedding x, x.property⟩ : B.domain) + ⟨embedding y, y.property⟩ :=
          Subtype.ext (embedding.map_add (x : H) (y : H))
        change (B ⟨embedding (x + y), (x + y).property⟩).re = _
        rw [he, B.map_add, re_add]
      map_smul' a x := by
        have he : (⟨embedding (a • x), (a • x).property⟩ : B.domain) =
            (a : ℂ) • (⟨embedding x, x.property⟩ : B.domain) :=
          Subtype.ext (embedding.map_smul a (x : H))
        change (B ⟨embedding (a • x), (a • x).property⟩).re = _
        rw [he, B.map_smul]
        exact re_real_smul a _ }

theorem restrictOperator_embedding
    (B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) (x : (restrictOperator B).domain) :
    embedding (restrictOperator B x) = B ⟨embedding x, x.property⟩ := by
  apply (embedding_re_eq_iff _).mpr
  apply (conjugation_eq_self_iff _).mp
  have hh := hB ⟨embedding x, x.property⟩
  rw [conjugation_embedding] at hh
  obtain ⟨hy, he⟩ := (ExpandedFA.Unbounded.mem_graph_iff B _).mp hh
  exact he.symm

theorem restrictionDomain_re_im
    (B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) (z : B.domain) :
    z.val.re ∈ restrictionDomain B ∧ z.val.im ∈ restrictionDomain B := by
  obtain ⟨hzJ, _⟩ := (ExpandedFA.Unbounded.mem_graph_iff B _).mp (hB z)
  constructor
  · change embedding z.val.re ∈ B.domain
    rw [embedding_re_formula]
    exact B.domain.smul_mem (Complex.ofReal ((2 : ℝ)⁻¹)) (B.domain.add_mem z.property hzJ)
  · change embedding z.val.im ∈ B.domain
    rw [embedding_im_formula]
    exact B.domain.smul_mem (Complex.ofReal ((2 : ℝ)⁻¹))
      (B.domain.smul_mem (-Complex.I) (B.domain.sub_mem z.property hzJ))

/-- Complex span of a real subspace, with both coordinates in that subspace. -/
def submodule (D : Submodule ℝ H) : Submodule ℂ (Complexification H) where
  carrier := {z | z.re ∈ D ∧ z.im ∈ D}
  zero_mem' := ⟨D.zero_mem, D.zero_mem⟩
  add_mem' hz hw := ⟨D.add_mem hz.1 hw.1, D.add_mem hz.2 hw.2⟩
  smul_mem' a _z hz := ⟨D.sub_mem (D.smul_mem a.re hz.1) (D.smul_mem a.im hz.2),
    D.add_mem (D.smul_mem a.im hz.1) (D.smul_mem a.re hz.2)⟩

@[simp] theorem mem_submodule (D : Submodule ℝ H) (z : Complexification H) :
    z ∈ submodule D ↔ z.re ∈ D ∧ z.im ∈ D := Iff.rfl

theorem dense_submodule (D : Submodule ℝ H) (hD : Dense (D : Set H)) :
    Dense (submodule D : Set (Complexification H)) := by
  have hh := coordinates.symm.surjective.denseRange.dense_image
    coordinates.symm.continuous (hD.prod hD)
  convert hh using 1
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), hz, rfl⟩
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    exact hxy

/-- Coordinatewise extension of a domain-carrying real linear operator. -/
def operator (A : Operator ℝ H H) : Operator ℂ (Complexification H) (Complexification H) where
  domain := submodule A.domain
  toFun :=
    { toFun := fun z => mk (A ⟨z.val.re, z.property.1⟩) (A ⟨z.val.im, z.property.2⟩)
      map_add' z w := by
        ext
        · exact A.map_add ⟨z.val.re, z.property.1⟩ ⟨w.val.re, w.property.1⟩
        · exact A.map_add ⟨z.val.im, z.property.2⟩ ⟨w.val.im, w.property.2⟩
      map_smul' a z := by
        ext
        · change A (a.re • (⟨z.val.re, z.property.1⟩ : A.domain) -
              a.im • ⟨z.val.im, z.property.2⟩) = _
          rw [A.map_sub, A.map_smul, A.map_smul]
          rfl
        · change A (a.im • (⟨z.val.re, z.property.1⟩ : A.domain) +
              a.re • ⟨z.val.im, z.property.2⟩) = _
          rw [A.map_add, A.map_smul, A.map_smul]
          rfl }

@[simp] theorem operator_re (A : Operator ℝ H H) (z : (operator A).domain) :
    (operator A z).re = A ⟨z.val.re, z.property.1⟩ := rfl
@[simp] theorem operator_im (A : Operator ℝ H H) (z : (operator A).domain) :
    (operator A z).im = A ⟨z.val.im, z.property.2⟩ := rfl

theorem dense_operator (A : Operator ℝ H H) (hA : Dense (A.domain : Set H)) :
    Dense ((operator A).domain : Set (Complexification H)) := dense_submodule _ hA

theorem mem_operator_graph (A : Operator ℝ H H) (y z : Complexification H) :
    (y, z) ∈ (operator A).graph ↔
      (y.re, z.re) ∈ A.graph ∧ (y.im, z.im) ∈ A.graph := by
  constructor
  · intro h
    obtain ⟨hy, h⟩ := (ExpandedFA.Unbounded.mem_graph_iff (operator A) (y, z)).mp h
    exact ⟨(ExpandedFA.Unbounded.mem_graph_iff A (y.re, z.re)).mpr ⟨hy.1, congrArg re h⟩,
      (ExpandedFA.Unbounded.mem_graph_iff A (y.im, z.im)).mpr ⟨hy.2, congrArg im h⟩⟩
  · rintro ⟨hr, hi⟩
    obtain ⟨hr, heR⟩ := (ExpandedFA.Unbounded.mem_graph_iff A (y.re, z.re)).mp hr
    obtain ⟨hi, heI⟩ := (ExpandedFA.Unbounded.mem_graph_iff A (y.im, z.im)).mp hi
    exact (ExpandedFA.Unbounded.mem_graph_iff (operator A) (y, z)).mpr
      ⟨⟨hr, hi⟩, ext heR heI⟩

/-- Testing on real vectors suffices to recover both adjoint coordinate identities. -/
theorem adjoint_pairing_iff (A : Operator ℝ H H) (y z : Complexification H) :
    (∀ x : (operator A).domain,
      inner ℂ (operator A x) y = inner ℂ (x : Complexification H) z) ↔
    (∀ x : A.domain, inner ℝ (A x) y.re = inner ℝ (x : H) z.re) ∧
    (∀ x : A.domain, inner ℝ (A x) y.im = inner ℝ (x : H) z.im) := by
  constructor
  · intro h
    have hh (x : A.domain) := h ⟨mk x 0, x.property, A.domain.zero_mem⟩
    have hzero : A ⟨0, A.domain.zero_mem⟩ = 0 := A.map_zero
    constructor
    · intro x
      simpa only [inner_eq, innerValue, operator_re, operator_im, re_mk, im_mk,
        hzero, inner_zero_left, add_zero] using congrArg Complex.re (hh x)
    · intro x
      simpa only [inner_eq, innerValue, operator_re, operator_im, re_mk, im_mk,
        hzero, inner_zero_left, sub_zero] using congrArg Complex.im (hh x)
  · rintro ⟨hr, hi⟩ x
    apply Complex.ext
    · change inner ℝ (A _) y.re + inner ℝ (A _) y.im = _
      rw [hr, hi]
      rfl
    · change inner ℝ (A _) y.im - inner ℝ (A _) y.re = _
      rw [hi, hr]
      rfl

/-- Exact adjoint identity, including the full adjoint domain. -/
theorem operator_adjoint [CompleteSpace H] (A : Operator ℝ H H)
    (hA : Dense (A.domain : Set H)) : (operator A).adjoint = operator A.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨y, z⟩
  change (y, z) ∈ (hilbertAdjoint (operator A)).graph ↔ _
  rw [mem_hilbertAdjoint_graph_iff _ (dense_operator A hA), adjoint_pairing_iff,
    mem_operator_graph]
  change _ ↔ (y.re, z.re) ∈ (hilbertAdjoint A).graph ∧
    (y.im, z.im) ∈ (hilbertAdjoint A).graph
  rw [mem_hilbertAdjoint_graph_iff A hA, mem_hilbertAdjoint_graph_iff A hA]

theorem operator_selfAdjoint [CompleteSpace H] (A : Operator ℝ H H)
    (hA : Dense (A.domain : Set H)) (hself : A.adjoint = A) :
    (operator A).adjoint = operator A := by rw [operator_adjoint A hA, hself]

/-- Nonnegativity transfers without a gap or an injectivity assumption. -/
theorem operator_nonnegative (A : Operator ℝ H H)
    (hA : ∀ x : A.domain, 0 ≤ inner ℝ (x : H) (A x))
    (z : (operator A).domain) :
    0 ≤ (inner ℂ (z : Complexification H) (operator A z)).re :=
  add_nonneg (hA ⟨z.val.re, z.property.1⟩) (hA ⟨z.val.im, z.property.2⟩)

theorem operator_conjugation_mem (A : Operator ℝ H H) (z : (operator A).domain) :
    conjugation (z : Complexification H) ∈ (operator A).domain :=
  ⟨z.property.1, A.domain.neg_mem z.property.2⟩

theorem operator_conjugation (A : Operator ℝ H H) (z : (operator A).domain) :
    operator A ⟨conjugation z, operator_conjugation_mem A z⟩ = conjugation (operator A z) := by
  ext
  · rfl
  · change A (- (⟨z.val.im, z.property.2⟩ : A.domain)) = - A _
    exact A.map_neg _

theorem operator_restrictOperator
    (B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) : operator (restrictOperator B) = B := by
  have hdom : (operator (restrictOperator B)).domain = B.domain := by
    ext z
    constructor
    · intro hz
      have hh := B.domain.add_mem hz.1 (B.domain.smul_mem Complex.I hz.2)
      simpa only [decomposition] using hh
    · intro hz
      exact restrictionDomain_re_im B hB ⟨z, hz⟩
  apply (LinearPMap.ext_iff).mpr
  refine ⟨hdom, ?_⟩
  intro z hz hw
  have hr : z.re ∈ (restrictOperator B).domain := hz.1
  have hi : z.im ∈ (restrictOperator B).domain := hz.2
  calc
    operator (restrictOperator B) ⟨z, hz⟩ =
        embedding (restrictOperator B ⟨z.re, hr⟩) +
          Complex.I • embedding (restrictOperator B ⟨z.im, hi⟩) := by
      simpa only [operator_re, operator_im] using (decomposition
        (operator (restrictOperator B) ⟨z, hz⟩)).symm
    _ = B ⟨embedding z.re, hr⟩ + Complex.I • B ⟨embedding z.im, hi⟩ := by
      rw [restrictOperator_embedding B hB ⟨z.re, hr⟩,
        restrictOperator_embedding B hB ⟨z.im, hi⟩]
    _ = B ((⟨embedding z.re, hr⟩ : B.domain) +
        Complex.I • ⟨embedding z.im, hi⟩) := by rw [B.map_add, B.map_smul]
    _ = B ⟨z, hw⟩ := by congr 1; exact Subtype.ext (decomposition z)

/-- The complexification functor is faithful on domain-carrying operators. -/
theorem operator_injective : Function.Injective (operator (H := H)) := by
  intro A B hab
  apply LinearPMap.eq_of_eq_graph
  ext ⟨y, z⟩
  have hh := congrArg (fun T => (embedding y, embedding z) ∈ T.graph) hab
  simp only [mem_operator_graph, embedding_re, embedding_im] at hh
  simpa using Iff.of_eq hh

theorem dense_restrictOperator
    (B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) (hd : Dense (B.domain : Set (Complexification H))) :
    Dense ((restrictOperator B).domain : Set H) := by
  let reL : Complexification H →L[ℝ] H :=
    (ContinuousLinearMap.fst ℝ H H).comp coordinates.toContinuousLinearMap
  have hs : Function.Surjective reL := fun x => ⟨embedding x, rfl⟩
  apply (hs.denseRange.dense_image reL.continuous hd).mono
  rintro x ⟨z, hz, rfl⟩
  exact (restrictionDomain_re_im B hB ⟨z, hz⟩).1

theorem restrictOperator_selfAdjoint [CompleteSpace H]
    (B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) (hd : Dense (B.domain : Set (Complexification H)))
    (hself : B.adjoint = B) : (restrictOperator B).adjoint = restrictOperator B := by
  apply operator_injective
  rw [← operator_adjoint _ (dense_restrictOperator B hB hd),
    operator_restrictOperator B hB, hself]

/-- Restriction has exactly the graph cut out by the real embedding. -/
theorem mem_restrictOperator_graph
    (B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) (x y : H) :
    (x, y) ∈ (restrictOperator B).graph ↔
      (embedding x, embedding y) ∈ B.graph := by
  constructor
  · intro h
    obtain ⟨hx, he⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp h
    exact (ExpandedFA.Unbounded.mem_graph_iff B _).mpr
      ⟨hx, (restrictOperator_embedding B hB ⟨x, hx⟩).symm.trans
        (congrArg embedding he)⟩
  · intro h
    obtain ⟨hx, he⟩ := (ExpandedFA.Unbounded.mem_graph_iff B _).mp h
    exact (ExpandedFA.Unbounded.mem_graph_iff _ _).mpr ⟨hx, congrArg re he⟩

/-- The real graph is a continuous preimage of the complex graph. -/
theorem restrictOperator_isClosed
    (B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) (hc : B.IsClosed) :
    (restrictOperator B).IsClosed := by
  change _root_.IsClosed ((restrictOperator B).graph : Set (H × H))
  have he : ((restrictOperator B).graph : Set (H × H)) =
      (fun p : H × H => (embedding p.1, embedding p.2)) ⁻¹'
        (B.graph : Set (Complexification H × Complexification H)) := by
    ext p
    exact mem_restrictOperator_graph B hB p.1 p.2
  rw [he]
  exact hc.preimage ((embedding.continuous.comp continuous_fst).prodMk
    (embedding.continuous.comp continuous_snd))

/-- Extension followed by restriction recovers the original domain as well as
the original values. -/
theorem restrictOperator_operator (A : Operator ℝ H H) :
    restrictOperator (operator A) = A := by
  apply (LinearPMap.ext_iff).mpr
  constructor
  · ext x
    change (x ∈ A.domain ∧ (0 : H) ∈ A.domain) ↔ x ∈ A.domain
    exact and_iff_left A.domain.zero_mem
  · intro x hx hy
    rfl

theorem restrictOperator_mono
    {A B : Operator ℂ (Complexification H) (Complexification H)} (h : A ≤ B) :
    restrictOperator A ≤ restrictOperator B := by
  refine ⟨fun _ hx => h.1 hx, ?_⟩
  intro x y hxy
  change (A ⟨embedding x, x.property⟩).re = (B ⟨embedding y, y.property⟩).re
  exact congrArg re (h.2 (congrArg embedding hxy))

/-- A bounded operator's real restriction still has its full domain. -/
theorem restrictOperator_bounded
    (B : Complexification H →L[ℂ] Complexification H) :
    restrictOperator (B.toLinearMap.toPMap ⊤) =
      (restrictBounded B).toLinearMap.toPMap ⊤ := by
  apply (LinearPMap.ext_iff).mpr
  exact ⟨by ext; simp [restrictOperator, restrictionDomain], fun _ _ _ => rfl⟩

/-- Restriction respects exact products when the second factor preserves real
vectors. In particular no product domain is enlarged by this operation. -/
theorem restrictOperator_product
    (A B : Operator ℂ (Complexification H) (Complexification H))
    (hB : ConjugationInvariant B) :
    restrictOperator (OperatorDomainsSpec.productValue A B) =
      OperatorDomainsSpec.productValue (restrictOperator A) (restrictOperator B) := by
  apply (LinearPMap.ext_iff).mpr
  constructor
  · ext x
    change (∃ hx : embedding x ∈ B.domain, B ⟨embedding x, hx⟩ ∈ A.domain) ↔
      ∃ hx : embedding x ∈ B.domain,
        embedding (restrictOperator B ⟨x, hx⟩) ∈ A.domain
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, by rw [restrictOperator_embedding B hB]; exact hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, by rw [restrictOperator_embedding B hB] at hy; exact hy⟩
  · intro x hx hy
    change (A ⟨B ⟨embedding x, hx.choose⟩, hx.choose_spec⟩).re =
      (A ⟨embedding ((B ⟨embedding x, hy.choose⟩).re), hy.choose_spec⟩).re
    congr 2
    apply Subtype.ext
    exact (restrictOperator_embedding B hB ⟨x, hy.choose⟩).symm

variable [CompleteSpace H]

@[simp] theorem inner_conjugation (x y : Complexification H) :
    inner ℂ (conjugation x) (conjugation y) = star (inner ℂ x y) := by
  apply Complex.ext <;> simp [inner_eq, innerValue] <;> ring

def reflectOperator (T : Complexification H →L[ℂ] Complexification H) :
    Complexification H →L[ℂ] Complexification H :=
  (conjugation.toContinuousLinearEquiv.arrowCongrSL conjugation.toContinuousLinearEquiv) T

@[simp] theorem reflectOperator_apply (T : Complexification H →L[ℂ] Complexification H)
    (x : Complexification H) : reflectOperator T x = conjugation (T (conjugation x)) := rfl

theorem reflectOperator_selfAdjoint (T : Complexification H →L[ℂ] Complexification H)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (reflectOperator T) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (conjugation (T (conjugation x))) y =
    inner ℂ x (conjugation (T (conjugation y)))
  rw [← conjugation_conjugation y, inner_conjugation,
    ← conjugation_conjugation x, inner_conjugation]
  simp only [conjugation_conjugation]
  have hh := hT.isSymmetric (conjugation x) (conjugation y)
  change inner ℂ (T (conjugation x)) (conjugation y) = inner ℂ (conjugation x) (T (conjugation y)) at hh
  exact congrArg star hh

open SpectralMeasure
variable {S : Type*} [MeasurableSpace S]

def antiConjugate (E : SpectralMeasure.ProjectionValuedMeasure S (Complexification H)) :
    SpectralMeasure.ProjectionValuedMeasure S (Complexification H) where
  toFun B := reflectOperator (E B)
  univ := by
    change reflectOperator (E univ) = 1
    rw [E.univ]
    apply ContinuousLinearMap.ext
    intro x
    exact conjugation_conjugation x
  selfAdjoint B hB := reflectOperator_selfAdjoint (E B) (E.selfAdjoint B hB)
  inter B C hB hC := by
    apply ContinuousLinearMap.ext
    intro x
    change conjugation (E B (conjugation (conjugation (E C (conjugation x))))) = _
    rw [conjugation_conjugation]
    exact congrArg conjugation (congrArg (fun T : Complexification H →L[ℂ] Complexification H => T (conjugation x)) (E.inter B C hB hC))
  iUnion B hB hd x := by
    change HasSum (fun n => conjugation (E (B n) (conjugation x))) (conjugation (E (⋃ n, B n) (conjugation x)))
    exact (E.iUnion B hB hd (conjugation x)).map
      conjugation.toContinuousLinearEquiv.toContinuousLinearMap conjugation.continuous

@[simp] theorem antiConjugate_apply
    (E : SpectralMeasure.ProjectionValuedMeasure S (Complexification H))
    (B : Set S) (x : Complexification H) :
    antiConjugate E B x = conjugation (E B (conjugation x)) := rfl

open MeasurableSpectralCalculus UnboundedNormalSpectralTheorem

/-- Intrinsic disk characterization is equivariant under real conjugation. -/
theorem disk_fixed_conjugation
    {E : SpectralMeasure.ProjectionValuedMeasure ℂ (Complexification H)}
    (C : BoundedRealization E)
    (hJ : ∀ x y, (x, y) ∈ (measurableIntegral C (fun w : ℂ => w)).graph →
      (conjugation x, conjugation y) ∈ (measurableIntegral C (fun w : ℂ => w)).graph)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (x : Complexification H)
    (hx : E (Metric.closedBall z r) x = x) :
    E (Metric.closedBall (star z) r) (conjugation x) = conjugation x := by
  obtain ⟨a, ha0, _, hg, hb⟩ := SpectralRepresentation.disk_sequence C z r hr x hx
  let b : ℕ → Complexification H := fun n => conjugation (a n)
  have hg' (n : ℕ) : (b n, (star z) • b n + b (n + 1)) ∈
      (measurableIntegral C (fun w : ℂ => w)).graph := by
    have hh := hJ _ _ (hg n)
    simpa only [b, map_add, map_smulₛₗ, RCLike.star_def] using hh
  have hb' (n : ℕ) : ‖b n‖ ≤ r ^ n * ‖b 0‖ := by
    simpa only [b, conjugation.norm_map, ha0] using hb n
  simpa only [b, ha0] using
    SpectralRepresentation.disk_fixed_of_graph_sequence C (star z) r hr b hg' hb'

/-- Orthogonal projection onto each disk transforms to the reflected disk. -/
theorem closedBall_conjugation
    {E : SpectralMeasure.ProjectionValuedMeasure ℂ (Complexification H)}
    (C : BoundedRealization E)
    (hJ : ∀ x y, (x, y) ∈ (measurableIntegral C (fun w : ℂ => w)).graph →
      (conjugation x, conjugation y) ∈ (measurableIntegral C (fun w : ℂ => w)).graph)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    E (Metric.closedBall z r) = reflectOperator (E (Metric.closedBall (star z) r)) := by
  let P := E (Metric.closedBall z r)
  let Q := reflectOperator (E (Metric.closedBall (star z) r))
  have hP : IsSelfAdjoint P := E.selfAdjoint _ measurableSet_closedBall
  have hQ : IsSelfAdjoint Q := reflectOperator_selfAdjoint _
    (E.selfAdjoint _ measurableSet_closedBall)
  have hQP : Q * P = P := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : E (Metric.closedBall z r) (P x) = P x := by
      exact congrArg (fun T : Complexification H →L[ℂ] Complexification H => T x)
        (E.idempotent _ measurableSet_closedBall)
    change conjugation (E (Metric.closedBall (star z) r) (conjugation (P x))) = P x
    rw [disk_fixed_conjugation C hJ z r hr (P x) hx, conjugation_conjugation]
  have hPQ : P * Q = Q := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : E (Metric.closedBall (star z) r)
        (E (Metric.closedBall (star z) r) (conjugation x)) =
        E (Metric.closedBall (star z) r) (conjugation x) :=
      congrArg (fun T : Complexification H →L[ℂ] Complexification H => T (conjugation x))
        (E.idempotent _ measurableSet_closedBall)
    simpa only [star_star, P, Q, mul_apply_eq_comp, reflectOperator_apply] using
      disk_fixed_conjugation C hJ (star z) r hr _ hx
  have hh := congrArg star hQP
  rw [star_mul, hP.star_eq, hQ.star_eq] at hh
  exact hh.symm.trans hPQ

/-- Reflected antiunitary PVM agrees on all Borel sets. -/
theorem borel_conjugation
    {E : SpectralMeasure.ProjectionValuedMeasure ℂ (Complexification H)}
    (C : BoundedRealization E)
    (hJ : ∀ x y, (x, y) ∈ (measurableIntegral C (fun w : ℂ => w)).graph →
      (conjugation x, conjugation y) ∈ (measurableIntegral C (fun w : ℂ => w)).graph)
    (B : Set ℂ) (hB : MeasurableSet B) :
    E B = reflectOperator (E ((star : ℂ → ℂ) ⁻¹' B)) := by
  let F := antiConjugate (E.map (star : ℂ → ℂ) Complex.conjLIE.continuous.measurable)
  have hF : SameBorelValues E F := by
    apply sameBorelValues_of_closedBall_eq
    intro z r hr
    change E (Metric.closedBall z r) = reflectOperator
      (E ((star : ℂ → ℂ) ⁻¹' Metric.closedBall z r))
    have heq : (star : ℂ → ℂ) ⁻¹' Metric.closedBall z r = Metric.closedBall (star z) r := by
      exact Complex.conjLIE.toIsometryEquiv.preimage_closedBall z r
    rw [heq]
    exact closedBall_conjugation C hJ z r hr
  exact hF B hB

/-- A real-base resolution of a conjugation-invariant graph has real projections. -/
theorem realbase_commutes_conjugation
    {E : SpectralMeasure.ProjectionValuedMeasure ℝ (Complexification H)}
    (C : BoundedRealization E)
    (hJ : ∀ x y, (x, y) ∈ (measurableIntegral C (fun t : ℝ => (t : ℂ))).graph →
      (conjugation x, conjugation y) ∈ (measurableIntegral C (fun t : ℝ => (t : ℂ))).graph)
    (B : Set ℝ) (hB : MeasurableSet B) (x : Complexification H) :
    E B (conjugation x) = conjugation (E B x) := by
  let D := C.map Complex.ofReal Complex.measurable_ofReal
  have hD : measurableIntegral D (fun w : ℂ => w) =
      measurableIntegral C (fun t : ℝ => (t : ℂ)) := by
    rw [C.measurableIntegral_map]
    rfl
  have hJD : ∀ y z, (y, z) ∈ (measurableIntegral D (fun w : ℂ => w)).graph →
      (conjugation y, conjugation z) ∈ (measurableIntegral D (fun w : ℂ => w)).graph := by
    simpa only [hD] using hJ
  have hh := borel_conjugation D hJD (Complex.re ⁻¹' B)
    (Complex.continuous_re.measurable hB)
  have hh' := congrArg (fun T : Complexification H →L[ℂ] Complexification H => T (conjugation x)) hh
  simpa [D, SpectralMeasure.ProjectionValuedMeasure.map_apply, reflectOperator_apply,
    preimage_preimage, Function.comp_def, Complex.star_def] using hh'


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private def realify (a : SimpleFunc ℝ≥0 ℂ) : SimpleFunc ℝ≥0 ℂ :=
  a.map (fun z => (z.re : ℂ))

private theorem realify_tendsto {a : ℕ → SimpleFunc ℝ≥0 ℂ} {f : ℝ≥0 → ℝ}
    (ha : TendstoUniformly (fun n => a n) (fun s => (f s : ℂ)) atTop) :
    TendstoUniformly (fun n => realify (a n)) (fun s => (f s : ℂ)) atTop := by
  rw [Metric.tendstoUniformly_iff] at ha ⊢
  intro ε hε
  filter_upwards [ha ε hε] with n hn s
  change dist (f s : ℂ) ((a n s).re : ℂ) < ε
  have hle : dist (f s : ℂ) ((a n s).re : ℂ) ≤ dist (f s : ℂ) (a n s) := by
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Complex.ofReal_re,
      Complex.sub_re, Real.norm_eq_abs] using Complex.abs_re_le_norm ((f s : ℂ) - a n s)
  exact hle.trans_lt (hn s)

private theorem simpleIntegral_realify_commutes
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z))
    (a : SimpleFunc ℝ≥0 ℂ) (z : Complexification H) :
    E.simpleIntegral (realify a) (conjugation z) =
      conjugation (E.simpleIntegral (realify a) z) := by
  rw [realify, E.simpleIntegral_map_of_zero a (fun z => (z.re : ℂ)) (by simp)]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sum, map_smulₛₗ, starRingEnd_apply, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hE _ (a.measurableSet_fiber c)]
  simp

/-- Real bounded spectral integrals preserve the fixed real space. -/
theorem realIntegral_commutes
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z))
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (z : Complexification H) :
    C.integral (fun s => (f s : ℂ)) (conjugation z) =
      conjugation (C.integral (fun s => (f s : ℂ)) z) := by
  have hfc : SpectralMeasure.Spec.IsBoundedMeasurable (fun s => (f s : ℂ)) := by
    obtain ⟨M, hM⟩ := hf.2
    exact ⟨Complex.continuous_ofReal.measurable.comp hf.1, M, fun s => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hM s⟩
  obtain ⟨a, ha⟩ := SpectralMeasure.exists_uniform_simple_approx _ hfc
  have hlim := C.uniform_limit _ hfc (fun n => realify (a n)) (realify_tendsto ha)
  have hleft := (((ContinuousLinearMap.apply ℂ (Complexification H))
    (conjugation z)).continuous.tendsto _).comp hlim
  have hright := conjugation.continuous.tendsto _ |>.comp
    ((((ContinuousLinearMap.apply ℂ (Complexification H)) z).continuous.tendsto _).comp hlim)
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall
    (fun n => (simpleIntegral_realify_commutes E hE (a n) z).symm)))

/-- Positive diagonal measure on real vectors, before restricting the PVM. -/
def realDiagonalMeasure
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)) (x : H) :
    Measure ℝ≥0 := E.diagonalMeasure (embedding x)

instance realDiagonalMeasure_finite
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)) (x : H) :
    IsFiniteMeasure (realDiagonalMeasure E x) := inferInstanceAs
      (IsFiniteMeasure (E.diagonalMeasure (embedding x)))

/-- The coefficient signed measure has exactly the real scalar pairings. -/
def realCoefficientMeasure
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)) (x y : H) :
    SignedMeasure ℝ≥0 := ComplexMeasure.re (E.coefficientMeasure (embedding x) (embedding y))

theorem realCoefficientMeasure_apply
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (x y : H) (B : Set ℝ≥0) (hB : MeasurableSet B) :
    realCoefficientMeasure E x y B = inner ℝ x (restrictBounded (E B) y) := by
  change (E.coefficientMeasure (embedding x) (embedding y) B).re = _
  rw [E.coefficientMeasure_apply _ _ _ hB]
  exact inner_embedding_left x _

theorem realDiagonalMeasure_apply
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (x : H) (B : Set ℝ≥0) (hB : MeasurableSet B) :
    realDiagonalMeasure E x B = ENNReal.ofReal (inner ℝ x (restrictBounded (E B) x)) := by
  rw [realDiagonalMeasure, E.diagonalMeasure_apply _ _ hB]
  congr 1
  have hh := congrArg Complex.re (E.coefficient_projection B hB (embedding x) (embedding x))
  change (inner ℂ (embedding x) (E B (embedding x))).re =
    (inner ℂ (E B (embedding x)) (E B (embedding x))).re at hh
  have hself : (inner ℂ (E B (embedding x)) (E B (embedding x))).re =
      ‖E B (embedding x)‖ ^ 2 := by
    change inner ℝ (E B (embedding x)).re (E B (embedding x)).re +
      inner ℝ (E B (embedding x)).im (E B (embedding x)).im = _
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sq]
  rw [hself] at hh
  exact hh.symm.trans (inner_embedding_left x _)

theorem realMeasurableIntegral_invariant
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z))
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) :
    ConjugationInvariant (MeasurableSpectralCalculus.measurableIntegral C
      (fun s => (f s : ℂ))) := by
  intro x
  change (_, _) ∈ (MeasurableSpectralCalculus.limitOperator
    (fun n => C.integral (MeasurableSpectralCalculus.truncation
      (fun s => (f s : ℂ)) n))).graph
  rw [MeasurableSpectralCalculus.mem_limitOperator_graph_iff]
  have hfc : Measurable (fun s => (f s : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hf
  have ht (n : ℕ) : MeasurableSpectralCalculus.truncation
      (fun s => (f s : ℂ)) n = fun s => (truncation f n s : ℂ) := by
    classical
    funext s
    simp only [MeasurableSpectralCalculus.truncation, truncation,
      Complex.norm_real, Real.norm_eq_abs]
    by_cases hs : |f s| ≤ (n : ℝ) <;> simp [hs]
  have hb (n : ℕ) : IsBoundedMeasurable (truncation f n) := by
    have h := MeasurableSpectralCalculus.boundedMeasurable_truncation hfc n
    rw [ht n] at h
    refine ⟨?_, n, ?_⟩
    · have hm := Complex.measurable_re.comp h.1
      simpa only [Function.comp_def, Complex.ofReal_re] using hm
    · intro s
      have := MeasurableSpectralCalculus.norm_truncation_le
        (fun s => (f s : ℂ)) n s
      rw [ht n] at this
      simpa only [Complex.norm_real, Real.norm_eq_abs] using this
  have hh := conjugation.continuous.tendsto _ |>.comp
    (MeasurableSpectralCalculus.measurableIntegral_tendsto C
      (fun s => (f s : ℂ)) x)
  have heq (n : ℕ) := realIntegral_commutes E hE C (truncation f n) (hb n) (x : _)
  simp only [← ht] at heq
  exact hh.congr' (Eventually.of_forall fun n => (heq n).symm)

end Complexification

/-- Apply the accepted complex spectral theorem to the external complexification
of the actual real operator. Subsequent lemmas descend this resolution to H. -/
theorem complex_spectral_resolution {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (L : Operator ℝ H H)
    (hL : NonnegativeSelfAdjoint L) :
    ∃ E : SpectralMeasure.ProjectionValuedMeasure ℝ (Complexification H),
      UnboundedNormalSpectralTheorem.RealResolves (Complexification.operator L) E := by
  have hd := Complexification.dense_operator L hL.1
  have hs := Complexification.operator_selfAdjoint L hL.1 hL.2.1
  have hc : (Complexification.operator L).IsClosed := by
    rw [← hs]
    exact LinearPMap.adjoint_isClosed hd
  exact (UnboundedNormalSpectralTheorem.selfadjoint_spectral
    (Complexification H) (Complexification.operator L) hd hc hs).1

namespace StrongConvergenceWork
open SpectralMeasure MeasurableSpectralCalculus
universe v
variable {S : Type u} [MeasurableSpace S] {K : Type v}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
/-- The separately diagonal-a.e. hypothesis implies a single spectral-null
exceptional set, because the convergence set is measurable. -/
theorem bounded_strong_convergence
    {E : SpectralMeasure.ProjectionValuedMeasure S K} (C : BoundedRealization E)
    (f : S → ℂ) (a : ℕ → S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (ha : ∀ n, SpectralMeasure.Spec.IsBoundedMeasurable (a n))
    (hb : ∃ M : ℝ, ∀ n s, ‖a n s‖ ≤ M)
    (hlim : ∀ x, ∀ᵐ s ∂C.measure x,
      Tendsto (fun n => a n s) atTop (nhds (f s))) :
    ∀ x, Tendsto (fun n => C.integral (a n) x) atTop (nhds (C.integral f x)) := by
  let Z := {s : S | ¬ Tendsto (fun n => a n s) atTop (nhds (f s))}
  have hZ : MeasurableSet Z :=
    (measurableSet_tendsto_fun (fun n => (ha n).1) hf.1).compl
  have hnull : E Z = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change E Z x = 0
    have hm : C.measure x Z = 0 := ae_iff.mp (hlim x)
    rw [C.measure_apply x Z hZ] at hm
    have hs := ENNReal.ofReal_eq_zero.mp hm
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (E Z x)]
  have hlimE : NormalSpectral.Spec.AlmostEverywhere E
      (fun s => Tendsto (fun n => a n s) atTop (nhds (f s))) := by
    refine ⟨Z, hZ, hnull, ?_⟩
    intro s hs
    exact not_not.mp hs
  have h := NormalSpectral.strong_convergence E f a hf ha hb hlimE
  have heqa (n : ℕ) : C.integral (a n) = E.spectralIntegral (a n) :=
    UnboundedNormalSpectralTheorem.SpectralRepresentation.integral_eq C _ (ha n)
  have heqf : C.integral f = E.spectralIntegral f :=
    UnboundedNormalSpectralTheorem.SpectralRepresentation.integral_eq C _ hf
  simpa only [heqa, heqf] using h

end StrongConvergenceWork


def complexSymbol (f : ℝ≥0 → ℝ) : ℝ≥0 → ℂ := fun s => (f s : ℂ)

@[simp] theorem complexSymbol_one : complexSymbol (fun _ => 1) = fun _ => 1 := rfl
@[simp] theorem complexSymbol_add (f g : ℝ≥0 → ℝ) :
    complexSymbol (f + g) = complexSymbol f + complexSymbol g := by ext; simp [complexSymbol]
@[simp] theorem complexSymbol_mul (f g : ℝ≥0 → ℝ) :
    complexSymbol (f * g) = complexSymbol f * complexSymbol g := by ext; simp [complexSymbol]
@[simp] theorem complexSymbol_smul (a : ℝ) (f : ℝ≥0 → ℝ) :
    complexSymbol (a • f) = (a : ℂ) • complexSymbol f := by ext; simp [complexSymbol]
@[simp] theorem complexSymbol_star (f : ℝ≥0 → ℝ) : star (complexSymbol f) = complexSymbol f := by
  ext; simp [complexSymbol]
@[simp] theorem complexSymbol_indicator (B : Set ℝ≥0) (f : ℝ≥0 → ℝ) :
    complexSymbol (B.indicator f) = B.indicator (complexSymbol f) := by
  classical
  ext s
  by_cases hs : s ∈ B <;> simp [complexSymbol, hs]

theorem measurable_complexSymbol {f : ℝ≥0 → ℝ} (hf : Measurable f) :
    Measurable (complexSymbol f) := Complex.measurable_ofReal.comp hf

theorem boundedMeasurable_complexSymbol {f : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) :
    SpectralMeasure.Spec.IsBoundedMeasurable (complexSymbol f) := by
  refine ⟨measurable_complexSymbol hf.1, hf.2.choose, fun s => ?_⟩
  simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs] using hf.2.choose_spec s

namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)}
  (C : MeasurableSpectralCalculus.BoundedRealization E)

def realBounded (f : ℝ≥0 → ℝ) : H →L[ℝ] H := restrictBounded (C.integral (complexSymbol f))
def realSpectralOperator (f : ℝ≥0 → ℝ) : Operator ℝ H H :=
  restrictOperator (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol f))

theorem realBounded_one : realBounded C (fun _ => 1) = 1 := by
  rw [realBounded, complexSymbol_one, C.one, restrictBounded_one]

theorem realBounded_add {f g : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    realBounded C (f + g) = realBounded C f + realBounded C g := by
  rw [realBounded, complexSymbol_add, C.add _ _ (boundedMeasurable_complexSymbol hf)
    (boundedMeasurable_complexSymbol hg), restrictBounded_add]
  rfl

theorem realBounded_smul (a : ℝ) {f : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) :
    realBounded C (a • f) = a • realBounded C f := by
  rw [realBounded, complexSymbol_smul, C.smul _ _ (boundedMeasurable_complexSymbol hf)]
  exact restrictBounded_real_smul a _

theorem realBounded_mul
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z))
    {f g : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    realBounded C (f * g) = realBounded C f * realBounded C g := by
  rw [realBounded, complexSymbol_mul, C.mul _ _ (boundedMeasurable_complexSymbol hf)
    (boundedMeasurable_complexSymbol hg)]
  exact restrictBounded_mul _ _ (realIntegral_commutes E hE C g hg)

theorem realBounded_adjoint {f : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) :
    ContinuousLinearMap.adjoint (realBounded C f) = realBounded C f := by
  rw [realBounded, restrictBounded_adjoint]
  change restrictBounded (star (C.integral (complexSymbol f))) = _
  rw [← C.map_star _ (boundedMeasurable_complexSymbol hf), complexSymbol_star]

theorem realBounded_indicator (B : Set ℝ≥0) (hB : MeasurableSet B) :
    realBounded C (B.indicator (fun _ => 1)) = restrictBounded (E B) := by
  rw [realBounded, complexSymbol_indicator, complexSymbol_one,
    UnboundedNormalSpectralTheorem.SpectralRepresentation.integral_indicator_one C B hB]

theorem realBounded_bound {f : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s, |f s| ≤ M) : ‖realBounded C f‖ ≤ M := by
  apply (restrictBounded_norm_le _).trans
  apply C.bound _ M (boundedMeasurable_complexSymbol hf) hM
  intro s
  simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs] using hb s

end Complexification

namespace RealTransfer

open Complexification MeasurableSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)}

def realIntegral (C : BoundedRealization E) (f : ℝ≥0 → ℝ) : Operator ℝ H H :=
  restrictOperator (measurableIntegral C (fun s => (f s : ℂ)))

theorem realIntegral_domain (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (x : H) :
    x ∈ (realIntegral C f).domain ↔ SquareIntegrable (C.measure (embedding x)) f := by
  change embedding x ∈ (measurableIntegral C (fun s => (f s : ℂ))).domain ↔ _
  have hf' : Measurable (fun s => (f s : ℂ)) := Complex.measurable_ofReal.comp hf
  rw [measurableIntegral_domain C hf' (embedding x)]
  simp only [MeasurableSpectralCalculus.SquareIntegrable, SquareIntegrable,
    Complex.norm_real, Real.norm_eq_abs]

variable (hE : ∀ B, MeasurableSet B → ∀ z,
  E B (conjugation z) = conjugation (E B z))
include hE

theorem realIntegral_dense (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) :
    Dense ((realIntegral C f).domain : Set H) :=
  dense_restrictOperator _ (realMeasurableIntegral_invariant E hE C f hf)
    (measurableIntegral_dense C (Complex.measurable_ofReal.comp hf))

theorem realIntegral_isClosed (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) :
    (realIntegral C f).IsClosed :=
  restrictOperator_isClosed _ (realMeasurableIntegral_invariant E hE C f hf)
    (measurableIntegral_isClosed C (Complex.measurable_ofReal.comp hf))

theorem realIntegral_selfAdjoint (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) :
    (realIntegral C f).adjoint = realIntegral C f :=
  restrictOperator_selfAdjoint _ (realMeasurableIntegral_invariant E hE C f hf)
    (measurableIntegral_dense C (Complex.measurable_ofReal.comp hf))
    (measurableIntegral_selfAdjoint C (Complex.measurable_ofReal.comp hf) (by simp))

theorem realIntegral_norm_sq (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (x : (realIntegral C f).domain) :
    ‖realIntegral C f x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂C.measure (embedding x) := by
  have hemb := restrictOperator_embedding _ (realMeasurableIntegral_invariant E hE C f hf) x
  have hnorm := congrArg (fun z => ‖z‖ ^ 2) hemb
  simp only [embedding.norm_map] at hnorm
  apply hnorm.trans
  simpa only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs] using
    unbounded_norm_sq C (Complex.measurable_ofReal.comp hf) ⟨embedding x, x.property⟩

theorem realIntegral_nonnegative (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (hp : ∀ s, 0 ≤ f s)
    (x : (realIntegral C f).domain) :
    0 ≤ inner ℝ (x : H) (realIntegral C f x) := by
  have hh := PositivityWork.measurableIntegral_nonnegative C
    (Complex.measurable_ofReal.comp hf) (by simp) (by simpa only [Function.comp_def, Complex.ofReal_re] using hp)
    (⟨embedding x, x.property⟩ : (measurableIntegral C (fun s => (f s : ℂ))).domain)
  change 0 ≤ (inner ℂ (embedding (x : H))
    (measurableIntegral C (fun s => (f s : ℂ)) ⟨embedding x, x.property⟩)).re at hh
  rw [← restrictOperator_embedding _ (realMeasurableIntegral_invariant E hE C f hf) x] at hh
  simp only [inner_embedding_left, embedding_re] at hh
  exact hh

omit hE in
theorem realIntegral_domain_growth (C : BoundedRealization E)
    (f g : ℝ≥0 → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hb : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ s, |f s| ^ 2 ≤ a + b * |g s| ^ 2) :
    (realIntegral C g).domain ≤ (realIntegral C f).domain := by
  intro x hx
  apply ComplexCalculus.domain_growth C
    (Complex.measurable_ofReal.comp hf) (Complex.measurable_ofReal.comp hg)
    (by simpa only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs] using hb)
  exact hx

omit hE in
/-- All accepted bounded realizations have the same actual scalar measure. -/
theorem realization_measure_eq_diagonalMeasure (C : BoundedRealization E)
    (z : Complexification H) : C.measure z = E.diagonalMeasure z := by
  ext B hB
  rw [C.measure_apply z B hB, E.diagonalMeasure_apply z B hB]

omit hE in
theorem realIntegral_domain_diagonal (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (x : H) :
    x ∈ (realIntegral C f).domain ↔ SquareIntegrable (realDiagonalMeasure E x) f := by
  rw [realIntegral_domain C f hf x, realization_measure_eq_diagonalMeasure C]
  rfl

theorem realIntegral_norm_sq_diagonal (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (x : (realIntegral C f).domain) :
    ‖realIntegral C f x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂realDiagonalMeasure E x := by
  rw [realIntegral_norm_sq hE C f hf x, realization_measure_eq_diagonalMeasure C]
  rfl

omit hE in
/-- Truncations of a real symbol are the real restrictions of its complex
truncations; their norm limit is the exact restricted integral. -/
theorem realIntegral_truncation_limit (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (x : (realIntegral C f).domain) :
    Tendsto (fun n => restrictBounded
      (C.integral (fun s => (truncation f n s : ℂ))) x) atTop
      (𝓝 (realIntegral C f x)) := by
  have ht (n : ℕ) : MeasurableSpectralCalculus.truncation
      (fun s => (f s : ℂ)) n = fun s => (truncation f n s : ℂ) := by
    classical
    funext s
    simp only [MeasurableSpectralCalculus.truncation, truncation,
      Complex.norm_real, Real.norm_eq_abs]
    by_cases hs : |f s| ≤ (n : ℝ) <;> simp [hs]
  have hc : Continuous (fun z : Complexification H => z.re) :=
    continuous_fst.comp coordinates.continuous
  have hh : Tendsto (fun n =>
      (C.integral (MeasurableSpectralCalculus.truncation
        (fun s => (f s : ℂ)) n) (embedding (x : H))).re) atTop
      (𝓝 (realIntegral C f x)) :=
    (hc.tendsto _).comp (measurableIntegral_tendsto C
      (fun s => (f s : ℂ)) ⟨embedding x, x.property⟩)
  simp only [ht] at hh
  exact hh


end RealTransfer
namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
instance realCoefficientMeasure_variation_finite
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)) (x y : H) :
    IsFiniteMeasure (realCoefficientMeasure E x y).variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

theorem realSimpleIntegral_coefficient
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (b : SimpleFunc ℝ≥0 ℝ) (x y : H) :
    inner ℝ x (restrictBounded (E.simpleIntegral (b.map Complex.ofReal)) y) =
      (realCoefficientMeasure E x y).integral b (ContinuousLinearMap.mul ℝ ℝ) := by
  rw [VectorMeasure.integral_eq_setToFun,
    setToFun_simpleFunc _ b b.integrable_of_isFiniteMeasure]
  change inner ℝ x (E.simpleIntegral (b.map Complex.ofReal) (embedding y)).re = _
  rw [← inner_embedding_left]
  rw [E.simpleIntegral_map_of_zero b Complex.ofReal (by simp)]
  simp only [sum_apply, smul_apply, inner_sum, inner_smul_right]
  change Complex.re (∑ r ∈ b.range, (r : ℂ) *
    inner ℂ (embedding x) (E (b ⁻¹' {r}) (embedding y))) = _
  change Complex.reCLM (∑ r ∈ b.range, (r : ℂ) * inner ℂ (embedding x) (E (b ⁻¹' {r}) (embedding y))) = _
  rw [map_sum]
  change (∑ r ∈ b.range, ((r : ℂ) * inner ℂ (embedding x)
    (E (b ⁻¹' {r}) (embedding y))).re) = _
  simp only [
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro r hr
  change r * (inner ℂ (embedding x) (E (b ⁻¹' {r}) (embedding y))).re =
    r * realCoefficientMeasure E x y (b ⁻¹' {r})
  rw [realCoefficientMeasure_apply E x y _ (b.measurableSet_fiber r)]
  rw [inner_embedding_left]
  rfl

theorem bounded_realCoefficient_integrable
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (f : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (x y : H) :
    (realCoefficientMeasure E x y).Integrable f := by
  obtain ⟨M, hM⟩ := hf.2
  apply Integrable.of_bound hf.1.stronglyMeasurable.aestronglyMeasurable M
  exact Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hM s



theorem bounded_realCoefficient_integral
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (x y : H) :
    inner ℝ x (restrictBounded (C.integral (fun s => (f s : ℂ))) y) =
      (realCoefficientMeasure E x y).integral f (ContinuousLinearMap.mul ℝ ℝ) := by
  have hfc : SpectralMeasure.Spec.IsBoundedMeasurable (fun s => (f s : ℂ)) := by
    obtain ⟨M, hM⟩ := hf.2
    exact ⟨Complex.continuous_ofReal.measurable.comp hf.1, M, fun s => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hM s⟩
  obtain ⟨a, ha⟩ := SpectralMeasure.exists_uniform_simple_approx _ hfc
  let b : ℕ → SimpleFunc ℝ≥0 ℝ := fun n => (a n).map Complex.re
  have hb : TendstoUniformly (fun n => (b n).map Complex.ofReal)
      (fun s => (f s : ℂ)) atTop := by
    rw [Metric.tendstoUniformly_iff] at ha ⊢
    intro ε hε
    filter_upwards [ha ε hε] with n hn s
    change dist (f s : ℂ) ((a n s).re : ℂ) < ε
    have hle : dist (f s : ℂ) ((a n s).re : ℂ) ≤ dist (f s : ℂ) (a n s) := by
      simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Complex.ofReal_re,
        Complex.sub_re, Real.norm_eq_abs] using Complex.abs_re_le_norm ((f s : ℂ) - a n s)
    exact hle.trans_lt (hn s)
  have hlim := C.uniform_limit _ hfc (fun n => (b n).map Complex.ofReal) hb
  have hcont : Continuous (fun T : Complexification H →L[ℂ] Complexification H =>
      inner ℝ x (T (embedding y)).re) := by
    exact continuous_const.inner (((continuous_fst.comp coordinates.continuous).comp
      (ContinuousLinearMap.apply ℂ (Complexification H) (embedding y)).continuous))
  have hleft := (hcont.tendsto _).comp hlim
  have hright : Tendsto (fun n => (realCoefficientMeasure E x y).integral (b n)
      (ContinuousLinearMap.mul ℝ ℝ)) atTop (nhds ((realCoefficientMeasure E x y).integral f
        (ContinuousLinearMap.mul ℝ ℝ))) := by
    apply VectorMeasure.tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun n => (b n).measurable.stronglyMeasurable.aestronglyMeasurable
    · obtain ⟨M, hM⟩ := hf.2
      refine ⟨M + 1, ?_⟩
      filter_upwards [Metric.tendstoUniformly_iff.mp hb 1 (by positivity)] with n hn
      exact Eventually.of_forall fun s => by
        have hdist := hn s
        change dist (f s : ℂ) (b n s : ℂ) < 1 at hdist
        have hdist' : |f s - b n s| < 1 := by
          simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs] using hdist
        have htri := abs_add_le (b n s - f s) (f s)
        rw [sub_add_cancel] at htri
        rw [abs_sub_comm] at htri
        change |b n s| ≤ M + 1
        linarith [hM s]
    · exact Eventually.of_forall fun s => by
        have hh := Complex.continuous_re.tendsto _ |>.comp (hb.tendsto_at s)
        simpa only [Function.comp_def, SimpleFunc.map_apply, Complex.ofReal_re] using hh
  have hsame (n : ℕ) : inner ℝ x
      ((SpectralMeasure.Spec.SimpleIntegralValue E ((b n).map Complex.ofReal)) (embedding y)).re =
      (realCoefficientMeasure E x y).integral (b n) (ContinuousLinearMap.mul ℝ ℝ) :=
    realSimpleIntegral_coefficient E (b n) x y
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n => (hsame n).symm))


end Complexification


theorem signedMeasure_integral_sign (ν : SignedMeasure ℝ≥0) :
    ∃ ε : ℝ≥0 → ℝ, Measurable ε ∧ (∀ s, |ε s| = 1) ∧
      ∀ (u : ℝ≥0 → ℝ), IsBoundedMeasurable u →
        ν.integral (ε * u) (ContinuousLinearMap.mul ℝ ℝ) = ∫ s, u s ∂ν.variation := by
  classical
  obtain ⟨S, hS, hpos, hneg⟩ := ν.toJordanDecomposition.mutuallySingular
  let ε : ℝ≥0 → ℝ := S.piecewise (fun _ => -1) (fun _ => 1)
  have hε : Measurable ε := measurable_const.piecewise hS measurable_const
  have hεabs (s : ℝ≥0) : |ε s| = 1 := by
    by_cases hs : s ∈ S <;> simp [ε, hs]
  refine ⟨ε, hε, hεabs, ?_⟩
  intro u hu
  obtain ⟨M, hM⟩ := hu.2
  have hnorm (s : ℝ≥0) : ‖(ε * u) s‖ ≤ M := by
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, hεabs, one_mul] using hM s
  have hiP : Integrable (ε * u) ν.toJordanDecomposition.posPart :=
    Integrable.of_bound (hε.mul hu.1).stronglyMeasurable.aestronglyMeasurable M
      (Eventually.of_forall hnorm)
  have hiN : Integrable (ε * u) ν.toJordanDecomposition.negPart :=
    Integrable.of_bound (hε.mul hu.1).stronglyMeasurable.aestronglyMeasurable M
      (Eventually.of_forall hnorm)
  have huP : Integrable u ν.toJordanDecomposition.posPart :=
    Integrable.of_bound hu.1.stronglyMeasurable.aestronglyMeasurable M
      (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hM s)
  have huN : Integrable u ν.toJordanDecomposition.negPart :=
    Integrable.of_bound hu.1.stronglyMeasurable.aestronglyMeasurable M
      (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hM s)
  have haeP : ∀ᵐ s ∂ν.toJordanDecomposition.posPart, s ∉ S := by
    apply ae_iff.mpr
    simpa only [not_not] using (show ν.toJordanDecomposition.posPart {a | a ∈ S} = 0 from hpos)
  have haeN : ∀ᵐ s ∂ν.toJordanDecomposition.negPart, s ∈ S := by
    exact ae_iff.mpr hneg
  have heP : (ε * u) =ᵐ[ν.toJordanDecomposition.posPart] u := by
    filter_upwards [haeP] with s hs
    simp [ε, hs]
  have heN : (ε * u) =ᵐ[ν.toJordanDecomposition.negPart] -u := by
    filter_upwards [haeN] with s hs
    simp [ε, hs]
  have hiVP : ν.toJordanDecomposition.posPart.toSignedMeasure.Integrable (ε * u) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hiP
  have hiVN : ν.toJordanDecomposition.negPart.toSignedMeasure.Integrable (ε * u) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hiN
  have hpair : ContinuousLinearMap.mul ℝ ℝ = (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm a b
  calc
    ν.integral (ε * u) (ContinuousLinearMap.mul ℝ ℝ) =
        (ν.toJordanDecomposition.posPart.toSignedMeasure -
          ν.toJordanDecomposition.negPart.toSignedMeasure).integral (ε * u)
          (ContinuousLinearMap.mul ℝ ℝ) := by
      congr 1
      exact ν.toSignedMeasure_toJordanDecomposition.symm
    _ = (ν.toJordanDecomposition.posPart.toSignedMeasure.integral (ε * u)
        (ContinuousLinearMap.mul ℝ ℝ)) -
        (ν.toJordanDecomposition.negPart.toSignedMeasure.integral (ε * u)
          (ContinuousLinearMap.mul ℝ ℝ)) :=
      VectorMeasure.integral_sub_vectorMeasure hiVP hiVN
    _ = (∫ s, (ε * u) s ∂ν.toJordanDecomposition.posPart) -
        (∫ s, (ε * u) s ∂ν.toJordanDecomposition.negPart) := by
      rw [hpair, VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
    _ = (∫ s, u s ∂ν.toJordanDecomposition.posPart) +
        (∫ s, u s ∂ν.toJordanDecomposition.negPart) := by
      rw [integral_congr_ae heP, integral_congr_ae heN]
      simp only [Pi.neg_apply, integral_neg, sub_neg_eq_add]
    _ = ∫ s, u s ∂ν.variation := by
      rw [← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation,
        integral_add_measure huP huN]


namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem bounded_realCoefficient_variation_bound
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (x y : H) :
    (∫ s, |f s| ∂(realCoefficientMeasure E x y).variation) ≤
      ‖x‖ * ‖C.integral (fun s => (f s : ℂ)) (embedding y)‖ := by
  obtain ⟨ε, hε, hεabs, hsign⟩ :=
    signedMeasure_integral_sign
      (realCoefficientMeasure E x y)
  have hfa : IsBoundedMeasurable (fun s => |f s|) :=
    ⟨((by simpa only [Real.norm_eq_abs] using hf.1.norm) : Measurable (fun s => |f s|)), hf.2.choose, fun s => by simpa only [abs_abs] using hf.2.choose_spec s⟩
  have hεf : IsBoundedMeasurable (ε * fun s => |f s|) := by
    refine ⟨hε.mul ((by simpa only [Real.norm_eq_abs] using hf.1.norm) : Measurable (fun s => |f s|)), hf.2.choose, fun s => ?_⟩
    simpa only [Pi.mul_apply, abs_mul, hεabs, abs_abs, one_mul] using hf.2.choose_spec s
  have hnorm : ‖C.integral (fun s => ((ε * fun s => |f s|) s : ℂ)) (embedding y)‖ =
      ‖C.integral (fun s => (f s : ℂ)) (embedding y)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖C.integral (complexSymbol (ε * fun s => |f s|)) (embedding y)‖ ^ 2 =
      ‖C.integral (complexSymbol f) (embedding y)‖ ^ 2
    rw [C.norm_sq _ (boundedMeasurable_complexSymbol hεf),
      C.norm_sq _ (boundedMeasurable_complexSymbol hf)]
    congr 1
    funext s
    simp only [complexSymbol, Complex.norm_real, Real.norm_eq_abs, Pi.mul_apply, abs_mul, hεabs,
      abs_abs, one_mul]
  calc
    (∫ s, |f s| ∂(realCoefficientMeasure E x y).variation) =
        (realCoefficientMeasure E x y).integral (ε * fun s => |f s|)
          (ContinuousLinearMap.mul ℝ ℝ) := (hsign _ hfa).symm
    _ = inner ℝ x (restrictBounded
        (C.integral (fun s => ((ε * fun s => |f s|) s : ℂ))) y) :=
      (bounded_realCoefficient_integral E C _ hεf x y).symm
    _ ≤ ‖x‖ * ‖restrictBounded
        (C.integral (fun s => ((ε * fun s => |f s|) s : ℂ))) y‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * ‖C.integral
        (fun s => ((ε * fun s => |f s|) s : ℂ)) (embedding y)‖ :=
      mul_le_mul_of_nonneg_left (norm_re_le _) (norm_nonneg x)
    _ = ‖x‖ * ‖C.integral (fun s => (f s : ℂ)) (embedding y)‖ := by rw [hnorm]


end Complexification

section ComplexTransferHelpers
open SpectralMeasure MeasurableSpectralCalculus
universe v
section Bounded
variable {S : Type u} [MeasurableSpace S] {K : Type v}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A uniformly bounded symbol has the everywhere defined bounded integral. -/
theorem measurableIntegral_bounded_eq
    {E : SpectralMeasure.ProjectionValuedMeasure S K} (C : BoundedRealization E)
    (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    measurableIntegral C f = (C.integral f).toLinearMap.toPMap ⊤ := by
  obtain ⟨M, hM⟩ := hf.2
  obtain ⟨N, hN⟩ := exists_nat_ge M
  have ht : ∀ᶠ n : ℕ in atTop, MeasurableSpectralCalculus.truncation f n = f := by
    filter_upwards [eventually_ge_atTop N] with n hn
    funext s
    change ({s : S | ‖f s‖ ≤ (n : ℝ)}.indicator f) s = f s
    have hs : s ∈ {s : S | ‖f s‖ ≤ (n : ℝ)} := (hM s).trans (hN.trans (Nat.cast_le.mpr hn))
    exact Set.indicator_of_mem hs f
  have hlim (x : K) : Tendsto
      (fun n => C.integral (MeasurableSpectralCalculus.truncation f n) x)
      atTop (nhds (C.integral f x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [ht] with n hn
    rw [hn]
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  change (x, y) ∈ (limitOperator _).graph ↔ _
  rw [mem_limitOperator_graph_iff]
  constructor
  · intro h
    exact (ExpandedFA.Unbounded.mem_graph_iff _ _).mpr
      ⟨Submodule.mem_top, tendsto_nhds_unique (hlim x) h⟩
  · intro h
    obtain ⟨_, he⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp h
    change C.integral f x = y at he
    rw [← he]
    exact hlim x
end Bounded

namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)}

/-- The exact bounded agreement descends to the real fixed space. -/
theorem realIntegral_bounded_eq (C : BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) :
    restrictOperator (measurableIntegral C (fun s => (f s : ℂ))) =
      (restrictBounded (C.integral (fun s => (f s : ℂ)))).toLinearMap.toPMap ⊤ := by
  rw [measurableIntegral_bounded_eq C _ ?_, restrictOperator_bounded]
  obtain ⟨M, hM⟩ := hf.2
  exact ⟨Complex.measurable_ofReal.comp hf.1, M, fun s => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hM s⟩

/-- Restriction preserves the full maximal product domain and product inclusion. -/
theorem realIntegral_product_rule (C : BoundedRealization E)
    (f g : ℝ≥0 → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hInv : ConjugationInvariant (measurableIntegral C (fun s => (g s : ℂ)))) :
    (OperatorDomainsSpec.productValue
      (restrictOperator (measurableIntegral C (fun s => (f s : ℂ))))
      (restrictOperator (measurableIntegral C (fun s => (g s : ℂ))))).domain =
        (restrictOperator (measurableIntegral C (fun s => (g s : ℂ)))).domain ⊓
        (restrictOperator (measurableIntegral C (fun s => ((f * g) s : ℂ)))).domain ∧
    OperatorDomainsSpec.productValue
      (restrictOperator (measurableIntegral C (fun s => (f s : ℂ))))
      (restrictOperator (measurableIntegral C (fun s => (g s : ℂ)))) ≤
        restrictOperator (measurableIntegral C (fun s => ((f * g) s : ℂ))) := by
  have hmul : (fun s => ((f * g) s : ℂ)) =
      (fun s => (f s : ℂ)) * (fun s => (g s : ℂ)) := by funext s; simp
  rw [hmul]
  have h := SpectralProductAndSumDomains.product_rule C (fun s => (f s : ℂ)) (fun s => (g s : ℂ))
    (Complex.measurable_ofReal.comp hf) (Complex.measurable_ofReal.comp hg)
  constructor
  · rw [← restrictOperator_product _ _ hInv]
    apply Submodule.ext
    intro x
    change embedding x ∈ (OperatorDomainsSpec.productValue
      (measurableIntegral C (fun s => (f s : ℂ)))
      (measurableIntegral C (fun s => (g s : ℂ)))).domain ↔
      embedding x ∈ (measurableIntegral C (fun s => (g s : ℂ))).domain ∧
      embedding x ∈ (measurableIntegral C
        ((fun s => (f s : ℂ)) * (fun s => (g s : ℂ)))).domain
    rw [h.1]
    rfl
  · have hh := restrictOperator_mono h.2
    rw [restrictOperator_product _ _ hInv] at hh
    exact hh

/-- Growth of real symbols gives inclusion of the exact restriction domains. -/
theorem realIntegral_domain_growth (C : BoundedRealization E)
    (f g : ℝ≥0 → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hb : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ s, |f s| ^ 2 ≤ a + b * |g s| ^ 2) :
    (restrictOperator (measurableIntegral C (fun s => (g s : ℂ)))).domain ≤
      (restrictOperator (measurableIntegral C (fun s => (f s : ℂ)))).domain := by
  have h := ComplexCalculus.domain_growth C
    (Complex.measurable_ofReal.comp hf) (Complex.measurable_ofReal.comp hg) (by
      simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hb)
  intro x hx
  exact h hx

/-- A bounded real multiplier preserves each exact restricted domain. -/
theorem realIntegral_bounded_commutes (C : BoundedRealization E)
    (f g : ℝ≥0 → ℝ) (hf : Measurable f) (hg : IsBoundedMeasurable g)
    (hA : ConjugationInvariant (measurableIntegral C (fun s => (f s : ℂ))))
    (hB : ∀ z, C.integral (fun s => (g s : ℂ)) (conjugation z) =
      conjugation (C.integral (fun s => (g s : ℂ)) z))
    (x : (restrictOperator (measurableIntegral C (fun s => (f s : ℂ)))).domain) :
    (restrictBounded (C.integral (fun s => (g s : ℂ))) x,
      restrictBounded (C.integral (fun s => (g s : ℂ)))
        (restrictOperator (measurableIntegral C (fun s => (f s : ℂ))) x)) ∈
      (restrictOperator (measurableIntegral C (fun s => (f s : ℂ)))).graph := by
  have hgc : SpectralMeasure.Spec.IsBoundedMeasurable (fun s => (g s : ℂ)) := by
    obtain ⟨M, hM⟩ := hg.2
    exact ⟨Complex.measurable_ofReal.comp hg.1, M, fun s => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hM s⟩
  apply (mem_restrictOperator_graph _ hA _ _).mpr
  rw [restrictBounded_embedding _ hB, restrictBounded_embedding _ hB,
    restrictOperator_embedding _ hA]
  exact UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_commutes C
    (Complex.measurable_ofReal.comp hf) hgc ⟨embedding x, x.property⟩

end Complexification
end ComplexTransferHelpers

/-- A complex spectral resolution on the nonnegative half-line whose Borel
projections preserve the embedded real Hilbert space. -/
theorem nonnegative_spectral_resolution {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (L : Operator ℝ H H)
    (hL : NonnegativeSelfAdjoint L) :
    ∃ E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H),
    ∃ C : MeasurableSpectralCalculus.BoundedRealization E,
      (∀ B, MeasurableSet B → ∀ z,
        E B (Complexification.conjugation z) = Complexification.conjugation (E B z)) ∧
      MeasurableSpectralCalculus.measurableIntegral C (fun s : ℝ≥0 => ((s : ℝ) : ℂ)) =
        Complexification.operator L := by
  obtain ⟨E, C, hC, hsquare⟩ := complex_spectral_resolution L hL
  have hJ : ∀ x y, (x, y) ∈
      (MeasurableSpectralCalculus.measurableIntegral C (fun t : ℝ => (t : ℂ))).graph →
      (Complexification.conjugation x, Complexification.conjugation y) ∈
      (MeasurableSpectralCalculus.measurableIntegral C (fun t : ℝ => (t : ℂ))).graph := by
    rw [hC]
    intro x y hxy
    obtain ⟨hx, he⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp hxy
    exact (ExpandedFA.Unbounded.mem_graph_iff _ _).mpr
      ⟨Complexification.operator_conjugation_mem L ⟨x, hx⟩,
        (Complexification.operator_conjugation L ⟨x, hx⟩).trans
          (congrArg Complexification.conjugation he)⟩
  have hcomm := Complexification.realbase_commutes_conjugation C hJ
  obtain ⟨D, hD, _⟩ := SupportWork.realResolves_nonnegative_rebase
    (Complexification.operator L) E ⟨C, hC, hsquare⟩
    (Complexification.operator_nonnegative L hL.2.2)
  refine ⟨E.map Real.toNNReal measurable_real_toNNReal, D, ?_, hD⟩
  intro B hB z
  exact hcomm (Real.toNNReal ⁻¹' B) (measurable_real_toNNReal hB) z

namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A complex linear map preserving real vectors is its real restriction on
both coordinates. -/
theorem bounded_coordinates (B : Complexification H →L[ℂ] Complexification H)
    (hB : ∀ z, B (conjugation z) = conjugation (B z)) (z : Complexification H) :
    B z = mk (restrictBounded B z.re) (restrictBounded B z.im) := by
  calc
    B z = B (embedding z.re + Complex.I • embedding z.im) := congrArg B (decomposition z).symm
    _ = embedding (restrictBounded B z.re) + Complex.I • embedding (restrictBounded B z.im) := by
      rw [B.map_add, B.map_smul, restrictBounded_embedding B hB,
        restrictBounded_embedding B hB]
    _ = _ := decomposition (mk (restrictBounded B z.re) (restrictBounded B z.im))

variable [CompleteSpace H]

/-- The diagonal measure of a complexified vector splits into the two real
coordinate measures. No common control measure or separability is needed. -/
theorem measure_coordinates
    {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)}
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z))
    (C : MeasurableSpectralCalculus.BoundedRealization E) (z : Complexification H) :
    C.measure z = C.measure (embedding z.re) + C.measure (embedding z.im) := by
  apply Measure.ext
  intro B hB
  rw [Measure.add_apply, C.measure_apply _ _ hB, C.measure_apply _ _ hB,
    C.measure_apply _ _ hB]
  rw [bounded_coordinates (E B) (hE B hB) z,
    ← restrictBounded_embedding (E B) (hE B hB) z.re,
    ← restrictBounded_embedding (E B) (hE B hB) z.im]
  simp only [norm_sq, re_mk, im_mk, embedding.norm_map]
  exact ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)

end Complexification

namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)}
theorem unbounded_realCoefficient_integral
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (x : H)
    (y : (RealTransfer.realIntegral C f).domain)
    (hfi : (realCoefficientMeasure E x y).Integrable f) :
    inner ℝ x (RealTransfer.realIntegral C f y) =
      (realCoefficientMeasure E x y).integral f (ContinuousLinearMap.mul ℝ ℝ) := by
  have hm (n : ℕ) : Measurable (truncation f n) := by
    exact hf.indicator (measurableSet_le (continuous_abs.measurable.comp hf) measurable_const)
  have hb (n : ℕ) : IsBoundedMeasurable (truncation f n) := by
    refine ⟨hm n, n, fun s => ?_⟩
    classical
    by_cases hs : |f s| ≤ (n : ℝ)
    · simpa [truncation, hs] using hs
    · simp [truncation, hs]
  have hnorm (n : ℕ) (s : ℝ≥0) : ‖truncation f n s‖ ≤ |f s| := by
    classical
    by_cases hs : |f s| ≤ (n : ℝ) <;> simp [truncation, hs, Real.norm_eq_abs]
  have ht (s : ℝ≥0) : Tendsto (fun n => truncation f n s) atTop (nhds (f s)) := by
    obtain ⟨N, hN⟩ := exists_nat_ge |f s|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hs : |f s| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
    simp [truncation, hs]
  have hright : Tendsto
      (fun n => (realCoefficientMeasure E x y).integral (truncation f n)
        (ContinuousLinearMap.mul ℝ ℝ)) atTop
      (nhds ((realCoefficientMeasure E x y).integral f (ContinuousLinearMap.mul ℝ ℝ))) := by
    apply VectorMeasure.tendsto_integral_of_dominated_convergence (fun s => |f s|)
    · exact fun n => (hm n).stronglyMeasurable.aestronglyMeasurable
    · exact hfi.norm
    · exact fun n => Eventually.of_forall (hnorm n)
    · exact Eventually.of_forall ht
  have hc : Continuous (fun z : H => inner ℝ x z) := continuous_const.inner continuous_id
  have hleft := (hc.tendsto _).comp (RealTransfer.realIntegral_truncation_limit C f y)
  have heq (n : ℕ) := bounded_realCoefficient_integral E C (truncation f n) (hb n) x (y : H)
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n => (heq n).symm))

end Complexification

namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)}
/-- Bounded convergence for real spectral multipliers follows from the
separate real diagonal hypotheses, including on arbitrary complex vectors. -/
theorem realBounded_strong_convergence
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z))
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ≥0 → ℝ) (a : ℕ → ℝ≥0 → ℝ)
    (hf : IsBoundedMeasurable f) (ha : ∀ n, IsBoundedMeasurable (a n))
    (hb : ∃ M : ℝ, ∀ n s, |a n s| ≤ M)
    (hlim : ∀ x : H, ∀ᵐ s ∂C.measure (embedding x),
      Tendsto (fun n => a n s) atTop (nhds (f s))) :
    ∀ x : H, Tendsto (fun n => realBounded C (a n) x) atTop
      (nhds (realBounded C f x)) := by
  have hlim' (z : Complexification H) : ∀ᵐ s ∂C.measure z,
      Tendsto (fun n => complexSymbol (a n) s) atTop (nhds (complexSymbol f s)) := by
    rw [measure_coordinates hE C z, ae_add_measure_iff]
    constructor
    · filter_upwards [hlim z.re] with s hs
      exact Complex.continuous_ofReal.tendsto (f s) |>.comp hs
    · filter_upwards [hlim z.im] with s hs
      exact Complex.continuous_ofReal.tendsto (f s) |>.comp hs
  have hbc : ∃ M : ℝ, ∀ n s, ‖complexSymbol (a n) s‖ ≤ M := by
    simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs] using hb
  have h := StrongConvergenceWork.bounded_strong_convergence C
    (complexSymbol f) (fun n => complexSymbol (a n))
    (boundedMeasurable_complexSymbol hf) (fun n => boundedMeasurable_complexSymbol (ha n))
    hbc hlim'
  intro x
  exact ((continuous_fst.comp coordinates.continuous).tendsto _).comp (h (embedding x))

end Complexification

namespace Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem realCoefficient_integrable_of_domain
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H))
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (x y : H)
    (hy : embedding y ∈ (MeasurableSpectralCalculus.measurableIntegral C
      (fun s => (f s : ℂ))).domain) :
    (realCoefficientMeasure E x y).Integrable f := by
  let ν := realCoefficientMeasure E x y
  let z : (MeasurableSpectralCalculus.measurableIntegral C
      (fun s => (f s : ℂ))).domain := ⟨embedding y, hy⟩
  have hfc : Measurable (fun s => (f s : ℂ)) := Complex.measurable_ofReal.comp hf
  have htrunc (n : ℕ) : MeasurableSpectralCalculus.truncation
      (fun s => (f s : ℂ)) n = fun s => (truncation f n s : ℂ) := by
    classical
    funext s
    by_cases hs : |f s| ≤ (n : ℝ) <;>
      simp [MeasurableSpectralCalculus.truncation, truncation, Complex.norm_real,
        Real.norm_eq_abs, hs]
  have htm (n : ℕ) : Measurable (truncation f n) := by
    have hm := Complex.measurable_re.comp
      (MeasurableSpectralCalculus.boundedMeasurable_truncation hfc n).1
    simpa only [htrunc n, Function.comp_def, Complex.ofReal_re] using hm
  have htb (n : ℕ) : IsBoundedMeasurable (truncation f n) := by
    refine ⟨htm n, n, fun s => ?_⟩
    have hh := MeasurableSpectralCalculus.norm_truncation_le
      (fun s => (f s : ℂ)) n s
    simpa only [htrunc n, Complex.norm_real, Real.norm_eq_abs] using hh
  have hnorm_le (n : ℕ) :
      ‖C.integral (fun s => (truncation f n s : ℂ)) (embedding y)‖ ≤
        ‖MeasurableSpectralCalculus.measurableIntegral C (fun s => (f s : ℂ)) z‖ := by
    simpa only [htrunc n] using
      MeasurableSpectralCalculus.norm_integral_truncation_le C hfc z n
  let K := ‖x‖ * ‖MeasurableSpectralCalculus.measurableIntegral C (fun s => (f s : ℂ)) z‖
  have hbound (n : ℕ) : (∫ s, |truncation f n s| ∂ν.variation) ≤ K := by
    exact (bounded_realCoefficient_variation_bound E C _ (htb n) x y).trans
      (mul_le_mul_of_nonneg_left (hnorm_le n) (norm_nonneg x))
  have htn (n : ℕ) : Integrable (fun s => |truncation f n s|) ν.variation := by
    exact (bounded_realCoefficient_integrable E _ (htb n) x y).norm
  have hlim (s : ℝ≥0) : Tendsto (fun n => truncation f n s) atTop (𝓝 (f s)) := by
    have hh := Complex.continuous_re.tendsto _ |>.comp
      (MeasurableSpectralCalculus.truncation_tendsto (fun s => (f s : ℂ)) s)
    simpa only [htrunc, Function.comp_def, Complex.ofReal_re] using hh
  have hmono (s : ℝ≥0) : Monotone (fun n => |truncation f n s|) := by
    intro n m hnm
    change |truncation f n s| ≤ |truncation f m s|
    by_cases hn : |f s| ≤ (n : ℝ)
    · have hm : |f s| ≤ (m : ℝ) := hn.trans (by exact_mod_cast hnm)
      simp [truncation, hn, hm]
    · have hz : truncation f n s = 0 := by simp [truncation, hn]
      rw [hz, abs_zero]
      exact abs_nonneg _
  have hMCT : Tendsto (fun n => ∫⁻ s, ENNReal.ofReal |truncation f n s| ∂ν.variation)
      atTop (𝓝 (∫⁻ s, ENNReal.ofReal |f s| ∂ν.variation)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (ENNReal.measurable_ofReal.comp (by
        simpa only [Real.norm_eq_abs] using (htm n).norm)).aemeasurable
    · exact Eventually.of_forall fun s n m hnm => ENNReal.ofReal_le_ofReal (hmono s hnm)
    · exact Eventually.of_forall fun s =>
        (ENNReal.continuous_ofReal.tendsto _).comp ((hlim s).norm)
  have hfinite : (∫⁻ s, ENNReal.ofReal |f s| ∂ν.variation) ≤ ENNReal.ofReal K := by
    apply le_of_tendsto hMCT
    exact Eventually.of_forall fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (htn n)
        (Eventually.of_forall fun s => abs_nonneg (truncation f n s))]
      exact ENNReal.ofReal_le_ofReal (hbound n)
  refine ⟨hf.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs] using hfinite.trans_lt ENNReal.ofReal_lt_top



end Complexification

section CalculusConstruction
open Complexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (Complexification H)}

def calculusFromResolution (C : MeasurableSpectralCalculus.BoundedRealization E)
    (hE : ∀ B, MeasurableSet B → ∀ z, E B (conjugation z) = conjugation (E B z))
    :
    Calculus (H := H) where
  E := restrictPVM E hE
  measure x := C.measure (embedding x)
  coefficient := realCoefficientMeasure E
  finite x := C.finite (embedding x)
  measure_apply x B hB := by
    rw [RealTransfer.realization_measure_eq_diagonalMeasure C]
    exact realDiagonalMeasure_apply E x B hB
  coefficient_apply := realCoefficientMeasure_apply E
  bounded := realBounded C
  integral := RealTransfer.realIntegral C
  bounded_one := realBounded_one C
  bounded_add _ _ := realBounded_add C
  bounded_smul a _ := realBounded_smul C a
  bounded_mul _ _ := realBounded_mul C hE
  bounded_adjoint _ := realBounded_adjoint C
  bounded_indicator := realBounded_indicator C
  bounded_bound f M hf hM hb := realBounded_bound C hf hM hb
  bounded_agrees := realIntegral_bounded_eq C
  strong_convergence := realBounded_strong_convergence hE C
  domain := RealTransfer.realIntegral_domain C
  dense := RealTransfer.realIntegral_dense hE C
  closed := RealTransfer.realIntegral_isClosed hE C
  selfAdjoint := RealTransfer.realIntegral_selfAdjoint hE C
  truncation_limit f _ := RealTransfer.realIntegral_truncation_limit C f
  norm_sq := RealTransfer.realIntegral_norm_sq hE C
  inner_integrable f hf x y :=
    realCoefficient_integrable_of_domain E C f hf x y y.property
  inner_integral f hf x y := unbounded_realCoefficient_integral C f hf x y
    (realCoefficient_integrable_of_domain E C f hf x y y.property)
  nonnegative := RealTransfer.realIntegral_nonnegative hE C
  product_domain f g hf hg := (realIntegral_product_rule C f g hf hg
    (realMeasurableIntegral_invariant E hE C g hg)).1
  product_le f g hf hg := (realIntegral_product_rule C f g hf hg
    (realMeasurableIntegral_invariant E hE C g hg)).2
  domain_bound := RealTransfer.realIntegral_domain_growth C
  bounded_commutes f g hf hg := realIntegral_bounded_commutes C f g hf hg
    (realMeasurableIntegral_invariant E hE C f hf) (realIntegral_commutes E hE C g hg)


end CalculusConstruction

@[fun_prop] theorem continuous_coordinate : Continuous coordinate := continuous_subtype_val
@[fun_prop] theorem continuous_root : Continuous root := Real.continuous_sqrt.comp continuous_coordinate
@[fun_prop] theorem continuous_cosine (t : ℝ) : Continuous (cosine t) := by
  unfold cosine
  fun_prop
@[fun_prop] theorem continuous_sine (t : ℝ) : Continuous (sine t) := by
  unfold sine
  fun_prop

@[simp] theorem root_zero : root 0 = 0 := by simp [root]
@[simp] theorem root_sq (s : ℝ≥0) : root s ^ 2 = coordinate s := Real.sq_sqrt s.2
@[simp] theorem root_mul_root : root * root = coordinate := by
  funext s
  simpa only [Pi.mul_apply, ← pow_two] using root_sq s

@[simp] theorem quotientSine_zero (t : ℝ) : quotientSine t 0 = t := by
  simp [quotientSine]

/-- Sinc gives the zero-frequency extension and its global time bound. -/
theorem quotientSine_eq_sinc (t : ℝ) (s : ℝ≥0) :
    quotientSine t s = t * Real.sinc (t * root s) := by
  by_cases hs : s = 0
  · simp [hs]
  by_cases ht : t = 0
  · simp [quotientSine, ht]
  have hr : root s ≠ 0 := by
    intro h
    have he := root_sq s
    rw [h, zero_pow (by decide)] at he
    exact hs (NNReal.coe_eq_zero.mp he.symm)
  rw [quotientSine, ite_eq_right hs, Real.sinc_of_ne_zero (mul_ne_zero ht hr)]
  field_simp

@[fun_prop] theorem continuous_quotientSine (t : ℝ) : Continuous (quotientSine t) := by
  have he : quotientSine t = fun s => t * Real.sinc (t * root s) :=
    funext (quotientSine_eq_sinc t)
  rw [he]
  fun_prop

theorem abs_quotientSine_le (t : ℝ) (s : ℝ≥0) : |quotientSine t s| ≤ |t| := by
  rw [quotientSine_eq_sinc, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (t * root s)) (abs_nonneg t)

theorem boundedMeasurable_cosine (t : ℝ) : IsBoundedMeasurable (cosine t) :=
  ⟨(continuous_cosine t).measurable, 1, fun _ => Real.abs_cos_le_one _⟩
theorem boundedMeasurable_sine (t : ℝ) : IsBoundedMeasurable (sine t) :=
  ⟨(continuous_sine t).measurable, 1, fun _ => Real.abs_sin_le_one _⟩
theorem boundedMeasurable_quotientSine (t : ℝ) : IsBoundedMeasurable (quotientSine t) :=
  ⟨(continuous_quotientSine t).measurable, |t|, abs_quotientSine_le t⟩

@[simp] theorem root_mul_quotientSine (t : ℝ) : root * quotientSine t = sine t := by
  funext s
  by_cases hs : s = 0
  · simp [hs, sine]
  have hr : root s ≠ 0 := by
    intro h
    have he := root_sq s
    rw [h, zero_pow (by decide)] at he
    exact hs (NNReal.coe_eq_zero.mp he.symm)
  simp only [Pi.mul_apply, quotientSine, ite_eq_right hs, sine]
  exact mul_div_cancel₀ _ hr

/-- Scalar rotation law needed in the energy identity, including λ=0. -/
theorem cosine_sq_add_sine_sq (t : ℝ) (s : ℝ≥0) :
    cosine t s ^ 2 + sine t s ^ 2 = 1 := by
  simpa only [cosine, sine, add_comm] using Real.sin_sq_add_cos_sq (t * root s)

section CalculusConsequences
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Product equality includes the exact domain; no closure is taken. -/
theorem squareRoot_square (C : Calculus (H := H)) :
    OperatorDomainsSpec.productValue (squareRoot C) (squareRoot C) = C.integral coordinate := by
  have hdom : (C.integral coordinate).domain ≤ (C.integral root).domain := by
    apply C.domain_bound root coordinate continuous_root.measurable continuous_coordinate.measurable
    refine ⟨1, 1, zero_le_one, zero_le_one, fun s => ?_⟩
    rw [sq_abs, root_sq, sq_abs]
    have hs := sq_nonneg (coordinate s - 1 / 2)
    nlinarith
  apply LinearPMap.eq_of_le_of_domain_eq
  · simpa only [squareRoot, root_mul_root] using
      C.product_le root root continuous_root.measurable continuous_root.measurable
  · simpa only [squareRoot, root_mul_root, inf_eq_right.mpr hdom] using
      C.product_domain root root continuous_root.measurable continuous_root.measurable

/-- For a symmetric real operator the kernel of its square equals its kernel.
The proof uses actual product evaluation and inner-product definiteness. -/
theorem squareRoot_ker (C : Calculus (H := H)) :
    (squareRoot C).ker = (C.integral coordinate).ker := by
  let S := squareRoot C
  have hs : S.IsFormalAdjoint S := by
    have h := LinearPMap.adjoint_isFormalAdjoint (C.dense root continuous_root.measurable)
    rw [C.selfAdjoint root continuous_root.measurable] at h
    exact h
  rw [← squareRoot_square C]
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hz⟩ := (mem_kernel_iff S x).mp hx
    have hSx : S ⟨x, hx⟩ ∈ S.domain := by rw [hz]; exact S.domain.zero_mem
    apply (mem_kernel_iff (OperatorDomainsSpec.productValue S S) x).mpr
    refine ⟨⟨hx, hSx⟩, ?_⟩
    rw [product_apply S S ⟨x, hx⟩ hSx]
    simp only [hz]
    change S (0 : S.domain) = 0
    exact S.map_zero
  · intro hx
    obtain ⟨hx, hz⟩ := (mem_kernel_iff (OperatorDomainsSpec.productValue S S) x).mp hx
    obtain ⟨hxd, hSd⟩ := (mem_product_domain_iff S S x).mp hx
    have hh := hs ⟨x, hxd⟩ ⟨S ⟨x, hxd⟩, hSd⟩
    have hSS : S ⟨S ⟨x, hxd⟩, hSd⟩ = 0 := by
      rw [← product_apply S S ⟨x, hxd⟩ hSd]
      exact hz
    rw [hSS, inner_zero_right] at hh
    exact (mem_kernel_iff S x).mpr ⟨hxd, inner_self_eq_zero.mp hh⟩

/-- A bounded symbol with bounded product maps all of H to the maximal
unbounded domain. This is a consequence of the exact product rule. -/
theorem bounded_product_graph (C : Calculus (H := H))
    {f g : ℝ≥0 → ℝ} (hf : Measurable f)
    (hg : IsBoundedMeasurable g) (hfg : IsBoundedMeasurable (f * g)) (x : H) :
    (C.bounded g x, C.bounded (f * g) x) ∈ (C.integral f).graph := by
  let A := C.integral f
  let B := C.integral g
  let P := OperatorDomainsSpec.productValue A B
  have hBdom : B.domain = ⊤ := by rw [show B = _ from C.bounded_agrees g hg]; rfl
  have hDdom : (C.integral (f * g)).domain = ⊤ := by
    rw [C.bounded_agrees (f * g) hfg]; rfl
  have hPdom : P.domain = ⊤ := by
    rw [show P.domain = _ from C.product_domain f g hf hg.1, hBdom, hDdom, inf_top_eq]
  have hxP : x ∈ P.domain := hPdom.symm ▸ Submodule.mem_top
  obtain ⟨hxB, hxA⟩ := (mem_product_domain_iff A B x).mp hxP
  have heB : B ⟨x, hxB⟩ = C.bounded g x :=
    (LinearPMap.ext_iff.mp (C.bounded_agrees g hg)).2 (hg := Submodule.mem_top)
  have heP : P ⟨x, hxP⟩ = C.bounded (f * g) x := by
    calc
      P ⟨x, hxP⟩ = C.integral (f * g)
          ⟨x, (C.product_le f g hf hg.1).1 hxP⟩ := (C.product_le f g hf hg.1).2 rfl
      _ = _ := (LinearPMap.ext_iff.mp (C.bounded_agrees (f * g) hfg)).2
        (hg := Submodule.mem_top)
  have heA : A ⟨B ⟨x, hxB⟩, hxA⟩ = C.bounded (f * g) x := by
    rw [← product_apply A B ⟨x, hxB⟩ hxA]
    exact heP
  exact A.mem_graph_iff.mpr ⟨⟨B ⟨x, hxB⟩, hxA⟩, heB, heA⟩

theorem wave_laws (C : Calculus (H := H)) (L : Operator ℝ H H)
    (hL : C.integral coordinate = L) : WaveLaws C L := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (squareRoot_square C).trans hL
  · rw [← hL]
    exact squareRoot_ker C
  · exact C.nonnegative root continuous_root.measurable (fun _ => Real.sqrt_nonneg _)
  · intro t
    exact ⟨C.bounded_bound _ 1 (boundedMeasurable_cosine t) zero_le_one
        (fun _ => Real.abs_cos_le_one _),
      C.bounded_bound _ 1 (boundedMeasurable_sine t) zero_le_one
        (fun _ => Real.abs_sin_le_one _),
      C.bounded_bound _ |t| (boundedMeasurable_quotientSine t) (abs_nonneg t)
        (abs_quotientSine_le t)⟩
  · intro t x
    have hh := bounded_product_graph C continuous_root.measurable
      (boundedMeasurable_quotientSine t)
      (by simpa only [root_mul_quotientSine] using boundedMeasurable_sine t) x
    simpa only [root_mul_quotientSine, squareRoot, quotientOperator, sinOperator] using hh
  · intro t x
    exact ⟨C.bounded_commutes root (cosine t) continuous_root.measurable
        (boundedMeasurable_cosine t) x,
      C.bounded_commutes root (sine t) continuous_root.measurable
        (boundedMeasurable_sine t) x⟩

end CalculusConsequences

theorem wave_consequences : Spec.WaveConsequences.{u} := wave_laws

/-- The real spectral calculus is obtained by complexification, spectral
conjugation invariance, nonnegative support and restriction to real vectors. -/
theorem spectral_existence : Spec.SpectralExistence.{u} := by
  intro H _ _ _ L hL
  obtain ⟨E, C, hE, hC⟩ := nonnegative_spectral_resolution L hL
  refine ⟨calculusFromResolution C hE, ?_⟩
  change Complexification.restrictOperator
    (MeasurableSpectralCalculus.measurableIntegral C
      (fun s : ℝ≥0 => ((s : ℝ) : ℂ))) = L
  rw [hC, Complexification.restrictOperator_operator]

theorem real_nonnegative_spectral_calculus : Spec.FullTheorem.{u} := by
  intro H _ _ _ L hL
  obtain ⟨C, hC⟩ := spectral_existence H L hL
  exact ⟨C, hC, wave_laws C L hC⟩

end ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
