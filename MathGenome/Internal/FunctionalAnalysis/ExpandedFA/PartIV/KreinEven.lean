import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinEven
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinKernelPlus
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators Topology InnerProductSpace Convolution ComplexConjugate

namespace ExpandedFA.PartIV.KreinEven
open KreinSolutions.Specs

/-- The single positive-half-line moment gives a uniform compact majorant.
No uniqueness or positive-mass hypothesis is used. -/
theorem compact_domination : Spec.CompactDomination := by
  intro p ν h R hR
  let := h.1
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).piecewise
    (fun ξ => Real.cosh (R * Real.sqrt ξ)) (fun _ => 1)
  refine ⟨g, Integrable.piecewise measurableSet_Ioi.nullMeasurableSet
    (h.2.2.2 R hR) (integrable_const 1).integrableOn, ?_⟩
  intro ξ s hs
  by_cases hn : ξ < 0
  · simp only [CValue, hn, ↓reduceIte]
    exact (Real.abs_cos_le_one _).trans (by simp [g, not_lt_of_gt hn])
  · by_cases hz : ξ = 0
    · subst ξ
      simp [CValue, g]
    · have hp : 0 < ξ := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp only [CValue, hn, hz, ↓reduceIte, abs_of_pos (Real.cosh_pos _)]
      simp only [g, Set.piecewise, mem_Ioi, hp, ↓reduceIte]
      change Real.cosh (Real.sqrt ξ * s) ≤ Real.cosh (R * Real.sqrt ξ)
      apply Real.cosh_le_cosh.mpr
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (mul_nonneg hR.le (Real.sqrt_nonneg _))]
      nlinarith [mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg ξ)]

/-- Linearity of the integral and the addition formula identify the represented
kernel with an integral of rank-one kernels. -/
theorem represented_kernel {p : ℝ → ℝ} {ν : Measure ℝ}
    (h : Spec.Represents p ν) (s t : ℝ) :
    Integrable (fun ξ => CValue ξ s * CValue ξ t) ν ∧
    KernelPlusValue p s t = ∫ ξ, CValue ξ s * CValue ξ t ∂ν := by
  have ha := (h.2.2.1 (s-t)).1
  have hb := (h.2.2.1 (s+t)).1
  have he : (fun ξ => (CValue ξ (s-t) + CValue ξ (s+t)) / 2) =
      (fun ξ => CValue ξ s * CValue ξ t) := by
    funext ξ
    rw [KreinSolutions.additionSum]
    ring
  constructor
  · rw [← he]
    exact (ha.add hb).div_const 2
  · rw [KernelPlusValue, (h.2.2.1 _).2, (h.2.2.1 _).2,
      ← integral_add ha hb, ← integral_div, he]

/-- Every represented kernel has nonnegative finite quadratic sums. -/
theorem representation_positive_kernel {p : ℝ → ℝ} {ν : Measure ℝ}
    (h : Spec.Represents p ν) : PositiveDefiniteValue (KernelPlusValue p) := by
  constructor
  · intro s t
    rw [(represented_kernel h s t).2, (represented_kernel h t s).2]
    congr 1
    funext ξ
    ring
  · intro n x a
    have hi (i j : Fin n) : Integrable
        (fun ξ => a i * a j * (CValue ξ (x i) * CValue ξ (x j))) ν :=
      (represented_kernel h _ _).1.const_mul _
    calc
      0 ≤ ∫ ξ, (∑ i, a i * CValue ξ (x i)) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
      _ = ∫ ξ, ∑ i, ∑ j, a i * a j * (CValue ξ (x i) * CValue ξ (x j)) ∂ν := by
        congr 1
        funext ξ
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, a i * a j * KernelPlusValue p (x i) (x j) := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum _ (fun j _ => hi i j)]
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul, (represented_kernel h _ _).2]

/-- The upstream spectral theorem and the rank-one converse. -/
theorem kernel_representation : Spec.KernelRepresentation := by
  intro p hp he
  constructor
  · exact KreinKernelPlus.kernel_plus p hp he
  · rintro ⟨ν, hν⟩
    exact representation_positive_kernel hν

lemma measurable_C (s : ℝ) : Measurable (fun ξ => CValue ξ s) := by
  unfold CValue
  exact Measurable.ite measurableSet_Iio (by fun_prop)
    (Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop))

lemma C_neg_square (a s : ℝ) : CValue (-(a ^ 2)) s = Real.cos (a * s) := by
  by_cases ha : a = 0
  · simp [ha, CValue]
  · have hn : -(a ^ 2) < 0 := neg_neg_of_pos (sq_pos_of_ne_zero ha)
    simp only [CValue, hn, ↓reduceIte, neg_neg, Real.sqrt_sq_eq_abs]
    rcases le_total 0 a with hp | hp
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hp, neg_mul, Real.cos_neg]

lemma C_square (a s : ℝ) : CValue (a ^ 2) s = Real.cosh (a * s) := by
  by_cases ha : a = 0
  · simp [ha, CValue]
  · have hp : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    simp only [CValue, not_lt_of_ge hp.le, ne_of_gt hp, ↓reduceIte,
      Real.sqrt_sq_eq_abs]
    rcases le_total 0 a with hp | hp
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hp, neg_mul, Real.cosh_neg]

/-- The hyperbolic moment follows already from absolute integrability at R. -/
lemma positive_moment_of_integrable {ν : Measure ℝ} {R : ℝ}
    (h : Integrable (fun ξ => CValue ξ R) ν) :
    IntegrableOn (fun ξ => Real.cosh (R * Real.sqrt ξ)) (Ioi 0) ν := by
  apply h.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hp : 0 < ξ := hξ
  simp [CValue, not_lt_of_gt hp, ne_of_gt hp, mul_comm]

/-- Push a spectral measure onto the two actual frequency half-lines. -/
theorem mixture_of_representation {p : ℝ → ℝ} {ν : Measure ℝ}
    (h : Spec.Represents p ν) : ∃ α β : Measure ℝ, Spec.Mixture p α β := by
  let := h.1
  let f : ℝ → ℝ := fun ξ => Real.sqrt (-ξ)
  let g : ℝ → ℝ := Real.sqrt
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  let α : Measure ℝ := (ν.restrict (Iic 0)).map f
  let β : Measure ℝ := (ν.restrict (Ioi 0)).map g
  have hα : IsFiniteMeasure α := inferInstance
  have hβ : IsFiniteMeasure β := inferInstance
  have hca (s : ℝ) : (fun ξ => Real.cos (f ξ * s)) =ᵐ[ν.restrict (Iic 0)]
      (fun ξ => CValue ξ s) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with ξ hξ
    by_cases hn : ξ < 0
    · simp [f, CValue, hn]
    · have hz : ξ = 0 := le_antisymm hξ (le_of_not_gt hn)
      simp [hz, f, CValue]
  have hcb (s : ℝ) : (fun ξ => Real.cosh (g ξ * s)) =ᵐ[ν.restrict (Ioi 0)]
      (fun ξ => CValue ξ s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have hp : 0 < ξ := hξ
    simp [g, CValue, not_lt_of_gt hp, ne_of_gt hp]
  have hia (s : ℝ) : Integrable (fun a => Real.cos (a * s)) α := by
    apply (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr
    exact (h.2.2.1 s).1.integrableOn.congr (hca s).symm
  have hib (s : ℝ) : Integrable (fun b => Real.cosh (b * s)) β := by
    apply (integrable_map_measure (by fun_prop) hg.aemeasurable).mpr
    exact (h.2.2.1 s).1.integrableOn.congr (hcb s).symm
  have heq (s : ℝ) : p s = (∫ a, Real.cos (a * s) ∂α) +
      ∫ b, Real.cosh (b * s) ∂β := by
    rw [integral_map hf.aemeasurable (by fun_prop),
      integral_map hg.aemeasurable (by fun_prop),
      integral_congr_ae (hca s), integral_congr_ae (hcb s)]
    have hu : ν.restrict (Iic (0 : ℝ)) + ν.restrict (Ioi 0) = ν := by
      simpa only [compl_Iic] using ν.restrict_add_restrict_compl measurableSet_Iic
    rw [← integral_add_measure (h.2.2.1 s).1.integrableOn
      (h.2.2.1 s).1.integrableOn, hu]
    exact (h.2.2.1 s).2
  refine ⟨α, β, hα, hβ, ?_, ?_, ?_, fun s => ⟨hia s, hib s, heq s⟩, ?_⟩
  · rw [Measure.map_apply hf measurableSet_Iio]
    have hz : f ⁻¹' Iio 0 = ∅ := by
      ext ξ
      simp [f, not_lt_of_ge (Real.sqrt_nonneg (-ξ))]
    rw [hz, measure_empty]
  · rw [Measure.map_apply hg measurableSet_Iic, Measure.restrict_apply (hg measurableSet_Iic)]
    have hz : g ⁻¹' Iic 0 ∩ Ioi 0 = ∅ := by
      ext ξ
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_empty_iff_false,
        iff_false, not_and]
      intro hξ hp
      exact (not_le_of_gt (Real.sqrt_pos.mpr hp)) hξ
    rw [hz, measure_empty]
  · simpa only [mul_zero, Real.cos_zero, Real.cosh_zero, integral_const, smul_eq_mul,
      mul_one] using (heq 0).symm
  · intro R hR
    simpa only [mul_comm R] using hib R

/-- Squaring the frequencies reconstructs a spectral parameter measure.
The zero atom in the cosh part is excluded by the definition of Mixture. -/
theorem representation_of_mixture {p : ℝ → ℝ} {α β : Measure ℝ}
    (h : Spec.Mixture p α β) : ∃ ν : Measure ℝ, Spec.Represents p ν := by
  let := h.1
  let := h.2.1
  let f : ℝ → ℝ := fun a => -(a ^ 2)
  let g : ℝ → ℝ := fun b => b ^ 2
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  let ν : Measure ℝ := α.map f + β.map g
  have hia (s : ℝ) : Integrable (fun ξ => CValue ξ s) (α.map f) := by
    apply (integrable_map_measure (measurable_C s).aestronglyMeasurable hf.aemeasurable).mpr
    simpa only [Function.comp_def, f, C_neg_square] using (h.2.2.2.2.2.1 s).1
  have hib (s : ℝ) : Integrable (fun ξ => CValue ξ s) (β.map g) := by
    apply (integrable_map_measure (measurable_C s).aestronglyMeasurable hg.aemeasurable).mpr
    simpa only [Function.comp_def, g, C_square] using (h.2.2.2.2.2.1 s).2.1
  have hi (s : ℝ) : Integrable (fun ξ => CValue ξ s) ν :=
    integrable_add_measure.mpr ⟨hia s, hib s⟩
  have heq (s : ℝ) : p s = ∫ ξ, CValue ξ s ∂ν := by
    rw [integral_add_measure (hia s) (hib s),
      integral_map hf.aemeasurable (measurable_C s).aestronglyMeasurable,
      integral_map hg.aemeasurable (measurable_C s).aestronglyMeasurable]
    simpa only [f, g, C_neg_square, C_square] using (h.2.2.2.2.2.1 s).2.2
  refine ⟨ν, inferInstance, ?_, fun s => ⟨hi s, heq s⟩,
    fun R _ => positive_moment_of_integrable (hi R)⟩
  have hz : ∀ ξ : ℝ, CValue ξ 0 = 1 := by intro ξ; simp [CValue]
  simpa only [hz, integral_const, smul_eq_mul, mul_one] using (heq 0).symm

/-- Both frequency transports, including the mass and moment conditions. -/
theorem mixture_equivalence : Spec.MixtureEquivalence := by
  intro p
  constructor
  · rintro ⟨ν, h⟩
    exact mixture_of_representation h
  · rintro ⟨α, β, h⟩
    exact representation_of_mixture h


/-- Continuously smoothed kernels approximate p even when p is unbounded. -/
lemma double_smoothing_tendsto (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (p : ℝ → ℝ) (hp : Continuous p) (x : ℝ) :
    Tendsto (fun n => ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume]
      ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] p)) x) atTop (𝓝 (p x)) := by
  apply ContDiffBump.convolution_tendsto_right hφ
  · apply Eventually.of_forall
    intro n
    exact ((φ n).hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
      (φ n).continuous_normed hp.locallyIntegrable).aestronglyMeasurable
  · exact ContDiffBump.convolution_tendsto_right
      (φ := fun z : ℕ × ℝ => φ z.1) (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hp.aestronglyMeasurable)
      ((hp.tendsto x).comp tendsto_snd) tendsto_snd
  · exact tendsto_const_nhds

lemma double_bump_integral (φ : ContDiffBump (0 : ℝ)) (p : ℝ → ℝ) (x y : ℝ) :
    (∫ s, ∫ t, p (s-t) * φ.normed volume (s-x) * φ.normed volume (t-y)) =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume]
        (φ.normed volume ⋆[lsmul ℝ ℝ, volume] p)) (x-y) := by
  have hi (s : ℝ) : (∫ t, p (s-t) * φ.normed volume (s-x) * φ.normed volume (t-y)) =
      φ.normed volume (s-x) * ∫ t, p (s-t) * φ.normed volume (t-y) := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  simp_rw [hi]
  rw [← integral_sub_left_eq_self (fun s => φ.normed volume (s-x) *
    ∫ t, p (s-t) * φ.normed volume (t-y)) volume x]
  simp only [sub_sub_cancel_left, φ.normed_neg]
  rw [convolution_def]
  congr 1
  funext s
  simp only [lsmul_apply, smul_eq_mul]
  congr 1
  rw [← integral_add_left_eq_self (fun t => p (x-s-t) * φ.normed volume (t-y)) y]
  simp only [add_sub_cancel_left]
  rw [convolution_def]
  congr 1
  funext t
  simp only [lsmul_apply, smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring


lemma real_weighted_integrable (p : ℝ → ℝ) (hp : Continuous p)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun z : ℝ × ℝ => p (z.1-z.2) * f z.1 * g z.2)
      (volume.prod volume) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · apply HasCompactSupport.intro (hfc.isCompact.prod hgc.isCompact)
    rintro ⟨s,t⟩ h
    by_cases hs : s ∈ tsupport f
    · have ht : t ∉ tsupport g := by simpa only [mem_prod, hs, true_and] using h
      simp [image_eq_zero_of_notMem_tsupport ht]
    · simp [image_eq_zero_of_notMem_tsupport hs]

lemma bump_translate_compact (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    HasCompactSupport (fun s => φ.normed volume (s-x)) := by
  simpa [Function.comp_def, sub_eq_add_neg] using
    (φ.hasCompactSupport_normed (μ := volume)).comp_homeomorph (Homeomorph.addRight (-x))

lemma finite_bump_integral {ι : Type*} [Fintype ι]
    (φ : ContDiffBump (0 : ℝ)) (p : ℝ → ℝ) (hp : Continuous p) (x a : ι → ℝ) :
    (∫ s, ∫ t, p (s-t) * (∑ i, a i * φ.normed volume (s-x i)) *
      (∑ j, a j * φ.normed volume (t-x j))) =
    ∑ i, ∑ j, a i * a j *
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume]
        (φ.normed volume ⋆[lsmul ℝ ℝ, volume] p)) (x i-x j) := by
  have hc (i : ι) : Continuous (fun s => φ.normed volume (s-x i)) :=
    φ.continuous_normed.comp (continuous_id.sub continuous_const)
  have hi (i j : ι) := real_weighted_integrable p hp _ _ (hc i) (hc j)
    (bump_translate_compact φ (x i)) (bump_translate_compact φ (x j))
  have hi' (i j : ι) (s : ℝ) : Integrable
      (fun t => p (s-t) * φ.normed volume (s-x i) * φ.normed volume (t-x j)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact (bump_translate_compact φ (x j)).mul_left
  have he (s t : ℝ) : p (s-t) * (∑ i, a i * φ.normed volume (s-x i)) *
      (∑ j, a j * φ.normed volume (t-x j)) =
      ∑ i, ∑ j, a i * a j *
        (p (s-t) * φ.normed volume (s-x i) * φ.normed volume (t-x j)) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  have hinner (s : ℝ) :
      (∫ t, ∑ i, ∑ j, a i * a j *
        (p (s-t) * φ.normed volume (s-x i) * φ.normed volume (t-x j))) =
      ∑ i, ∑ j, a i * a j *
        ∫ t, p (s-t) * φ.normed volume (s-x i) * φ.normed volume (t-x j) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hi' i j s).const_mul _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => (hi' i j s).const_mul _)]
    simp only [integral_const_mul]
  simp_rw [hinner]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hi i j).integral_prod_left.const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hi i j).integral_prod_left.const_mul _)]
  simp only [integral_const_mul, double_bump_integral]


/-- Finite symmetrized point masses are approached by genuine even continuous
compact tests. Double smoothing handles the diagonal sequence of radii. -/
theorem kernel_positive_of_test {p : ℝ → ℝ} (hp : Continuous p)
    (he : Function.Even p) (htest : Spec.EvenTestPositive p) :
    PositiveDefiniteValue (KernelPlusValue p) := by
  refine ⟨(KreinSolutions.kernelRegularity p hp he).1.2, ?_⟩
  intro m x a
  let φ := KreinKernelPlus.shrinkingBump
  let c : Fin m × Bool → ℝ := fun i => if i.2 then x i.1 else -x i.1
  let d : Fin m × Bool → ℝ := fun i => a i.1
  let f (n : ℕ) (s : ℝ) := ∑ i, d i * (φ n).normed volume (s-c i)
  have hf (n : ℕ) : Continuous (f n) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul ((φ n).continuous_normed.comp
      (continuous_id.sub continuous_const))
  have hfc (n : ℕ) : HasCompactSupport (f n) := by
    change HasCompactSupport (fun s => ∑ i, d i * (φ n).normed volume (s-c i))
    simpa only [Finset.sum_fn] using
      HasCompactSupport.finset_sum (s := Finset.univ)
        (f := fun i s => d i * (φ n).normed volume (s-c i))
        (fun i _ => (bump_translate_compact (φ n) (c i)).mul_left)
  have hfe (n : ℕ) : Function.Even (f n) := by
    intro s
    simp only [f, Fintype.sum_prod_type, Fintype.sum_bool, c, d, Bool.false_eq_true, ↓reduceIte, sub_neg_eq_add]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : -s-x i = -(s+x i) := by ring
    have h2 : -s+x i = -(s-x i) := by ring
    rw [h1, h2, (φ n).normed_neg, (φ n).normed_neg]
    ring
  have hnonneg (n : ℕ) : 0 ≤ ∑ i, ∑ j, d i * d j *
      ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume]
        ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] p)) (c i-c j) := by
    rw [← finite_bump_integral (φ n) p hp c d]
    exact htest (f n) (hf n) (hfe n) (hfc n)
  have hlim : Tendsto (fun n => ∑ i, ∑ j, d i * d j *
      ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume]
        ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] p)) (c i-c j)) atTop
      (𝓝 (∑ i, ∑ j, d i * d j * p (c i-c j))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (double_smoothing_tendsto φ KreinKernelPlus.shrinkingBump_radius
      p hp (c i-c j)).const_mul _
  have hpos : 0 ≤ ∑ i, ∑ j, d i * d j * p (c i-c j) :=
    ge_of_tendsto hlim (Eventually.of_forall hnonneg)
  have heq : (∑ i, ∑ j, d i * d j * p (c i-c j)) =
      4 * ∑ i, ∑ j, a i * a j * KernelPlusValue p (x i) (x j) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, c, d, Bool.false_eq_true, ↓reduceIte]
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h1 : p (-x i - x j) = p (x i+x j) := by
      rw [show -x i-x j = -(x i+x j) by ring, he]
    have h2 : p (-x i - -x j) = p (x i-x j) := by
      rw [show -x i - -x j = -(x i-x j) by ring, he]
    rw [h1, h2]
    simp only [sub_neg_eq_add, KernelPlusValue]
    ring
  rw [heq] at hpos
  linarith


theorem test_positive_of_kernel {p : ℝ → ℝ} (hp : Continuous p)
    (he : Function.Even p) (hK : PositiveDefiniteValue (KernelPlusValue p)) :
    Spec.EvenTestPositive p := by
  have hK' : PositiveDefiniteValue (KreinSymmetricOperator.Spec.kernel true p) := hK
  obtain ⟨H, hnorm, hinner, hcomplete, hsep, ⟨G⟩⟩ :=
    KreinSymmetricOperator.gram_space_exists true p hp he hK'
  let := hnorm
  let := hinner
  let := hcomplete
  intro f hf he hfcompact
  let fc : ℝ → ℂ := fun t => (f t : ℂ)
  have hfc : Continuous fc := Complex.continuous_ofReal.comp hf
  have hfcc : HasCompactSupport fc := hfcompact.comp_left (g := Complex.ofReal) (by simp)
  have hpar : ∀ t, fc (-t) = KreinSymmetricOperator.Spec.paritySign true * fc t := by
    intro t
    simp [fc, he t, KreinSymmetricOperator.Spec.paritySign]
  have h := KreinSymmetricOperator.inner_testIntegral_kernel_parity G hp fc fc
    hfc hfcc hfc hfcc hpar
  have hh : (∫ s, ∫ t, conj (fc s) * fc t * (p (s-t) : ℂ)) =
      ((∫ s, ∫ t, p (s-t) * f s * f t : ℝ) : ℂ) := by
    have heq : ∀ s t : ℝ, conj (fc s) * fc t * (p (s-t) : ℂ) =
        ((p (s-t) * f s * f t : ℝ) : ℂ) := by
      intro s t
      simp only [fc, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    simp_rw [heq]
    exact (integral_congr_ae (Eventually.of_forall fun _ => integral_ofReal)).trans
      integral_ofReal
  rw [hh] at h
  have hh' := congrArg Complex.re h
  change Complex.re _ = _ at hh'
  simp only [Complex.ofReal_re] at hh'
  rw [← hh']
  exact inner_self_nonneg (𝕜 := ℂ)

/-- Integral tests and all finite kernel tests are equivalent, without a
smoothness hypothesis on the original tests or any boundedness assumption on p. -/
theorem integral_kernel_equivalence : Spec.IntegralKernelEquivalence := by
  intro p hp he
  exact ⟨kernel_positive_of_test hp he, test_positive_of_kernel hp he⟩

/-- Krein's complete even-test representation. -/
theorem representation : Spec.Representation := by
  intro p hp he
  exact (integral_kernel_equivalence p hp he).trans (kernel_representation p hp he)

end ExpandedFA.PartIV.KreinEven
