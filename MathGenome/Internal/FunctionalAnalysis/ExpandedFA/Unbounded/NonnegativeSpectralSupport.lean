import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.NonnegativeSpectralSupport
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem

noncomputable section
open MeasureTheory Set

namespace ExpandedFA.Unbounded.NonnegativeSpectralSupport
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open MeasurableSpectralCalculus
open UnboundedNormalSpectralTheorem.SpectralRepresentation

/-- On an interval [a,b] with b<0, the localized operator differs from aI
by at most b-a. Its quadratic form therefore cannot be nonnegative unless
the whole spectral projection vanishes. -/
theorem negative_interval_null
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ H) (C : BoundedRealization E)
    (hnonneg : ∀ x : (measurableIntegral C (fun t : ℝ => (t : ℂ))).domain,
      0 ≤ (inner ℂ (x : H) (measurableIntegral C (fun t : ℝ => (t : ℂ)) x)).re)
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0) : E (Icc a b) = 0 := by
  classical
  let B := Icc a b
  let p : ℝ → ℂ := B.indicator (fun _ => 1)
  let f : ℝ → ℂ := B.indicator (fun t => (t : ℂ))
  let g : ℝ → ℂ := B.indicator (fun t => ((t - a : ℝ) : ℂ))
  have hB : MeasurableSet B := measurableSet_Icc
  have hp : SpectralMeasure.Spec.IsBoundedMeasurable p :=
    SpectralMeasure.BorelNormSpectrum.bounded_indicator B hB
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1)
  have hf_bound (t : ℝ) (ht : t ∈ B) : ‖(t : ℂ)‖ ≤ |a| + |b| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b, ht.1],
      by linarith [le_abs_self b, abs_nonneg a, ht.2]⟩
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f := by
    refine ⟨Complex.measurable_ofReal.indicator hB, |a| + |b|, fun t => ?_⟩
    by_cases ht : t ∈ B
    · simpa [f, ht] using hf_bound t ht
    · simp [f, ht, add_nonneg (abs_nonneg a) (abs_nonneg b)]
  have hg_bound (t : ℝ) : ‖g t‖ ≤ b - a := by
    by_cases ht : t ∈ B
    · rw [show g t = ((t-a : ℝ) : ℂ) from Set.indicator_of_mem ht _,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact sub_le_sub_right ht.2 a
    · simp [g, ht, sub_nonneg.mpr hab]
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g :=
    ⟨(Complex.measurable_ofReal.comp (measurable_id.sub measurable_const)).indicator hB,
      b - a, hg_bound⟩
  have hgp : g * p = g := by
    funext t
    by_cases ht : t ∈ B <;> simp [g, p, ht]
  have hprod : C.integral g * E B = C.integral g := by
    rw [← integral_indicator_one C B hB, ← C.mul g p hg hp, hgp]
  have hfun : f = (a : ℂ) • p + g := by
    funext t
    by_cases ht : t ∈ B
    · simp [f, p, g, ht, Complex.ofReal_sub]
    · simp [f, p, g, ht]
  have hi : C.integral f = (a : ℂ) • E B + C.integral g := by
    rw [hfun, C.add _ _ (hp.smul _) hg, C.smul _ _ hp, integral_indicator_one C B hB]
  have hnorm : ‖C.integral g‖ ≤ b - a := C.bound g (b-a) hg (sub_nonneg.mpr hab) hg_bound
  ext x
  let y := E B x
  have hygraph := localized_graph C Complex.measurable_ofReal hB hf_bound x
  obtain ⟨hy, heval⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp hygraph
  have hpos := hnonneg ⟨y, hy⟩
  have hgy : C.integral g y = C.integral g x :=
    congrArg (fun T : H →L[ℂ] H => T x) hprod
  have heval' : measurableIntegral C (fun t : ℝ => (t : ℂ)) ⟨y, hy⟩ =
      (a : ℂ) • y + C.integral g y := by
    rw [heval, hi]
    change (a : ℂ) • y + C.integral g x = (a : ℂ) • y + C.integral g y
    rw [hgy]
  rw [heval', inner_add_right, inner_smul_right] at hpos
  have hinner := re_inner_le_norm (𝕜 := ℂ) y (C.integral g y)
  change (inner ℂ y (C.integral g y)).re ≤ ‖y‖ * ‖C.integral g y‖ at hinner
  have hbound : ‖C.integral g y‖ ≤ (b-a) * ‖y‖ :=
    (C.integral g).le_opNorm y |>.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg y))
  have hsq : (inner ℂ y y).re = ‖y‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hsq] at hpos
  have hynorm : ‖y‖ = 0 := by
    have htot : 0 ≤ b * ‖y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hbound (norm_nonneg y)
      nlinarith
    have hsq0 : ‖y‖ ^ 2 ≤ 0 := by
      by_contra h
      have := mul_neg_of_neg_of_pos hb (lt_of_not_ge h)
      linarith
    nlinarith [norm_nonneg y]
  simpa only [zero_apply] using (norm_eq_zero.mp hynorm : y = 0)

/-- The negative half-line is exhausted by bounded closed negative intervals.
No spectral support or unbounded scalar-integral identity is assumed. -/
theorem nonnegative_support : Spec.NonnegativeSupport.{u} := by
  intro H _ _ _ A E C hrep hnonneg
  subst A
  have hinterval (a b : ℝ) (hb : b < 0) : E (Icc a b) = 0 := by
    by_cases hab : a ≤ b
    · exact negative_interval_null E C hnonneg hab hb
    · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab), E.map_empty]
  let B : ℕ → ℕ → Set ℝ := fun n k => Icc (-(n : ℝ)) (-((k : ℝ) + 1)⁻¹)
  have hexhaust : Iio (0 : ℝ) = ⋃ n, ⋃ k, B n k := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_ge (-t)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < -t from neg_pos.mpr ht)
      refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨k, ?_⟩⟩
      change -(n : ℝ) ≤ t ∧ t ≤ -((k : ℝ) + 1)⁻¹
      rw [one_div] at hk
      constructor <;> linarith
    · intro ht
      obtain ⟨n, ht⟩ := mem_iUnion.mp ht
      obtain ⟨k, ht⟩ := mem_iUnion.mp ht
      exact lt_of_le_of_lt ht.2 (neg_neg_of_pos (inv_pos.mpr (by positivity)))
  have hm (x : H) : C.measure x (Iio 0) = 0 := by
    rw [hexhaust]
    apply measure_iUnion_null
    intro n
    apply measure_iUnion_null
    intro k
    rw [C.measure_apply x (B n k) measurableSet_Icc,
      hinterval _ _ (neg_neg_of_pos (inv_pos.mpr (by positivity)))]
    simp
  refine ⟨?_, hm⟩
  ext x
  have hh := hm x
  rw [C.measure_apply x (Iio 0) measurableSet_Iio] at hh
  have hnorm : ‖E (Iio 0) x‖ = 0 := by
    have hsq := ENNReal.ofReal_eq_zero.mp hh
    nlinarith [norm_nonneg (E (Iio 0) x)]
  simpa only [zero_apply] using norm_eq_zero.mp hnorm

end ExpandedFA.Unbounded.NonnegativeSpectralSupport
