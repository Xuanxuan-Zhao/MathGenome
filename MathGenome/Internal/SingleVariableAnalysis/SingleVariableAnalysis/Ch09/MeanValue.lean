import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.MeanValue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Products
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ExtremeValues
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.IntermediateValues

/-! The weighted mean value theorem for the proper Riemann integral.
The real proof uses extrema, order and the intermediate value theorem.
Zero total weight is handled by the same two-sided bounds, with no division.
The complex statement retains only the weighted norm inequalities. -/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- Local support for the product integral: uniform continuity makes every
sufficiently short cell have small oscillation. -/
private theorem continuous_real_integrable {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) : RealIntegrable f a b := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · have hb : BoundedOnInterval f a b :=
      ⟨(isCompact_Icc.image_of_continuousOn hf).bddBelow,
        (isCompact_Icc.image_of_continuousOn hf).bddAbove⟩
    apply (darboux_criterion f hab hb).mpr
    intro ε hε
    let η := ε / (b - a + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
    obtain ⟨P, hP⟩ := exists_fine_partition hab.le δ hδ
    have hcell (i : Fin P.n) :
        cellSupremum f P hb i - cellInfimum f P hb i ≤ η := by
      apply cell_oscillation_le_of_sub_le
      intro x hx y hy
      have hxy : dist x y < δ := by
        rw [Real.dist_eq]
        apply lt_of_le_of_lt _ ((cellLength_le_mesh P i).trans_lt hP)
        change x ∈ Set.Icc _ _ at hx
        change y ∈ Set.Icc _ _ at hy
        change |x - y| ≤ P.point i.succ - P.point i.castSucc
        exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
      have h := huc x (cell_subset_interval P i hx) y (cell_subset_interval P i hy) hxy
      exact (le_abs_self _).trans (by simpa only [Real.dist_eq] using h.le)
    refine ⟨P, ?_⟩
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_right (hcell i) (cell_positive P i).le
    rw [sum_cell_oscillation, ← Finset.mul_sum, sum_cellLength] at hs
    have hηeq : η * (b - a + 1) = ε := by
      dsimp [η]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  · exact realIntegrable_degenerate f a

/-- Positivity of the weight passes to its Darboux integral. -/
theorem realIntegral_nonneg_of_nonneg {g : ℝ → ℝ} {a b : ℝ}
    (hg : RealIntegrable g a b) (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x) :
    0 ≤ realIntegral g hg := by
  obtain ⟨hz, hIz⟩ := real_zero_value hg.ordered
  have h := realIntegral_mono (fun _ => 0) g hz hg hg0
  simpa only [hIz] using h

/-- Any two bounds on the real factor bound the weighted integral, including
when the weight has integral zero. -/
theorem realIntegral_weighted_bounds {f g : ℝ → ℝ} {a b m M : ℝ}
    (hg : RealIntegrable g a b) (hfg : RealIntegrable (fun x => f x * g x) a b)
    (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hm : ∀ x ∈ Set.Icc a b, m ≤ f x)
    (hM : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    m * realIntegral g hg ≤ realIntegral _ hfg ∧
      realIntegral _ hfg ≤ M * realIntegral g hg := by
  obtain ⟨hmg, hImg⟩ := real_mul_value hg m
  obtain ⟨hMg, hIMg⟩ := real_mul_value hg M
  constructor
  · rw [← hImg]
    exact realIntegral_mono _ _ hmg hfg fun x hx =>
      mul_le_mul_of_nonneg_right (hm x hx) (hg0 x hx)
  · rw [← hIMg]
    exact realIntegral_mono _ _ hfg hMg fun x hx =>
      mul_le_mul_of_nonneg_right (hM x hx) (hg0 x hx)

theorem real_weighted_mean_value :
    Specs.SingleVariableAnalysis.Ch09.MeanValue.realWeightedMeanValue := by
  intro f g a b hab hf hg hg0
  have hfg := real_product (continuous_real_integrable hab hf) hg
  refine ⟨hfg, ?_⟩
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab) hf
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hf
  have hbounds := realIntegral_weighted_bounds hg hfg hg0 hmin hmax
  have hG := realIntegral_nonneg_of_nonneg hg hg0
  by_cases hzero : realIntegral g hg = 0
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
    simp only [hzero, mul_zero] at hbounds ⊢
    exact le_antisymm hbounds.2 hbounds.1
  · have hpos : 0 < realIntegral g hg := lt_of_le_of_ne hG (Ne.symm hzero)
    have hrange : realIntegral _ hfg / realIntegral g hg ∈ Set.Icc (f u) (f v) :=
      ⟨(le_div_iff₀ hpos).mpr hbounds.1, (div_le_iff₀ hpos).mpr hbounds.2⟩
    obtain ⟨c, hc, hfc⟩ := isPreconnected_Icc.intermediate_value hu hv hf hrange
    refine ⟨c, hc, ?_⟩
    rw [hfc]
    exact (div_mul_cancel₀ _ hzero).symm

theorem complex_weighted_norm_bound :
    Specs.SingleVariableAnalysis.Ch09.MeanValue.complexWeightedNormBound := by
  intro f g a b hab hf hg hg0
  have hfi : ComplexIntegrable f a b :=
    ⟨continuous_real_integrable hab (Complex.continuous_re.comp_continuousOn hf),
      continuous_real_integrable hab (Complex.continuous_im.comp_continuousOn hf)⟩
  have hgi : ComplexIntegrable (fun x => (g x : ℂ)) a b := by
    constructor
    · simpa only [Complex.ofReal_re] using hg
    · simpa only [Complex.ofReal_im] using (real_zero_value hab).choose
  have hfg := complex_product hfi hgi
  have hng := real_product (ComplexIntegrable.norm hfi) hg
  refine ⟨hfg, hng, ?_, ?_⟩
  · obtain ⟨hn, htri, _⟩ := complex_norm_estimate _ hfg
    apply htri.trans
    apply realIntegral_mono _ _ hn hng
    intro x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 x hx)]
  · obtain ⟨hMg, hIMg⟩ := real_mul_value hg (sSup ((fun x => ‖f x‖) '' Set.Icc a b))
    rw [← hIMg]
    apply realIntegral_mono _ _ hng hMg
    intro x hx
    apply mul_le_mul_of_nonneg_right _ (hg0 x hx)
    exact le_csSup (isCompact_Icc.image_of_continuousOn hf.norm).bddAbove
      (Set.mem_image_of_mem _ hx)

end SingleVariableAnalysis.Riemann
