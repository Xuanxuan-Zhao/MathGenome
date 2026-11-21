import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.GaussianRemainder
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.Gaussian
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.HermiteRemainder
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators

namespace NumAnalysis206.Quadrature

/-- A continuous interval function is integrable when the measure is
concentrated there, regardless of its values off the interval. -/
lemma integrable_of_continuousOn_support_interval (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hs : μ.support ⊆ Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : Integrable f μ := by
  have hae : ∀ᵐ t ∂μ, t ∈ Icc a b :=
    (show ∀ᵐ t ∂μ, t ∈ μ.support from μ.support_mem_ae).mono (fun _ ht => hs ht)
  have hi := hf.integrableOn_Icc (μ := μ)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hi

/-- Integrating pointwise intermediate values against a nonnegative weight
needs no measurable choice of the intermediate points. -/
lemma integral_pointwise_intermediate_value
    (μ : Measure ℝ) {a b : ℝ} (hab : a ≤ b)
    (hae : ∀ᵐ t ∂μ, t ∈ Icc a b)
    {g h k : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hh : Integrable h μ) (hk : Integrable k μ)
    (hk0 : ∀ᵐ t ∂μ, 0 ≤ k t) (hpos : 0 < ∫ t, k t ∂μ)
    {c : ℝ} (hc : 0 < c)
    (hpoint : ∀ t ∈ Icc a b, ∃ ξ ∈ Icc a b, h t = g ξ / c * k t) :
    ∃ ξ ∈ Icc a b, (∫ t, h t ∂μ) = g ξ / c * (∫ t, k t ∂μ) := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hg
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hg
  have hlo : g u / c * (∫ t, k t ∂μ) ≤ ∫ t, h t ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hk.const_mul _) hh
    filter_upwards [hae, hk0] with t ht ht0
    obtain ⟨ξ, hξ, heq⟩ := hpoint t ht
    rw [heq]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hmin hξ) hc.le) ht0
  have hhi : (∫ t, h t ∂μ) ≤ g v / c * (∫ t, k t ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hh (hk.const_mul _)
    filter_upwards [hae, hk0] with t ht ht0
    obtain ⟨ξ, hξ, heq⟩ := hpoint t ht
    rw [heq]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hmax hξ) hc.le) ht0
  have hlo' : g u ≤ (∫ t, h t ∂μ) / (∫ t, k t ∂μ) * c := by
    exact (div_le_iff₀ hc).mp ((le_div_iff₀ hpos).mpr hlo)
  have hhi' : (∫ t, h t ∂μ) / (∫ t, k t ∂μ) * c ≤ g v := by
    exact (le_div_iff₀ hc).mp ((div_le_iff₀ hpos).mpr hhi)
  obtain ⟨ξ, hξ, heq⟩ := isPreconnected_Icc.intermediate_value hu hv hg ⟨hlo', hhi'⟩
  refine ⟨ξ, hξ, ?_⟩
  rw [heq]
  field_simp

/-- The analytic Gaussian remainder and its uniform derivative bound. -/
theorem gaussian_remainder : Specs.gaussianRemainder := by
  intro μ _ n hn hm hG a b hs f D hD π hπ x hx hroot
  classical
  obtain ⟨z, hz, hprod, hroots, _, hloc⟩ := orthogonal_roots μ n hn hm hG π hπ
  have hzmem (i : Fin n) : z i ∈ Icc a b := by
    obtain ⟨l, hl, r, hr, hli, hir⟩ := hloc i
    exact ⟨(hs hl).1.trans hli.le, hir.le.trans (hs hr).2⟩
  have hab : a ≤ b := (hzmem ⟨0, by omega⟩).1.trans (hzmem ⟨0, by omega⟩).2
  have hae : ∀ᵐ t ∂μ, t ∈ Icc a b :=
    (show ∀ᵐ t ∂μ, t ∈ μ.support from μ.support_mem_ae).mono (fun _ ht => hs ht)
  have hsum : ∑ i : Fin n, (2 : ℕ) = 2 * n := by simp [Nat.mul_comm]
  obtain ⟨p, hp, _⟩ := NumAnalysis206.Approximation.real_hermite_interpolation
    n (by omega) z hz (fun _ => 2) (fun _ => by norm_num) (fun i j => D j (z i))
  simp only [hsum] at hp
  have hpn : p.natDegree ≤ 2 * n - 1 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have := (natDegree_lt_iff_degree_lt hp0).mpr hp.1
      omega
  have hmatch (i : Fin n) : p.eval (x i) = f (x i) := by
    obtain ⟨j, hj⟩ := (hroots (x i)).mp (hroot i)
    have hv := hp.2 j 0 (by norm_num)
    change p.eval (z j) = D 0 (z j) at hv
    rw [← hj, hv, hD.1 (hzmem j)]
  have hQ : (∑ i, Specs.gaussianWeightValue μ x i * f (x i)) =
      ∫ t : ℝ, p.eval t ∂μ := by
    rw [gaussian_exactness μ n hn hm π hπ x hx hroot p hpn]
    exact Finset.sum_congr rfl (fun i _ => congrArg _ (hmatch i).symm)
  have hfc : ContinuousOn f (Icc a b) :=
    (hD.2.1 0 (by omega)).congr (fun t ht => (hD.1 ht).symm)
  have hfi : Integrable f μ := integrable_of_continuousOn_support_interval μ hs hfc
  have hpi : Integrable (fun t => p.eval t) μ :=
    polynomial_integrable μ n hm p (by omega)
  have hki : Integrable (fun t => (π.eval t)^2) μ := by
    simpa only [pow_two] using
      polynomial_products μ n hm π π (by rw [hπ.2.1]; omega)
  have hkpos : 0 < ∫ t : ℝ, (π.eval t)^2 ∂μ :=
    polynomial_square_positive μ n hm hG π hπ.1.ne_zero hπ.2.1.le
  have hfac : 0 < ((2 * n).factorial : ℝ) := by positivity
  have hpoint : ∀ t ∈ Icc a b, ∃ ξ ∈ Icc a b,
      f t - p.eval t = D (2 * n) ξ / ((2 * n).factorial : ℝ) * (π.eval t)^2 := by
    intro t ht
    have hjet : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b
        (∑ i : Fin n, (2 : ℕ)) f D := by rwa [hsum]
    obtain ⟨ξ, hξ, heq⟩ := NumAnalysis206.Approximation.hermite_error_formula
      n (by omega) z hz hzmem (fun _ => 2) (fun _ => by norm_num) hjet p
      (by simpa only [hsum] using hp.1) (by simpa only [hsum] using hp.2) t ht
    have hsub : insert t (Set.range z) ⊆ Icc a b := by
      rintro y (rfl | ⟨i, rfl⟩)
      · exact ht
      · exact hzmem i
    refine ⟨ξ, (convexHull_min hsub (convex_Icc a b)) hξ, ?_⟩
    have hsq : ∏ i : Fin n, (t - z i)^2 = (π.eval t)^2 := by
      rw [hprod]
      simp [eval_prod, Finset.prod_pow]
    simpa only [hsum, hsq] using heq
  obtain ⟨ξ, hξ, heq⟩ := integral_pointwise_intermediate_value μ hab hae
    (hD.2.1 (2 * n) le_rfl) (hfi.sub hpi) hki
    (Filter.Eventually.of_forall (fun t => sq_nonneg (π.eval t))) hkpos hfac hpoint
  change (∫ t : ℝ, f t - p.eval t ∂μ) = _ at heq
  rw [integral_sub hfi hpi] at heq
  have herr : (∫ t : ℝ, f t ∂μ) - ∑ i, Specs.gaussianWeightValue μ x i * f (x i) =
      D (2 * n) ξ / ((2 * n).factorial : ℝ) * (∫ t : ℝ, (π.eval t)^2 ∂μ) := by
    rwa [hQ]
  refine ⟨⟨ξ, hξ, herr⟩, ?_⟩
  rw [herr, abs_mul, abs_div, abs_of_pos hfac, abs_of_pos hkpos]
  apply mul_le_mul_of_nonneg_right _ hkpos.le
  apply div_le_div_of_nonneg_right _ hfac.le
  exact le_csSup (isCompact_Icc.bddAbove_image (hD.2.1 (2 * n) le_rfl).abs)
    (Set.mem_image_of_mem _ hξ)

end NumAnalysis206.Quadrature
