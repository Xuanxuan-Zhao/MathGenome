import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.ExponentialMoments

open MeasureTheory ProbabilityTheory

namespace P205.Probability

private theorem integrable_of_ae_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ) (hb : ∃ B : ℝ, ∀ᵐ ω ∂μ, |g ω| ≤ B) :
    Integrable g μ := by
  obtain ⟨B, hB⟩ := hb
  exact Integrable.of_bound hg B (by simpa only [Real.norm_eq_abs] using hB)

theorem bounded_exponential_integrable : Specs.P205.Probability.BoundedExponentialIntegrable := by
  intro Ω _ μ _ X hX hB lam
  obtain ⟨B, hB⟩ := hB
  apply integrable_exp_mul_of_mem_Icc hX.aemeasurable
  filter_upwards [hB] with ω hω
  exact abs_le.mp hω

private theorem integrable_finite_product {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (g : ι → Ω → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    (hb : ∀ i, ∃ C : ℝ, ∀ᵐ ω ∂μ, |g i ω| ≤ C) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, g i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact integrable_const 1
  | @insert i s hi ih =>
    obtain ⟨C, hC⟩ := hb i
    simpa only [Finset.prod_insert hi] using
      ih.bdd_mul (hg i) (by simpa only [Real.norm_eq_abs] using hC)

theorem independent_product : Specs.P205.Probability.IndependentProduct := by
  intro Ω ι _ _ μ _ X f hX _hBoundX hInd hf hBoundf
  have hComp (i : ι) : AEStronglyMeasurable (fun ω => f i (X i ω)) μ :=
    (hf i).comp_aemeasurable (hX i).aemeasurable
  refine ⟨fun i => integrable_of_ae_abs_bound (hComp i) (hBoundf i), ?_, ?_⟩
  · exact integrable_finite_product (fun i ω => f i (X i ω)) hComp hBoundf Finset.univ
  · exact hInd.integral_fun_prod_comp (fun i => (hX i).aemeasurable) hf

theorem independent_mgf_sum : Specs.P205.Probability.IndependentMGFSum := by
  intro Ω ι _ _ μ _ X hX hB hInd lam
  have hInt (i : ι) : Integrable (fun ω => Real.exp (lam * X i ω)) μ :=
    bounded_exponential_integrable μ (X i) (hX i) (hB i) lam
  refine ⟨hInt, ?_, ?_⟩
  · simpa only [Finset.sum_apply] using
      hInd.integrable_exp_mul_sum hX (s := Finset.univ) (fun i _ => hInt i)
  · have hSum : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
      ext ω
      simp only [Finset.sum_apply]
    rw [hSum]
    exact hInd.mgf_sum hX Finset.univ

theorem exponential_markov : Specs.P205.Probability.ExponentialMarkov := by
  intro Ω _ μ _ Y hY hB t lam hlam
  exact measure_ge_le_exp_mul_mgf t hlam.le (bounded_exponential_integrable μ Y hY hB lam)

end P205.Probability
