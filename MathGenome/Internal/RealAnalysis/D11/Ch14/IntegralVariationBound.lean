import MathGenome.Internal.RealAnalysis.D11.Ch14.ScalarIntegration
import MathGenome.Internal.RealAnalysis.D11.Ch06.DominatedConvergence
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.IntegralVariationBound

/-! Integral bounds and dominated convergence, paper.tex:4710–4721.
The complex sharp bound is proved on simple functions and passed to a
dominated simple approximation through the four Jordan integrals. In
particular no polar density or Radon–Nikodym theorem is used. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace D11.Ch14.IntegralVariationBound
open D11.Ch14.ScalarIntegration D11.Ch14.TotalVariation D11.Ch14.Jordan
open D11.Ch06.ScalarIntegral (scalarIntegrable scalarIntegrable_iff)
variable {X : Type u} [MeasurableSpace X]
variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Positive-measure DCT with the original measurable representatives and
with all absolute integrability conclusions retained. -/
private theorem dominated_integrability (μ : Measure X) (F : ℕ → X → 𝕜)
    (f : X → 𝕜) (g : X → ℝ) (hFm : ∀ n, Measurable (F n)) (hfm : Measurable f)
    (hgi : Integrable g μ) (hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    (∀ n, Integrable (F n) μ) ∧ Integrable f μ ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0) := by
  have hFi : ∀ n, Integrable (F n) μ := fun n =>
    hgi.mono' (hFm n).aestronglyMeasurable (hb n)
  have hfi : Integrable f μ := ⟨hfm.aestronglyMeasurable,
    hasFiniteIntegral_of_dominated_convergence hgi.hasFiniteIntegral hb hl⟩
  refine ⟨hFi, hfi, ?_⟩
  have h := tendsto_lintegral_norm_of_dominated_convergence
    (fun n => (hFm n).aestronglyMeasurable) hgi.hasFiniteIntegral hb hl
  have ht : Tendsto (fun n => (∫⁻ x, ENNReal.ofReal ‖F n x - f x‖ ∂μ).toReal)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  convert ht using 1
  funext n
  simpa only [Pi.sub_apply, ofReal_norm] using
    integral_norm_eq_lintegral_enorm ((hFi n).sub hfi).aestronglyMeasurable

/-- DCT for a Jordan difference, with domination measured by any positive
measure which dominates the signed variation. -/
private theorem tendsto_jordan_difference (ν : SignedMeasure X) (μ : Measure X)
    (hνμ : totalVariation ν ≤ μ) (F : ℕ → X → 𝕜) (f : X → 𝕜) (g : X → ℝ)
    (hFm : ∀ n, Measurable (F n)) (hgi : Integrable g μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (∫ x, F n x ∂(positivePart ν)) - (∫ x, F n x ∂(negativePart ν)))
      atTop (𝓝 ((∫ x, f x ∂(positivePart ν)) - (∫ x, f x ∂(negativePart ν)))) := by
  have hp : positivePart ν ≤ μ := (show positivePart ν ≤ totalVariation ν by
    rw [signed_totalVariation_eq_jordan]; exact Measure.le_add_right le_rfl).trans hνμ
  have hn : negativePart ν ≤ μ := (show negativePart ν ≤ totalVariation ν by
    rw [signed_totalVariation_eq_jordan]; exact Measure.le_add_left le_rfl).trans hνμ
  exact (tendsto_integral_of_dominated_convergence g
    (fun n => (hFm n).aestronglyMeasurable) (hgi.mono_measure hp)
    (fun n => (ae_mono hp) (hb n)) ((ae_mono hp) hl)).sub
    (tendsto_integral_of_dominated_convergence g
      (fun n => (hFm n).aestronglyMeasurable) (hgi.mono_measure hn)
      (fun n => (ae_mono hn) (hb n)) ((ae_mono hn) hl))

theorem signed_dominated_convergence :
    Specs.D11.Ch14.IntegralVariationBound.signed_dominated_convergence := by
  intro X _ 𝕜 _ _ _ ν F f g hFm hfm hg hb hl
  have hgi := (scalarIntegrable_iff _ _).mp hg |>.2
  obtain ⟨hFi, hfi, herr⟩ := dominated_integrability (totalVariation ν) F f g hFm hfm hgi hb hl
  let hF : ∀ n, signedIntegrable ν (F n) := fun n =>
    (signedIntegrable_iff _ _).mpr ⟨hFm n, hFi n⟩
  let hf : signedIntegrable ν f := (signedIntegrable_iff _ _).mpr ⟨hfm, hfi⟩
  refine ⟨hF, hf, ?_, herr, ?_⟩
  · intro n
    exact (scalarIntegrable_iff _ _).mpr ⟨((hFm n).sub hfm).norm, ((hFi n).sub hfi).norm⟩
  · exact tendsto_jordan_difference ν (totalVariation ν) le_rfl F f g hFm hgi hb hl

theorem complex_dominated_convergence :
    Specs.D11.Ch14.IntegralVariationBound.complex_dominated_convergence := by
  intro X _ ν F f g hFm hfm hg hb hl
  have hgi := (scalarIntegrable_iff _ _).mp hg |>.2
  obtain ⟨hFi, hfi, herr⟩ := dominated_integrability (totalVariation ν) F f g hFm hfm hgi hb hl
  let hF : ∀ n, complexIntegrable ν (F n) := fun n =>
    (complexIntegrable_iff _ _).mpr ⟨hFm n, hFi n⟩
  let hf : complexIntegrable ν f := (complexIntegrable_iff _ _).mpr ⟨hfm, hfi⟩
  refine ⟨hF, hf, ?_, herr, ?_⟩
  · intro n
    exact (scalarIntegrable_iff _ _).mpr ⟨((hFm n).sub hfm).norm, ((hFi n).sub hfi).norm⟩
  · exact (tendsto_jordan_difference ν.re (totalVariation ν) (real_variation_le ν)
      F f g hFm hgi hb hl).add
      (tendsto_const_nhds.mul (tendsto_jordan_difference ν.im (totalVariation ν)
        (imaginary_variation_le ν) F f g hFm hgi hb hl))

theorem norm_signedIntegral_le (ν : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable ν f) :
    ‖signedIntegral ν f hf‖ ≤ ∫ x, ‖f x‖ ∂(totalVariation ν) := by
  obtain ⟨hp, hn⟩ := signed_parts_integrable ν f hf
  calc
    ‖signedIntegral ν f hf‖ ≤ ‖∫ x, f x ∂(positivePart ν)‖ + ‖∫ x, f x ∂(negativePart ν)‖ :=
      norm_sub_le _ _
    _ ≤ (∫ x, ‖f x‖ ∂(positivePart ν)) + (∫ x, ‖f x‖ ∂(negativePart ν)) :=
      add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
    _ = ∫ x, ‖f x‖ ∂(totalVariation ν) := by
      rw [signed_totalVariation_eq_jordan, integral_add_measure hp.norm hn.norm]

/-- The sharp simple-function estimate uses each complex mass itself,
rather than bounding real and imaginary integrals separately. -/
theorem norm_complexIntegral_simple_le (ν : ComplexMeasure X) (s : SimpleFunc X ℂ)
    (hs : complexIntegrable ν s) :
    ‖complexIntegral ν s hs‖ ≤ ∫ x, ‖s x‖ ∂(totalVariation ν) := by
  classical
  let := complex_finite ν
  have hi := ((complexIntegrable_iff _ _).mp hs).2
  have hm : Integrable (s.map norm) (totalVariation ν) := hi.norm
  rw [complexIntegral_simple]
  calc
    ‖∑ c ∈ s.range, c * ν (s ⁻¹' {c})‖ ≤ ∑ c ∈ s.range, ‖c * ν (s ⁻¹' {c})‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c ∈ s.range, (totalVariation ν).real (s ⁻¹' {c}) * ‖c‖ := by
      apply Finset.sum_le_sum
      intro c hc
      rw [norm_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg c)
      exact VectorMeasure.norm_measure_le_variation (measure_ne_top (totalVariation ν) _)
    _ = ∫ x, ‖s x‖ ∂(totalVariation ν) := by
      change _ = ∫ x, (s.map norm) x ∂(totalVariation ν)
      rw [← SimpleFunc.integral_eq_integral (s.map norm) hm,
        s.map_integral norm hi norm_zero]
      rfl

theorem norm_complexIntegral_le (ν : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable ν f) :
    ‖complexIntegral ν f hf‖ ≤ ∫ x, ‖f x‖ ∂(totalVariation ν) := by
  obtain ⟨hfm, hfi⟩ := (complexIntegrable_iff _ _).mp hf
  let s : ℕ → SimpleFunc X ℂ := fun n =>
    SimpleFunc.approxOn f hfm (range f ∪ {0}) 0 (by simp) n
  have hsm : ∀ n, Measurable (s n) := fun n => (s n).measurable
  have hsl : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := fun x =>
    SimpleFunc.tendsto_approxOn hfm (by simp) (subset_closure (Or.inl (mem_range_self x)))
  have hsb : ∀ n x, ‖s n x‖ ≤ ‖f x‖ + ‖f x‖ := fun n x =>
    SimpleFunc.norm_approxOn_zero_le hfm (by simp) x n
  have hg : scalarIntegrable (totalVariation ν) (fun x => ‖f x‖ + ‖f x‖) :=
    (scalarIntegrable_iff _ _).mpr ⟨hfm.norm.add hfm.norm, hfi.norm.add hfi.norm⟩
  obtain ⟨hS, hF, _, _, hlim⟩ := complex_dominated_convergence ν (fun n => s n) f
    (fun x => ‖f x‖ + ‖f x‖) hsm hfm hg
    (fun n => Eventually.of_forall (hsb n)) (Eventually.of_forall hsl)
  have hnorm : Tendsto (fun n => ∫ x, ‖s n x‖ ∂(totalVariation ν))
      atTop (𝓝 (∫ x, ‖f x‖ ∂(totalVariation ν))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ + ‖f x‖)
    · intro n
      exact (hsm n).norm.aestronglyMeasurable
    · exact hfi.norm.add hfi.norm
    · intro n
      exact Eventually.of_forall (fun x => by simpa only [norm_norm] using hsb n x)
    · exact Eventually.of_forall (fun x => (hsl x).norm)
  exact le_of_tendsto_of_tendsto hlim.norm hnorm
    (Eventually.of_forall (fun n => norm_complexIntegral_simple_le ν (s n) (hS n)))

theorem signed_integral_variation_bound :
    Specs.D11.Ch14.IntegralVariationBound.signed_integral_variation_bound := by
  intro X _ 𝕜 _ _ _ ν f hf E hE
  obtain ⟨hfm, hfi⟩ := (signedIntegrable_iff _ _).mp hf
  have hEf : signedIntegrable ν (E.indicator f) :=
    (signedIntegrable_iff _ _).mpr ⟨hfm.indicator hE, hfi.indicator hE⟩
  refine ⟨hEf, ?_⟩
  calc
    ‖signedIntegral ν (E.indicator f) hEf‖ ≤
        ∫ x, ‖E.indicator f x‖ ∂(totalVariation ν) := norm_signedIntegral_le ν _ hEf
    _ = ∫ x in E, ‖f x‖ ∂(totalVariation ν) := by
      simp_rw [norm_indicator_eq_indicator_norm]
      exact integral_indicator hE

theorem complex_integral_variation_bound :
    Specs.D11.Ch14.IntegralVariationBound.complex_integral_variation_bound := by
  intro X _ ν f hf E hE
  obtain ⟨hfm, hfi⟩ := (complexIntegrable_iff _ _).mp hf
  have hEf : complexIntegrable ν (E.indicator f) :=
    (complexIntegrable_iff _ _).mpr ⟨hfm.indicator hE, hfi.indicator hE⟩
  refine ⟨hEf, ?_⟩
  calc
    ‖complexIntegral ν (E.indicator f) hEf‖ ≤
        ∫ x, ‖E.indicator f x‖ ∂(totalVariation ν) := norm_complexIntegral_le ν _ hEf
    _ = ∫ x in E, ‖f x‖ ∂(totalVariation ν) := by
      simp_rw [norm_indicator_eq_indicator_norm]
      exact integral_indicator hE

end D11.Ch14.IntegralVariationBound
