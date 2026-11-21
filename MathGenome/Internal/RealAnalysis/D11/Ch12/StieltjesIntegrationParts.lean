import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.StieltjesIntegrationParts
import MathGenome.Internal.RealAnalysis.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch14.IntegralVariationBound
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace D11.Ch12.StieltjesIntegrationParts
open ScalarStieltjesCorrespondence
open D11.Ch14.ScalarIntegration D11.Ch14.TotalVariation

variable {𝕜 : Type} [RCLike 𝕜]

theorem bounded_borel [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (F : ℝ → 𝕜) (hF : NBV F) :
    Measurable F ∧ (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) ∧
      IsFiniteMeasure (stieltjesMeasure F).variation := by
  refine ⟨hF.boundedVariationOn.measurable, ?_, measure_finite F hF⟩
  refine ⟨‖F 0‖ + (eVariationOn F univ).toReal, fun x => ?_⟩
  calc
    ‖F x‖ ≤ ‖F 0‖ + ‖F x - F 0‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖F 0‖ + (eVariationOn F univ).toReal := by
      gcongr
      simpa only [dist_eq_norm_sub] using hF.boundedVariationOn.dist_le (mem_univ x) (mem_univ 0)

theorem continuous_atomless (F : ℝ → 𝕜) (hF : NBV F) (hc : Continuous F) :
    (∀ x : ℝ, stieltjesMeasure F {x} = 0) ∧ NullSingletonClass (stieltjesMeasure F).variation := by
  have hatom (x : ℝ) : stieltjesMeasure F {x} = 0 := by
    rw [NormalizedStieltjes.atom_formula F hF,
      (hc.continuousAt.continuousWithinAt).leftLim_eq, sub_self]
  exact ⟨hatom, ⟨fun x => by simp [VectorMeasure.variation_apply_singleton, hatom]⟩⟩

theorem diagonal_null (F G : ℝ → 𝕜) (hF : NBV F) (hG : NBV G)
    (hc : Continuous F ∨ Continuous G) :
    ((stieltjesMeasure F).variation.prod (stieltjesMeasure G).variation) (diagonal ℝ) = 0 := by
  haveI := measure_finite F hF
  haveI := measure_finite G hG
  rcases hc with hc | hc
  · letI := (continuous_atomless F hF hc).2
    rw [Measure.prod_apply_symm measurableSet_diagonal]
    simp [diagonal]
  · letI := (continuous_atomless G hG hc).2
    rw [Measure.prod_apply measurableSet_diagonal]
    simp [diagonal]

private lemma mul_flip :
    (ContinuousLinearMap.lsmul ℝ 𝕜).flip = ContinuousLinearMap.lsmul ℝ 𝕜 := by
  ext x y
  exact mul_comm y x

theorem native_integration_parts (F G : ℝ → 𝕜) (hF : NBV F) (hG : NBV G)
    (hc : Continuous F ∨ Continuous G) (a b : ℝ) (hab : a < b) :
    (∫ᵛ x in Ioc a b, F x ∂[ContinuousLinearMap.lsmul ℝ 𝕜; stieltjesMeasure G]) +
    (∫ᵛ x in Ioc a b, G x ∂[ContinuousLinearMap.lsmul ℝ 𝕜; stieltjesMeasure F]) =
      F b * G b - F a * G a := by
  have step (F G : ℝ → 𝕜) (hF : NBV F) (hG : NBV G) (hc : Continuous F) :
      (∫ᵛ x in Ioc a b, F x ∂[ContinuousLinearMap.lsmul ℝ 𝕜; stieltjesMeasure G]) +
      (∫ᵛ x in Ioc a b, G x ∂[ContinuousLinearMap.lsmul ℝ 𝕜; stieltjesMeasure F]) =
        F b * G b - F a * G a := by
    have hl : F.leftLim = F := funext fun x =>
      hc.continuousAt.continuousWithinAt.leftLim_eq
    have h := hF.boundedVariationOn.setIntegral_Ioc_leftLim_vectorMeasure_eq_sub
      (B := ContinuousLinearMap.lsmul ℝ 𝕜) hG.boundedVariationOn hab.le
    rw [hl, hF.rightLim_eq, hG.rightLim_eq, mul_flip] at h
    rw [stieltjesMeasure_eq hF, stieltjesMeasure_eq hG]
    exact (eq_sub_iff_add_eq).mp h
  rcases hc with hc | hc
  · exact step F G hF hG hc
  · simpa only [add_comm, mul_comm] using step G F hG hF hc

/-! The complex Jordan integral and the pairing integral agree. We check
simple functions directly, then use the same dominated approximations on
both sides. This bridge uses no density representation of the measure. -/

theorem complexIntegral_simple_eq_native {X : Type*} [MeasurableSpace X]
    (ν : ComplexMeasure X) (s : SimpleFunc X ℂ) (hs : complexIntegrable ν s) :
    complexIntegral ν s hs =
      ∫ᵛ x, s x ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν] := by
  classical
  haveI : IsFiniteMeasure ν.variation := complex_finite ν
  have hsfun : (fun x => ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun _ => c) x) = s := by
    funext x
    simp [Set.indicator, eq_comm, s.mem_range_self x]
  rw [complexIntegral_simple]
  symm
  calc
    (∫ᵛ x, s x ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν]) =
        ∫ᵛ x, ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun _ => c) x
          ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν] := by rw [hsfun]
    _ = ∑ c ∈ s.range, ∫ᵛ x, (s ⁻¹' {c}).indicator (fun _ => c) x
          ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν] := by
      apply VectorMeasure.integral_finsetSum
      intro c _
      exact (integrable_const c).indicator (s.measurableSet_fiber c)
    _ = ∑ c ∈ s.range, c * ν (s ⁻¹' {c}) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [VectorMeasure.integral_indicator_const c (s.measurableSet_fiber c)]
      rfl

theorem complexIntegral_eq_native {X : Type*} [MeasurableSpace X]
    (ν : ComplexMeasure X) (f : X → ℂ) (hf : complexIntegrable ν f) :
    complexIntegral ν f hf =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν] := by
  obtain ⟨hfm, hfi⟩ := (complexIntegrable_iff _ _).mp hf
  let s : ℕ → SimpleFunc X ℂ := fun n =>
    SimpleFunc.approxOn f hfm (range f ∪ {0}) 0 (by simp) n
  have hsm : ∀ n, Measurable (s n) := fun n => (s n).measurable
  have hsl : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := fun x =>
    SimpleFunc.tendsto_approxOn hfm (by simp) (subset_closure (Or.inl (mem_range_self x)))
  have hsb : ∀ n x, ‖s n x‖ ≤ ‖f x‖ + ‖f x‖ := fun n x =>
    SimpleFunc.norm_approxOn_zero_le hfm (by simp) x n
  have hg : D11.Ch06.ScalarIntegral.scalarIntegrable (totalVariation ν)
      (fun x => ‖f x‖ + ‖f x‖) :=
    (D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mpr
      ⟨hfm.norm.add hfm.norm, hfi.norm.add hfi.norm⟩
  obtain ⟨hS, _, _, _, hlim⟩ := D11.Ch14.IntegralVariationBound.complex_dominated_convergence
    ν (fun n => s n) f (fun x => ‖f x‖ + ‖f x‖) hsm hfm hg
    (fun n => Eventually.of_forall (hsb n)) (Eventually.of_forall hsl)
  have hnative := VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := ν) (B := ContinuousLinearMap.lsmul ℝ ℂ) (fun x => ‖f x‖ + ‖f x‖)
    (fun n => (hsm n).aestronglyMeasurable) (hfi.norm.add hfi.norm)
    (fun n => Eventually.of_forall (hsb n)) (Eventually.of_forall hsl)
  have heq : (fun n => complexIntegral ν (s n) (hS n)) =
      (fun n => ∫ᵛ x, s n x ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν]) :=
    funext fun n => complexIntegral_simple_eq_native ν (s n) (hS n)
  change Tendsto (fun n => complexIntegral ν (s n) (hS n)) atTop
    (𝓝 (complexIntegral ν f hf)) at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim hnative

theorem signed_integration_parts :
    Specs.D11.Ch12.StieltjesIntegrationParts.signed_integration_parts := by
  intro F G hF hG hc a b hab
  change NBV F at hF
  change NBV G at hG
  haveI : IsFiniteMeasure (totalVariation (stieltjesMeasure F)) := measure_finite F hF
  haveI : IsFiniteMeasure (totalVariation (stieltjesMeasure G)) := measure_finite G hG
  have hFG : signedIntegrable (stieltjesMeasure G) ((Ioc a b).indicator F) :=
    (signedIntegrable_iff _ _).mpr
      ⟨hF.boundedVariationOn.measurable.indicator measurableSet_Ioc,
        hF.boundedVariationOn.integrable.indicator measurableSet_Ioc⟩
  have hGF : signedIntegrable (stieltjesMeasure F) ((Ioc a b).indicator G) :=
    (signedIntegrable_iff _ _).mpr
      ⟨hG.boundedVariationOn.measurable.indicator measurableSet_Ioc,
        hG.boundedVariationOn.integrable.indicator measurableSet_Ioc⟩
  refine ⟨hFG, hGF, ?_⟩
  change signedIntegral (stieltjesMeasure G) _ hFG +
    signedIntegral (stieltjesMeasure F) _ hGF = _
  rw [signedIntegral_eq_native, signedIntegral_eq_native,
    mul_flip, VectorMeasure.integral_indicator measurableSet_Ioc,
    VectorMeasure.integral_indicator measurableSet_Ioc]
  exact native_integration_parts F G hF hG hc a b hab

theorem complex_integration_parts :
    Specs.D11.Ch12.StieltjesIntegrationParts.complex_integration_parts := by
  intro F G hF hG hc a b hab
  change NBV F at hF
  change NBV G at hG
  haveI : IsFiniteMeasure (totalVariation (stieltjesMeasure F)) := measure_finite F hF
  haveI : IsFiniteMeasure (totalVariation (stieltjesMeasure G)) := measure_finite G hG
  have hFG : complexIntegrable (stieltjesMeasure G) ((Ioc a b).indicator F) :=
    (complexIntegrable_iff _ _).mpr
      ⟨hF.boundedVariationOn.measurable.indicator measurableSet_Ioc,
        hF.boundedVariationOn.integrable.indicator measurableSet_Ioc⟩
  have hGF : complexIntegrable (stieltjesMeasure F) ((Ioc a b).indicator G) :=
    (complexIntegrable_iff _ _).mpr
      ⟨hG.boundedVariationOn.measurable.indicator measurableSet_Ioc,
        hG.boundedVariationOn.integrable.indicator measurableSet_Ioc⟩
  refine ⟨hFG, hGF, ?_⟩
  change complexIntegral (stieltjesMeasure G) _ hFG +
    complexIntegral (stieltjesMeasure F) _ hGF = _
  rw [complexIntegral_eq_native, complexIntegral_eq_native,
    VectorMeasure.integral_indicator measurableSet_Ioc,
    VectorMeasure.integral_indicator measurableSet_Ioc]
  exact native_integration_parts F G hF hG hc a b hab

end D11.Ch12.StieltjesIntegrationParts
