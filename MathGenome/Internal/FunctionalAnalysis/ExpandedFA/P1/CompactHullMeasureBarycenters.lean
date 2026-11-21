import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.CompactHullMeasureBarycenters
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Representing measures on arbitrary compact sets. We use compactness of
probability measures without countability assumptions, then apply Riesz–Markov
to obtain a regular representative with the same continuous scalar integrals. -/

noncomputable section

namespace ExpandedFA.P1.CompactHullMeasureBarycenters

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u v

/-- Riesz–Markov regularization preserves complex as well as real tests. -/
theorem exists_regular_probability {X : Type v} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure X) (𝕜 : Type u) [RCLike 𝕜] :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν.Regular ∧
      ∀ f : C(X, 𝕜), ∫ x, f x ∂(μ : Measure X) = ∫ x, f x ∂ν := by
  obtain ⟨ν, hreg, hfin, hν⟩ :=
    Measure.exists_regular_eq_of_compactSpace (μ : Measure X)
  let : IsFiniteMeasure ν := hfin
  have hmass : IsProbabilityMeasure ν := by
    apply isProbabilityMeasure_iff_real.mpr
    simpa using (hν (BoundedContinuousFunction.const X (1 : ℝ))).symm
  refine ⟨ν, hmass, hreg, ?_⟩
  intro f
  have hfμ : Integrable f (μ : Measure X) := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hfν : Integrable f ν := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  apply RCLike.ext
  · rw [← integral_re hfμ, ← integral_re hfν]
    exact hν (ContinuousMap.equivBoundedOfCompact X ℝ
      ⟨fun x => RCLike.re (f x), RCLike.continuous_re.comp f.continuous⟩)
  · rw [← integral_im hfμ, ← integral_im hfν]
    exact hν (ContinuousMap.equivBoundedOfCompact X ℝ
      ⟨fun x => RCLike.im (f x), RCLike.continuous_im.comp f.continuous⟩)

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E]

/-- The moments of a probability measure, indexed by the original continuous dual. -/
private def moments (K : Set E) [MeasurableSpace K] (μ : ProbabilityMeasure K) :
    (E →L[𝕜] 𝕜) → 𝕜 := fun ℓ => ∫ x : K, ℓ (x : E) ∂(μ : Measure K)

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] in
private theorem continuous_moments (K : Set E) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] : Continuous (moments (𝕜 := 𝕜) K) := by
  apply continuous_pi
  intro ℓ
  let f : BoundedContinuousFunction K 𝕜 := ContinuousMap.equivBoundedOfCompact K 𝕜
    ⟨fun x => ℓ (x : E), ℓ.continuous.comp continuous_subtype_val⟩
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).mp
    (continuous_id.continuousAt : ContinuousAt (fun ν : ProbabilityMeasure K => ν) μ) f

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Scalar moment vectors of probabilities form a convex set. -/
private theorem convex_range_moments (K : Set E) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] :
    Convex ℝ (range (moments (𝕜 := 𝕜) K)) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  let ρ : Measure K := a' • (μ : Measure K) + b' • (ν : Measure K)
  have hρ : IsProbabilityMeasure ρ := by
    constructor
    change (a' • (μ : Measure K) + b' • (ν : Measure K)) univ = 1
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
    rw [← ENNReal.coe_add]
    have hab' : a' + b' = 1 := by
      apply Subtype.ext
      exact hab
    exact congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) hab'
  refine ⟨⟨ρ, hρ⟩, ?_⟩
  funext ℓ
  have hiμ : Integrable (fun x : K => ℓ (x : E)) (μ : Measure K) :=
    (ℓ.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiν : Integrable (fun x : K => ℓ (x : E)) (ν : Measure K) :=
    (ℓ.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ x : K, ℓ (x : E) ∂ρ) = a • _ + b • _
  rw [show ρ = a' • (μ : Measure K) + b' • (ν : Measure K) from rfl,
    integral_add_measure hiμ.smul_measure_nnreal hiν.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  rfl

/-- In fact compactness of the hull and separation by the dual are unnecessary
for this direction: compactness of K suffices to represent the scalar tests. -/
theorem representing_probability : Spec.RepresentingProbability.{u,v} := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ _hsep K hK _hC b hb
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set E := (fun x : E => fun ℓ : E →L[𝕜] 𝕜 => ℓ x) ⁻¹'
    range (moments (𝕜 := 𝕜) K)
  have hclosed : IsClosed S := by
    apply (isCompact_range (continuous_moments (𝕜 := 𝕜) K)).isClosed.preimage
    exact continuous_pi (fun ℓ => ℓ.continuous)
  have hconvex : Convex ℝ S := by
    intro x hx y hy a c ha hc hac
    have h := convex_range_moments (𝕜 := 𝕜) K hx hy ha hc hac
    have heq : (fun ℓ : E →L[𝕜] 𝕜 => ℓ (a • x + c • y)) =
        a • (fun ℓ : E →L[𝕜] 𝕜 => ℓ x) + c • (fun ℓ : E →L[𝕜] 𝕜 => ℓ y) := by
      funext ℓ
      simp only [Pi.add_apply, Pi.smul_apply, map_add,
        ContinuousLinearMap.map_smul_of_tower]
    change (fun ℓ : E →L[𝕜] 𝕜 => ℓ (a • x + c • y)) ∈ range (moments (𝕜 := 𝕜) K)
    rw [heq]
    exact h
  have hKS : K ⊆ S := by
    intro x hx
    refine ⟨(Measure.dirac (⟨x, hx⟩ : K)).toProbabilityMeasure, ?_⟩
    funext ℓ
    change (∫ y : K, ℓ (y : E) ∂Measure.dirac (⟨x, hx⟩ : K)) = ℓ x
    rw [integral_dirac]
  have hbS : b ∈ S := closure_minimal (convexHull_min hKS hconvex) hclosed hb
  obtain ⟨μ, hμ⟩ := hbS
  obtain ⟨ν, hprob, hreg, hν⟩ := exists_regular_probability μ 𝕜
  let : IsProbabilityMeasure ν := hprob
  refine ⟨ν, hprob, hreg, ?_⟩
  intro ℓ
  let f : C(K, 𝕜) := ⟨fun x => ℓ (x : E), ℓ.continuous.comp continuous_subtype_val⟩
  refine ⟨f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _), ?_⟩
  exact (congrFun hμ ℓ).symm.trans (hν f)

end ExpandedFA.P1.CompactHullMeasureBarycenters
