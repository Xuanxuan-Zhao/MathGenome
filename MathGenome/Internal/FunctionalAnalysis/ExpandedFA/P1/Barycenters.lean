import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Barycenters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.CompactHullMeasureBarycenters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Compact barycenters without local convexity. For a finite collection of
dual tests, its joint map has finite-dimensional range. The integral lies in
the compact convex image of the given hull. Compactness then realizes all
tests simultaneously, and the separating dual gives uniqueness.
-/

noncomputable section

namespace ExpandedFA.P1.Barycenters

open Set MeasureTheory
open scoped Topology

universe u v w

theorem barycenter_exists_unique : Spec.BarycenterExistsUnique.{u,v,w} := by
  intro 𝕜 E Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsep μ _ _hreg f hf hC
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let C := closure (convexHull ℝ (range f))
  have hconv : Convex ℝ C := (convex_convexHull ℝ (range f)).closure
  have hfC : ∀ q, f q ∈ C := fun q => subset_closure (subset_convexHull ℝ _ (mem_range_self q))
  let A : (E →L[𝕜] 𝕜) → Set E := fun ℓ =>
    {b | ℓ b = ∫ q, ℓ (f q) ∂μ}
  have hclosed : ∀ ℓ, IsClosed (A ℓ) := fun ℓ =>
    isClosed_eq ℓ.continuous continuous_const
  have hfinite : ∀ s : Finset (E →L[𝕜] 𝕜), (C ∩ ⋂ ℓ ∈ s, A ℓ).Nonempty := by
    intro s
    let g : E →L[ℝ] (s → 𝕜) :=
      ContinuousLinearMap.pi (fun ℓ => ℓ.val.restrictScalars ℝ)
    have hgi : Integrable (fun q => g (f q)) μ :=
      (g.continuous.comp hf).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hmem : (∫ q, g (f q) ∂μ) ∈ g '' C :=
      (hconv.linear_image g.toLinearMap).integral_mem
        (hC.image g.continuous).isClosed
        (Filter.Eventually.of_forall fun q => mem_image_of_mem g (hfC q)) hgi
    obtain ⟨b, hb, hgb⟩ := hmem
    refine ⟨b, hb, ?_⟩
    simp only [mem_iInter]
    intro ℓ hℓ
    have heq := congrFun hgb (⟨ℓ, hℓ⟩ : s)
    have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : s => 𝕜)
      (⟨ℓ, hℓ⟩ : s)).integral_comp_comm hgi
    exact heq.trans hproj.symm
  obtain ⟨b, hb, hbA⟩ := hC.inter_iInter_nonempty A hclosed hfinite
  have hbtest : ∀ ℓ : E →L[𝕜] 𝕜,
      Integrable (fun q => ℓ (f q)) μ ∧ ℓ b = ∫ q, ℓ (f q) ∂μ := by
    intro ℓ
    exact ⟨(ℓ.continuous.comp hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _), mem_iInter.mp hbA ℓ⟩
  refine ⟨b, ⟨hb, hbtest⟩, ?_⟩
  intro c hc
  by_contra hcb
  obtain ⟨ℓ, hℓ⟩ := hsep c b hcb
  exact hℓ ((hc.2 ℓ).2.trans (hbtest ℓ).2.symm)

theorem representing_probability : Spec.RepresentingProbability.{u,v} :=
  CompactHullMeasureBarycenters.representing_probability

theorem barycenter_norm_estimate : Spec.BarycenterNormEstimate.{u,v,w} := by
  intro 𝕜 E Q _ _ _ _ _ _ _ _ _ μ _ _hreg f hf b hb
  have hnorm : Integrable (fun q => ‖f q‖) μ :=
    hf.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨ℓ, hℓ, hℓb⟩ := C05Norming.norming_functional 𝕜 E b
  have hi : Integrable (fun q => ℓ (f q)) μ :=
    (ℓ.continuous.comp hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hnorm, ?_⟩
  calc
    ‖b‖ = ‖ℓ b‖ := by rw [hℓb, RCLike.norm_ofReal, abs_norm]
    _ = ‖∫ q, ℓ (f q) ∂μ‖ := by rw [hb]
    _ ≤ ∫ q, ‖ℓ (f q)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ q, ‖f q‖ ∂μ := by
      apply integral_mono hi.norm hnorm
      intro q
      exact (ℓ.le_opNorm (f q)).trans (by
        simpa using mul_le_mul_of_nonneg_right hℓ (norm_nonneg (f q)))

end ExpandedFA.P1.Barycenters
