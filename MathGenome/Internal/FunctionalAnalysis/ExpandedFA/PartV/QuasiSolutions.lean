import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.QuasiSolutions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-! Quasi-solutions on Hilbert balls and minimum-norm discrepancy solutions. -/

noncomputable section
open Set
open scoped InnerProductSpace

namespace ExpandedFA.PartV.QuasiSolutions
universe u v w

/-- Real Hilbert spaces are reflexive for the scalar-linear continuous dual. -/
theorem real_hilbert_bidual_surjective (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
  intro F
  let l : StrongDual ℝ H := F.comp (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  let x := (InnerProductSpace.toDual ℝ H).symm l
  refine ⟨x, ?_⟩
  ext g
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective g
  change (InnerProductSpace.toDual ℝ H y) x = F (InnerProductSpace.toDual ℝ H y)
  change ⟪y, x⟫_ℝ = l y
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

/-- A closed bounded convex subset of a real Hilbert space is weakly compact.
The bidual embedding and Banach–Alaoglu preserve the original norm boundedness. -/
theorem weaklyCompact_of_closed_bounded_convex (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H)
    (hc : IsClosed C) (hb : Bornology.IsBounded C) (hv : Convex ℝ C) :
    IsCompact (toWeakSpace ℝ H '' C) := by
  have hclosed : IsClosed (toWeakSpace ℝ H '' C) := by
    rw [← closure_eq_iff_isClosed, ← hv.toWeakSpace_closure ℝ, hc.closure_eq]
  rw [← hclosed.closure_eq]
  apply NormedSpace.isCompact_closure_of_isBounded ℝ H
  · simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ H).injective] using hb
  · intro y _
    obtain ⟨x, hx⟩ := real_hilbert_bidual_surjective H (WeakDual.toStrongDual y)
    exact ⟨toWeakSpace ℝ H x, congrArg StrongDual.toWeakDual hx⟩

/-- The image of a Hilbert ball under a bounded linear map is norm closed.
Compactness here is in the weak topology, not the norm topology. -/
theorem isClosed_image_closedBall_real (X : Type*) (Y : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (A : X →L[ℝ] Y) (c : X) (r : ℝ) :
    IsClosed (A '' Metric.closedBall c r) := by
  have hc := weaklyCompact_of_closed_bounded_convex X (Metric.closedBall c r)
    Metric.isClosed_closedBall Metric.isBounded_closedBall (convex_closedBall c r)
  have hi := hc.image (WeakSpace.map A).continuous
  have heq : (WeakSpace.map A) '' (toWeakSpace ℝ X '' Metric.closedBall c r) =
      toWeakSpace ℝ Y '' (A '' Metric.closedBall c r) := by
    rw [Set.image_image, Set.image_image]
    rfl
  rw [heq] at hi
  have := hi.isClosed.preimage (toWeakSpaceCLM ℝ Y).continuous
  change IsClosed ((toWeakSpace ℝ Y) ⁻¹' (toWeakSpace ℝ Y '' (A '' Metric.closedBall c r))) at this
  simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ Y).injective] using this

/-- Weak compactness makes the image ball closed, so nearest-point projection
in the target gives residual attainment, even when A has nonclosed range. -/
theorem residual_minimum_on_ball : Spec.ResidualMinimumOnBall.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A f c r hr
  let := Hilbert.Conventions.realification 𝕜 X
  let := Hilbert.Conventions.realification 𝕜 Y
  have hclosed := isClosed_image_closedBall_real X Y (A.restrictScalars ℝ) c r
  have hv : Convex ℝ (A '' Metric.closedBall c r) :=
    (convex_closedBall c r).linear_image (A.restrictScalars ℝ).toLinearMap
  have hne : (A '' Metric.closedBall c r).Nonempty :=
    ⟨A c, c, Metric.mem_closedBall_self hr, rfl⟩
  obtain ⟨y, ⟨⟨x, hx, hxy⟩, hmin⟩, _⟩ :=
    Hilbert.Projection.existsUnique_nearestPoint ℝ Y _ hne hclosed hv f
  refine ⟨x, hx, ?_⟩
  intro z hz
  rw [hxy, norm_sub_rev, norm_sub_rev (A z)]
  exact hmin (A z) ⟨z, hz, rfl⟩

theorem unique_residual_minimum_on_ball : Spec.UniqueResidualMinimumOnBall.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A hA f c r hr
  let := Hilbert.Conventions.realification 𝕜 X
  let := Hilbert.Conventions.realification 𝕜 Y
  have hclosed := isClosed_image_closedBall_real X Y (A.restrictScalars ℝ) c r
  have hv : Convex ℝ (A '' Metric.closedBall c r) :=
    (convex_closedBall c r).linear_image (A.restrictScalars ℝ).toLinearMap
  have hne : (A '' Metric.closedBall c r).Nonempty :=
    ⟨A c, c, Metric.mem_closedBall_self hr, rfl⟩
  obtain ⟨y, ⟨⟨x, hx, hxy⟩, hmin⟩, huniq⟩ :=
    Hilbert.Projection.existsUnique_nearestPoint ℝ Y _ hne hclosed hv f
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · intro z hz
    rw [hxy, norm_sub_rev, norm_sub_rev (A z)]
    exact hmin (A z) ⟨z, hz, rfl⟩
  · intro z hz
    apply hA
    rw [hxy]
    apply huniq (A z)
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [norm_sub_rev f, norm_sub_rev f]
    exact hz.2 t ht

/-- A nonempty discrepancy set is closed and real convex. Projection of zero
therefore gives its unique minimum-norm member. -/
theorem unique_minimum_norm_discrepancy : Spec.UniqueMinimumNormDiscrepancy.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A f δ _hδ hne
  let := Hilbert.Conventions.realification 𝕜 X
  let := Hilbert.Conventions.realification 𝕜 Y
  let C : Set X := {x | ‖A x - f‖ ≤ δ}
  have hC : C = A ⁻¹' Metric.closedBall f δ := by
    ext x
    simp only [C, Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have hclosed : IsClosed C := by
    rw [hC]
    exact Metric.isClosed_closedBall.preimage A.continuous
  have hv : Convex ℝ C := by
    rw [hC]
    exact (convex_closedBall f δ).linear_preimage (A.restrictScalars ℝ).toLinearMap
  obtain ⟨x, hx, huniq⟩ :=
    Hilbert.Projection.existsUnique_nearestPoint ℝ X C hne hclosed hv 0
  refine ⟨x, ?_, ?_⟩
  · simpa only [C, Set.mem_ofPred_eq, zero_sub, norm_neg] using hx
  · intro z hz
    apply huniq z
    simpa only [C, Set.mem_ofPred_eq, zero_sub, norm_neg] using hz

end ExpandedFA.PartV.QuasiSolutions
