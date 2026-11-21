import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.WeakSequentialCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Normed.Operator.Completeness

/-!
Sequential completeness in the weak topologies, paper.tex 6452–6467.
Scalar completeness and uniform boundedness give a continuous pointwise limit
in the dual. Apply that argument to the canonical images in the bidual and
use reflexivity to obtain the weak limit in the original space.
-/
namespace ExpandedFA.Supplements.WeakSequentialCompleteness

universe u v w
open Filter
open scoped Topology
noncomputable section

/-- Pointwise Cauchy sequences of functionals on a Banach space have
continuous linear pointwise limits. -/
lemma exists_dual_pointwise_limit (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (f : ℕ → E →L[𝕜] 𝕜) (hf : ∀ x, CauchySeq (fun n => f n x)) :
    ∃ g : E →L[𝕜] 𝕜, ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hf x)
  have hp : ∀ x, ∃ C, ∀ n, ‖f n x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := (hf x).isBounded_range.exists_norm_le
    exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
  obtain ⟨C, _, hC⟩ := P1.C07UniformBoundedness.uniform_boundedness 𝕜 E 𝕜 ℕ f hp
  have hb : Bornology.IsBounded (Set.range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩
  exact ⟨ContinuousLinearMap.ofTendstoOfBoundedRange g f (tendsto_pi_nhds.mpr hg) hb, hg⟩

/-- Scalar-test convergence implies convergence for the shared initial topology. -/
private lemma tendsto_dualPair (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (x : ℕ → X) (z : X)
    (h : ∀ y, Tendsto (fun n => B y (x n)) atTop (𝓝 (B y z))) :
    Tendsto x atTop (@nhds X (P1.C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B) z) := by
  rw [P1.dualPairTopology_initial, nhds_iInf]
  simp only [Filter.tendsto_iInf, nhds_induced, Filter.tendsto_comap_iff]
  exact h

/-- The dual of a Banach space is weak-star sequentially complete. -/
theorem dual_weakStar_sequentially_complete : Spec.DualWeakStarSequentialCompleteness := by
  intro 𝕜 E _ _ _ _ f hf
  obtain ⟨g, hg⟩ := exists_dual_pointwise_limit 𝕜 E f hf
  exact ⟨g, tendsto_dualPair 𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip f g hg⟩

/-- Every reflexive Banach space is weakly sequentially complete. -/
theorem reflexive_weak_sequentially_complete : Spec.ReflexiveWeakSequentialCompleteness := by
  intro 𝕜 E _ _ _ _ h x hx
  obtain ⟨Φ, hΦ⟩ := exists_dual_pointwise_limit 𝕜 (E →L[𝕜] 𝕜)
    (fun n => P1.C04CanonicalMap.canonicalEvaluation 𝕜 E (x n)) hx
  obtain ⟨z, hz⟩ := h Φ
  refine ⟨z, tendsto_dualPair 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) x z ?_⟩
  intro f
  have heq : Φ f = f z := by rw [← hz]; rfl
  change Tendsto (fun n => f (x n)) atTop (𝓝 (f z))
  simpa only [P1.C04CanonicalMap.canonicalEvaluation_apply, heq] using hΦ f

end
end ExpandedFA.Supplements.WeakSequentialCompleteness
