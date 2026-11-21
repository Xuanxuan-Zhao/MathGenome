import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.CompatibleConvexClosedSets
import Mathlib.Analysis.LocallyConvex.Separation

/-!
The compatible-topology clause of `fa2:p1:general-bipolar`.

A closed real-convex set is the intersection of all closed halfspaces
containing it. Over complex scalars these halfspaces use real parts of
continuous complex-linear functionals. If these functionals are continuous
in the second topology, all those halfspaces are closed there too. Apply
this argument in both directions. It includes the empty set and the zero
vector space; the halfspace representation needs no nonemptiness premise.
-/
namespace ExpandedFA.P1

private theorem isClosed_of_dual_continuous
    {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [t₁ : TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    (t₂ : TopologicalSpace E)
    (hdual : ∀ f : E →ₗ[𝕜] 𝕜,
      @Continuous E 𝕜 t₁ inferInstance f → @Continuous E 𝕜 t₂ inferInstance f)
    {C : Set E} (hconv : Convex ℝ C) (hclosed : @IsClosed E t₁ C) :
    @IsClosed E t₂ C := by
  let : TopologicalSpace E := t₁
  have hhalf := RCLike.iInter_halfSpaces_eq' (𝕜 := 𝕜) hconv hclosed
  have hclosed_half : ∀ (f : E →L[𝕜] 𝕜) (c : ℝ),
      @IsClosed E t₂ {x | RCLike.re (f x) ≤ c} := by
    intro f c
    have hf := hdual f.toLinearMap f.continuous
    let : TopologicalSpace E := t₂
    exact isClosed_le (RCLike.continuous_re.comp hf) continuous_const
  let : TopologicalSpace E := t₂
  rw [← hhalf]
  exact isClosed_iInter fun f => isClosed_iInter fun c =>
    isClosed_iInter fun _ => hclosed_half f c

/-- The same scalar-linear continuous dual determines all closed convex sets. -/
theorem compatible_convex_closed_sets :
    Specs.ExpandedFA.P1.CompatibleConvexClosedSets.compatibleConvexClosedSetsType := by
  intro 𝕜 E _ _ _ _ _ t₁ t₂ h₁ h₂ _ _ hdual C hconv
  constructor
  · intro hclosed
    let : TopologicalSpace E := t₁
    let : IsTopologicalAddGroup E := h₁.1.1
    let : ContinuousSMul 𝕜 E := h₁.1.2
    let : LocallyConvexSpace ℝ E := h₁.2
    exact isClosed_of_dual_continuous t₂ (fun f hf => (hdual f).mp hf) hconv hclosed
  · intro hclosed
    let : TopologicalSpace E := t₂
    let : IsTopologicalAddGroup E := h₂.1.1
    let : ContinuousSMul 𝕜 E := h₂.1.2
    let : LocallyConvexSpace ℝ E := h₂.2
    exact isClosed_of_dual_continuous t₁ (fun f hf => (hdual f).mpr hf) hconv hclosed

end ExpandedFA.P1
