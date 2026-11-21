import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup

/-! Independent statement of `fa2:p2:meridian`, in the real, three-dimensional
convex-body setting of the chapter. A value-normalized support f gives the
height coordinate in ker f ⊕ ℝp. The section equivalence is asserted on all
points, so in particular includes the supporting levels ±1. -/
namespace Specs.ExpandedFA.HilbertCharacterization.Meridians

universe u
open Set ConvexBodySetup

def meridiansType : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (K : Set V), ProjectionBody K →
    ∀ p ∈ frontier K, ∃ f : V →L[ℝ] ℝ,
      f ∈ NormalCone K p ∧ f p = 1 ∧
      ∀ (L M : Submodule ℝ V), Module.finrank ℝ L = 2 →
        Module.finrank ℝ M = 2 → ∀ (hpL : p ∈ L) (hpM : p ∈ M),
        ∃ A : L ≃ₗ[ℝ] M,
          A ⟨p, hpL⟩ = ⟨p, hpM⟩ ∧
          (∀ x : L, f (A x : V) = f (x : V)) ∧
          (∀ x : L, (A x : V) ∈ K ↔ (x : V) ∈ K)

end Specs.ExpandedFA.HilbertCharacterization.Meridians
