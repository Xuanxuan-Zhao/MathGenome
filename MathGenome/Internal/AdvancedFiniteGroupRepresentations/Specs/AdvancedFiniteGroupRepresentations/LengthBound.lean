import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation

/-! The exact length bound, FR-D05, source lines 1470–1510.
`Nontrivial` expresses nonvanishing of the actual equivariant Hom space.
No positivity hypothesis on n or on the dimension is imposed. -/
noncomputable section
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

def tensorMultiplicity_nonzero_iffType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (p : Partition n),
    Nontrivial (TensorMultiplicity V p) ↔ length p ≤ Module.finrank ℂ V

end Specs.AdvancedFiniteGroupRepresentations
