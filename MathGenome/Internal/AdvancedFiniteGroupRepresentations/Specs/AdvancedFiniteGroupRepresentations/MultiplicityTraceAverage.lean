import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorCycleTrace
import Mathlib.RepresentationTheory.Character

/-! FR-D07, second identity, source lines 1551–1559 and 1574–1583.
The action on the original Specht module is its inherited tabloid action;
`tensorMultiplicityOperator` is postcomposition on the actual equivariant Hom
space. The statement includes degree zero and zero-dimensional vector spaces.
-/
noncomputable section
open scoped BigOperators
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The ordinary character average, with the inverse in the Specht character. -/
def multiplicity_trace_averageType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p)),
    InheritedSpechtAction p σ → ∀ g : LinearGroup V,
      LinearMap.trace ℂ (TensorMultiplicity V p) (tensorMultiplicityOperator V p g) =
        (n.factorial : ℂ)⁻¹ * ∑ s : SymmetricGroup n,
          σ.character s⁻¹ * cycleTraceProduct V s g

end Specs.AdvancedFiniteGroupRepresentations
