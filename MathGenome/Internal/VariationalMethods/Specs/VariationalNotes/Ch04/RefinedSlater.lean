import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.ConvexProgramModels
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statement of the refined Slater theorem, paper.tex §v04-06.
All three finite index types may be empty. The affine constraints need only
be feasible at the relative-interior witness. The dual uses exactly D. -/
noncomputable section
universe u v w z
namespace VariationalNotes.Ch04.Specs

open ConvexProgramSpecs

def refined_slater : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [FiniteDimensional ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]
    (q : ConvexProgram X I A J) (p : ℝ),
    primalValue q = (p : EReal) →
    (∃ x₀, x₀ ∈ ConvexGeometry.Specs.relativeInterior (commonDomain q) ∧
      x₀ ∈ affinePolyhedron q ∧ ∀ i, q.g i x₀ < 0) →
    ∃ m : Multipliers I A J, admissible m ∧
      dualFunction q m = (p : EReal) ∧ dualValue q = (p : EReal)

end VariationalNotes.Ch04.Specs
