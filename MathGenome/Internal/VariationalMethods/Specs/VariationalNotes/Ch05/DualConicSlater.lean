import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ConicProgramModels

/-! Independent statement of paper.tex, Corollary `cor:dual-slater`.
The dual value is a finite real number. The sole feasibility qualification
is relative strict feasibility of the dual slack. -/
noncomputable section
universe u v
namespace VariationalNotes.Ch05.DualConicSlater.Specs
open ConicProgramModels.Specs

def dual_conic_slater : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X),
    IsClosed K → ConvexGeometry.Specs.IsCone K →
    ∀ (d : ℝ), dualValue K A b c = (d : EReal) →
    (∃ y₀ : Y, c - A.adjoint y₀ ∈
      ConvexGeometry.Specs.relativeInterior (innerPositiveDual K)) →
    ∃ x ∈ primalFeasible K A b,
      inner ℝ c x = d ∧ primalValue K A b c = (d : EReal)

end VariationalNotes.Ch05.DualConicSlater.Specs
