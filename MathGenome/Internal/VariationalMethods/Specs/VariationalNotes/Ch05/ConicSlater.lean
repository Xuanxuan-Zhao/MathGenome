import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ConicProgramModels

/-! Independent statement of paper.tex, Theorem `thm:conic-slater`.
The cone contains zero; relative interior is taken in its affine hull.
Neither primal attainment nor surjectivity of A is assumed or concluded. -/
noncomputable section
universe u v
namespace VariationalNotes.Ch05.ConicSlater.Specs
open ConicProgramModels.Specs

def conic_slater : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X),
    IsClosed K → ConvexGeometry.Specs.IsCone K →
    ∀ (p : ℝ), primalValue K A b c = (p : EReal) →
    (∃ x₀ ∈ ConvexGeometry.Specs.relativeInterior K, A x₀ = b) →
    ∃ y ∈ dualFeasible K A c,
      inner ℝ b y = p ∧ dualValue K A b c = (p : EReal)

end VariationalNotes.Ch05.ConicSlater.Specs
