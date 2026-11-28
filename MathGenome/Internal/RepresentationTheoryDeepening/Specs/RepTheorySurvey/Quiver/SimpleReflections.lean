import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Forms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Reflection

/-! The simple reflections of the quiver Tits form. -/

open scoped BigOperators Matrix

namespace RepTheorySurvey.Quiver.SimpleReflectionsSpec

-- The vertex, arrow, and coefficient types have independent universes.
set_option linter.checkUnivs false

universe u v r

abbrev VertexUnitType := ∀ {Q : Type u} (R : Type r) [CommRing R], Q → Q → R

/-- The unit vector at a vertex, with coefficients in the given ring. -/
noncomputable def vertexUnit : VertexUnitType.{u, r} :=
  fun {_} _ [_] i => open Classical in Pi.single i 1

abbrev SimpleReflectionType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (R : Type r) [CommRing R],
    Q → (Q → R) ≃ₗ[R] (Q → R)

/-- Reflection in the vertex unit vector, using the corresponding row of the polarization. -/
noncomputable def simpleReflection : SimpleReflectionType.{u, v, r} :=
  fun {Q} [_] [_] R [_] i =>
    Module.reflection (x := vertexUnit R i)
      (f := dotProductBilin R R ((FormsSpec.polarizationMatrix R).row i)) (by
        classical
        change (FormsSpec.polarizationMatrix R).row i ⬝ᵥ Pi.single i 1 = 2
        rw [dotProduct_single_one]
        simp [Matrix.row_apply, FormsSpec.polarizationMatrix])

abbrev IntegralVertexUnit : Prop :=
  ∀ {Q : Type u} (i : Q), vertexUnit ℤ i = FormsSpec.unitVector i

abbrev VertexUnitSquareLength : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (R : Type r) [CommRing R] (i : Q),
    vertexUnit R i ⬝ᵥ (FormsSpec.polarizationMatrix R *ᵥ vertexUnit R i) = 2

abbrev ReflectionFormula : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] {R : Type r} [CommRing R] (i : Q) (x : Q → R),
    simpleReflection R i x =
      x - (vertexUnit R i ⬝ᵥ (FormsSpec.polarizationMatrix R *ᵥ x)) • vertexUnit R i

abbrev ReflectionAtVertex : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] {R : Type r} [CommRing R],
    ¬ RM03.HasOrientedCycle Q → ∀ (i : Q) (x : Q → R),
      simpleReflection R i x i = -x i + ∑ j, (FormsSpec.edgeMultiplicity i j : R) * x j

abbrev ReflectionAtOtherVertex : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] {R : Type r} [CommRing R]
    {i j : Q}, j ≠ i → ∀ (x : Q → R), simpleReflection R i x j = x j

abbrev ReflectionInvolutive : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (R : Type r) [CommRing R] (i : Q),
    Function.Involutive (simpleReflection R i)

abbrev PreservesPolarization : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] {R : Type r} [CommRing R] (i : Q) (x y : Q → R),
    simpleReflection R i x ⬝ᵥ (FormsSpec.polarizationMatrix R *ᵥ simpleReflection R i y) =
      x ⬝ᵥ (FormsSpec.polarizationMatrix R *ᵥ y)

abbrev PreservesTitsForm : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)] {R : Type r} [CommRing R],
    ¬ RM03.HasOrientedCycle Q → ∀ (i : Q) (x : Q → R),
      FormsSpec.titsForm (simpleReflection R i x) = FormsSpec.titsForm x

abbrev ReflectionIntCast : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (i : Q) (x : FormsSpec.DimensionVector Q),
    simpleReflection ℝ i (fun j => (x j : ℝ)) = fun j => (simpleReflection ℤ i x j : ℝ)

end RepTheorySurvey.Quiver.SimpleReflectionsSpec
