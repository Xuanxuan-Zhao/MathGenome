import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups

noncomputable section

namespace LinearAlgebraicGroups.Specs.MatrixExamples

open Arithmetic Arithmetic.AdelicGroups
open GeneralLinearStructure (SpecialMatrixPoints)
open IntegralModels (MatrixRealization)

/-- The places and completions of the number field of rational numbers. -/
abbrev rationalPlaces : GlobalFieldData.{0, 0} ℚ := .number inferInstance

/-- The unique archimedean place of `ℚ`, omitted in the finite adelic group. -/
def archimedeanPlaces : Finset rationalPlaces.Place :=
  {Sum.inr Rat.infinitePlace}

/-- For each size at least two, the group with determinant-one matrix points has
a closed matrix realization and its rational diagonal is dense in its finite adeles
in every closed realization. -/
def RationalStrongApproximation : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∃ G : AffineAlgebraicGroup ℚ, Nonempty (SpecialMatrixPoints G n) ∧
      Nonempty (MatrixRealization G) ∧
      ∀ i : MatrixRealization G, StrongApproximation rationalPlaces i archimedeanPlaces

/-- The real determinant-one matrix group with its usual matrix topology is noncompact. -/
def RealNoncompact : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬ IsCompact (Set.univ : Set (Matrix.SpecialLinearGroup (Fin n) ℝ))

end LinearAlgebraicGroups.Specs.MatrixExamples
