import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SinkCycle

/-! First negative step of the cyclic sink schedule on an integral Tits root. -/

-- The vertex and arrow universes are independent.
set_option linter.checkUnivs false

universe u v

namespace RepTheorySurvey.Quiver.RootVectorReductionSpec

open FormsSpec SimpleReflectionsSpec SinkCycleSpec

abbrev VectorAtStepType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q],
    (Q ≃ Fin (Fintype.card Q)) → ℕ → DimensionVector Q → DimensionVector Q

/-- The vector after `m` reflections, with complete passes followed by the
prefix of the next pass. -/
noncomputable def vectorAtStep : VectorAtStepType.{u, v} :=
  fun {Q} [_] [_] number m d =>
    coxeterPrefix number ℤ (m % Fintype.card Q)
      (((coxeter number ℤ) ^ (m / Fintype.card Q)) d)

/-- A step applies the reflection at the current rank of the repeated numbering,
including the last reflection of each pass. -/
abbrev VectorAtStepSucc : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q]
    (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) (i : Fin (Fintype.card Q)),
    i.val = m % Fintype.card Q → ∀ d : DimensionVector Q,
      vectorAtStep number (m + 1) d =
        simpleReflection ℤ (number.symm i) (vectorAtStep number m d)

/-- The first reflection to create a negative entry acts on the unit vector at
its active sink. Here the first `m` reflections leave all entries nonnegative. -/
abbrev FirstNegativeStep : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ (number : Q ≃ Fin (Fintype.card Q)), IsSinkNumbering number →
    ∀ d : DimensionVector Q, (∀ j, 0 ≤ d j) → titsForm d = 1 →
      ∃ (m : ℕ) (i : Fin (Fintype.card Q)),
        i.val = m % Fintype.card Q ∧
        (∀ k ≤ m, ∀ j, 0 ≤ vectorAtStep number k d j) ∧
        vectorAtStep number m d = unitVector (number.symm i) ∧
        vectorAtStep number (m + 1) d (number.symm i) < 0

end RepTheorySurvey.Quiver.RootVectorReductionSpec
