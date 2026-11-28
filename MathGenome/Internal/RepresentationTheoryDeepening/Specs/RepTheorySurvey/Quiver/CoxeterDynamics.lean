import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SinkCycle

/-! Periodicity and sign change for a positive-definite Coxeter operator. -/

open scoped Matrix

universe u v r

namespace RepTheorySurvey.Quiver.CoxeterDynamicsSpec

open FormsSpec SinkCycleSpec

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)]

/-- A fixed integral Tits level fits inside one box in the vertex coordinates. -/
abbrev IntegralLevelBounded (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] : Prop :=
  ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ b : ℤ, ∃ B : ℤ, 0 ≤ B ∧
      ∀ d : DimensionVector Q, titsForm d = b → ∀ i : Q, |d i| ≤ B

/-- In particular, the integral level of value one is finite. -/
abbrev IntegralLevelFinite (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] : Prop :=
  ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ b : ℤ, {d : DimensionVector Q | titsForm d = b}.Finite

/-- The same positive period works for the integral operator and its real extension.
Powers of the linear equivalence use composition. -/
abbrev CoxeterPeriod (number : Q ≃ Fin (Fintype.card Q)) : Prop :=
  ∃ h : ℕ, 0 < h ∧ (coxeter number ℤ) ^ h = 1 ∧ (coxeter number ℝ) ^ h = 1

abbrev CoxeterFixedVector (number : Q ≃ Fin (Fintype.card Q)) : Prop :=
  ∀ x : Q → ℝ, coxeter number ℝ x = x → x = 0

abbrev CoxeterNegativeReal (number : Q ≃ Fin (Fintype.card Q)) : Prop :=
  ∀ x : Q → ℝ, x ≠ 0 → (∀ i, 0 ≤ x i) →
    ∃ m : ℕ, ∃ i : Q, ((coxeter number ℝ) ^ m) x i < 0

abbrev CoxeterNegativeIntegral (number : Q ≃ Fin (Fintype.card Q)) : Prop :=
  ∀ x : DimensionVector Q, x ≠ 0 → (∀ i, 0 ≤ x i) →
    ∃ m : ℕ, ∃ i : Q, ((coxeter number ℤ) ^ m) x i < 0

abbrev FiniteOrder (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] : Prop :=
  ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number → CoxeterPeriod number

abbrev OnlyZeroFixed (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] : Prop :=
  ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number → CoxeterFixedVector number

abbrev NegativeCoordinateReal (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] : Prop :=
  ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number → CoxeterNegativeReal number

abbrev NegativeCoordinateIntegral (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] : Prop :=
  ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number → CoxeterNegativeIntegral number

/-- The full sink-cycle lemma for a finite acyclic quiver. The positive-definiteness
hypothesis applies only to the assertions about powers and fixed vectors. -/
abbrev FullSinkCycle (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] : Prop :=
  ¬ RM03.HasOrientedCycle Q →
    (∃ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number) ∧
    ∀ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number →
      (∀ a : RM03.Arrow Q, endpointsAt number 0 a = (a.1, a.2.1)) ∧
      (∀ i : Fin (Fintype.card Q), ∀ j : Q,
        IsEmpty ((quiverAt number i.val).Hom (number.symm i) j)) ∧
      (∀ (i : Fin (Fintype.card Q)) (a : RM03.Arrow Q),
        endpointsAt number (i.val + 1) a =
          reverseIncident (number.symm i) (endpointsAt number i.val a)) ∧
      (∀ a : RM03.Arrow Q, endpointsAt number (Fintype.card Q) a = (a.1, a.2.1)) ∧
      (∀ (R : Type r) [CommRing R], open Classical in
        IsUnit (eulerMatrix number R) ∧
          coxeterMatrix number R = -(eulerMatrix number R)⁻¹ * (eulerMatrix number R)ᵀ) ∧
      (PositiveDefinite Q → CoxeterPeriod number ∧ CoxeterFixedVector number ∧
        CoxeterNegativeReal number ∧ CoxeterNegativeIntegral number)

abbrev IntegralLevelBoundedStatement : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)], IntegralLevelBounded Q

abbrev IntegralLevelFiniteStatement : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)], IntegralLevelFinite Q

abbrev FiniteOrderStatement : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)], FiniteOrder Q

abbrev OnlyZeroFixedStatement : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)], OnlyZeroFixed Q

abbrev NegativeCoordinateRealStatement : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)], NegativeCoordinateReal Q

abbrev NegativeCoordinateIntegralStatement : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)], NegativeCoordinateIntegral Q

abbrev FullSinkCycleStatement : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)], FullSinkCycle.{u, v, r} Q

end RepTheorySurvey.Quiver.CoxeterDynamicsSpec
