import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.LinearSystem
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorLocalization
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

namespace GaloisFormalization.PV

universe u v

/-- Adjoin the entries of an invertible matrix and the inverse of its determinant unit. -/
def matrixGeneratedSubalgebra (K : Type u) [CommRing K] {R : Type v}
    [CommRing R] [Algebra K R] {n : ℕ} (Y : Matrix.GeneralLinearGroup (Fin n) R) :
    Subalgebra K R :=
  Algebra.adjoin K (insert (LinearSystem.determinantInverse Y)
    (Set.range fun ij : Fin n × Fin n => Y.val ij.1 ij.2))

variable {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
  [Algebra K R] {n : ℕ}

/-- A simple operator extension generated over the base field by a fundamental
matrix and its inverse determinant. -/
def IsPicardVessiotRing (D : OperatorField kind K) (A : LinearSystem kind K n)
    (E : Operator kind R) : Prop :=
  D.IsExtension E ∧ E.IsSimple ∧
    ∃ Y : Matrix.GeneralLinearGroup (Fin n) R,
      A.IsFundamental E Y ∧ matrixGeneratedSubalgebra K Y = ⊤

/-- The total extension of a Picard–Vessiot ring is its total quotient ring
with the unique operator extending the operator on the ring. -/
def IsPicardVessiotTotalExtension (D : OperatorField kind K) (A : LinearSystem kind K n)
    (E : Operator kind R) (F : Operator kind (TotalQuotientRing R)) : Prop :=
  IsPicardVessiotRing D A E ∧ E.IsExtension F

/-- A Picard–Vessiot total extension is a Picard–Vessiot field if its
underlying ring is a field. -/
def IsPicardVessiotField (D : OperatorField kind K) (A : LinearSystem kind K n)
    (E : Operator kind R) (F : Operator kind (TotalQuotientRing R)) : Prop :=
  IsPicardVessiotTotalExtension D A E F ∧ IsField (TotalQuotientRing R)

variable {D : OperatorField kind K} {A : LinearSystem kind K n} {E : Operator kind R}

/-- The canonical localization operator gives the Picard–Vessiot total extension. -/
theorem IsPicardVessiotRing.totalExtension (h : IsPicardVessiotRing D A E) :
    IsPicardVessiotTotalExtension D A E E.totalQuotient :=
  ⟨h, E.fractionOperator_isExtension⟩

theorem IsPicardVessiotRing.existsUnique_totalExtension (D : OperatorField kind K)
    (A : LinearSystem kind K n) (E : Operator kind R) (h : IsPicardVessiotRing D A E) :
    ∃! F : Operator kind (TotalQuotientRing R), IsPicardVessiotTotalExtension D A E F := by
  obtain ⟨F, hF, huniq⟩ := Operator.fractionOperator_existsUnique (K := TotalQuotientRing R) E
  exact ⟨F, ⟨h, hF, IsFractionRing.injective R _⟩, fun G hG => huniq G hG.2.1⟩

/-- The induced algebra map embeds the base field as an operator subring of the
total quotient ring. -/
theorem IsPicardVessiotTotalExtension.isExtension {F : Operator kind (TotalQuotientRing R)}
    (h : IsPicardVessiotTotalExtension D A E F) : D.IsExtension F := by
  rw [Operator.IsExtension, Operator.IsAlgebra, IsScalarTower.algebraMap_eq K R]
  exact ⟨h.2.1.comp h.1.1.1, h.2.2.comp h.1.1.2⟩

end GaloisFormalization.PV
