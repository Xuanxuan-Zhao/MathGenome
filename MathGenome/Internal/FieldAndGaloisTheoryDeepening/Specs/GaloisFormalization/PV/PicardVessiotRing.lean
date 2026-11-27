import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.LinearSystem
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorLocalization
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! Independent specifications for Definition 1.6. -/
namespace GaloisFormalization.PV.Specs

universe u v

set_option linter.checkUnivs false in
def matrixGeneratedSubalgebraType :=
  (K : Type u) → [CommRing K] → {R : Type v} → [CommRing R] → [Algebra K R] →
    {n : ℕ} → Matrix.GeneralLinearGroup (Fin n) R → Subalgebra K R

def matrixGeneratedSubalgebra : matrixGeneratedSubalgebraType.{u, v} :=
  fun K _ _ _ _ _ Y =>
    Algebra.adjoin K (insert (determinantInverse Y)
      (Set.range fun ij : Fin _ × Fin _ => Y.val ij.1 ij.2))

section

variable {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
  [Algebra K R] {n : ℕ}

set_option linter.checkUnivs false in
def isPicardVessiotRingType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] →
    {R : Type v} → [CommRing R] → [Algebra K R] → {n : ℕ} →
    operatorField kind K → linearSystem kind K n → operator kind R → Prop

def isPicardVessiotRing (D : operatorField kind K) (A : linearSystem kind K n)
    (E : operator kind R) : Prop :=
  isExtension D E ∧ isSimple E ∧
    ∃ Y : Matrix.GeneralLinearGroup (Fin n) R,
      isFundamental A E Y ∧ matrixGeneratedSubalgebra K Y = ⊤

set_option linter.checkUnivs false in
def isPicardVessiotTotalExtensionType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] →
    {R : Type v} → [CommRing R] → [Algebra K R] → {n : ℕ} →
    operatorField kind K → linearSystem kind K n → operator kind R →
    operator kind (totalQuotientRing R) → Prop

def isPicardVessiotTotalExtension (D : operatorField kind K) (A : linearSystem kind K n)
    (E : operator kind R) (F : operator kind (totalQuotientRing R)) : Prop :=
  isPicardVessiotRing D A E ∧ isExtension E F

set_option linter.checkUnivs false in
def isPicardVessiotFieldType := isPicardVessiotTotalExtensionType.{u, v}

def isPicardVessiotField (D : operatorField kind K) (A : linearSystem kind K n)
    (E : operator kind R) (F : operator kind (totalQuotientRing R)) : Prop :=
  isPicardVessiotTotalExtension D A E F ∧ IsField (totalQuotientRing R)

def picardVessiotTotalExtensionExistsUnique :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ} (D : operatorField kind K) (A : linearSystem kind K n)
    (E : operator kind R), isPicardVessiotRing D A E →
      ∃! F : operator kind (totalQuotientRing R), isPicardVessiotTotalExtension D A E F

def picardVessiotTotalExtensionOverBase :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ} {D : operatorField kind K} {A : linearSystem kind K n}
    {E : operator kind R} {F : operator kind (totalQuotientRing R)},
      isPicardVessiotTotalExtension D A E F → isExtension D F

end
end GaloisFormalization.PV.Specs
