import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Derivative

namespace GaloisFormalization.PV.Specs

universe u v

open scoped Matrix

/-- The derivative on the rational function field over `C` is normalized
by vanishing on coefficients and taking the indeterminate to one. -/
def isRationalDerivative {C : Type u} [Field C]
    (D : operatorField .differential (RatFunc C)) : Prop :=
  (∀ c : C, apply D (algebraMap C (RatFunc C) c) = 0) ∧
    apply D (RatFunc.X : RatFunc C) = 1

def rationalDerivativeExistsUnique : Prop :=
  ∀ (C : Type u) [Field C],
    ∃! D : operatorField .differential (RatFunc C), isRationalDerivative D

/-- The constant field is identified with `C` by the coefficient embedding. -/
def rationalDerivativeConstants : Prop :=
  ∀ {C : Type u} [Field C] [CharZero C]
    (D : operatorField .differential (RatFunc C)), isRationalDerivative D →
    ∃ e : C ≃+* constantSubfield D, ∀ c : C,
      (e c : RatFunc C) = algebraMap C (RatFunc C) c

def rationalLogDerivative : Prop :=
  ∀ {C : Type u} [Field C] (D : operatorField .differential (RatFunc C)),
    isRationalDerivative D →
    ∀ {p q : Polynomial C}, p ≠ 0 → q ≠ 0 →
      let i := algebraMap (Polynomial C) (RatFunc C)
      let b := i p / i q
      let numerator := p.derivative * q - p * q.derivative
      apply D b / b = i numerator / i (p * q) ∧
      numerator.degree < (p * q).degree

def rationalDerivativeNoPowerSolution : Prop :=
  ∀ {C : Type u} [Field C] [CharZero C]
    (D : operatorField .differential (RatFunc C)), isRationalDerivative D →
    ∀ {m : ℕ}, 0 < m → ∀ b : (RatFunc C)ˣ,
      apply D (b : RatFunc C) ≠ (m : RatFunc C) * (b : RatFunc C)

/-- The one-by-one coefficient matrix for `d(y) = y`. -/
noncomputable def exponentialSystem (C : Type u) [Field C] : linearSystem .differential (RatFunc C) 1 :=
  differentialSystem (1 : Matrix (Fin 1) (Fin 1) (RatFunc C))

/-- In every Picard–Vessiot realization, the scalar multipliers exhaust the
unit group of the constant field, identified with `C` by the coefficient map. -/
def rationalDifferentialFullGroup : Prop :=
  ∀ {C : Type u} [Field C] [CharZero C] [IsAlgClosed C]
    (D : operatorField .differential (RatFunc C)), isRationalDerivative D →
    ∀ {R : Type v} [CommRing R] [Algebra (RatFunc C) R]
      (E : operator .differential R) (T : operator .differential (totalQuotientRing R))
      (Y : GL (Fin 1) R),
      isPicardVessiotTotalExtension D (exponentialSystem C) E T →
      isFundamental (exponentialSystem C) E Y →
      (matrixGaloisGroup D E Y).map Matrix.GeneralLinearGroup.det = ⊤

def rationalDifferentialFullGroupExists : Prop :=
  ∀ {C : Type u} [Field C] [CharZero C] [IsAlgClosed C]
    (D : operatorField .differential (RatFunc C)), isRationalDerivative D →
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra (RatFunc C) R),
    ∃ (E : operator .differential R) (T : operator .differential (totalQuotientRing R))
      (Y : GL (Fin 1) R),
      isPicardVessiotTotalExtension D (exponentialSystem C) E T ∧
      isFundamental (exponentialSystem C) E Y ∧
      (matrixGaloisGroup D E Y).map Matrix.GeneralLinearGroup.det = ⊤

end GaloisFormalization.PV.Specs
