import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.Specs.D07.Foundations.IntegerArithmetic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
Independent statements for K07.11.rational_root, paper.tex:2479–2499.

The polynomial is the upstream formal polynomial over ℤ. Its degree is
`natDegree` only after excluding zero. Thus `leadingCoeff` is exactly the
source's nonzero a_n, and `coeff 0` is a_0. Evaluation uses the canonical
unital map ℤ → ℚ. The integers r,s are arbitrary signed integers, not the
normalized numerator and positive denominator of a rational number.
-/

namespace Specs.D07.Ch11.RationalRoot

open Polynomial

/-- Both divisibilities for every reduced presentation r/s, including r=0. -/
def RationalRootDivisibility : Prop :=
  ∀ (f : Polynomial ℤ), f ≠ 0 → ∀ (r s : ℤ),
    Int.gcd r s = 1 → s ≠ 0 →
    f.eval₂ (Int.castRingHom ℚ) ((r : ℚ) / (s : ℚ)) = 0 →
    r ∣ f.coeff 0 ∧ s ∣ f.leadingCoeff

/-- A nonzero constant polynomial has no rational root. -/
def NoRootDegreeZero : Prop :=
  ∀ (f : Polynomial ℤ), f ≠ 0 → f.natDegree = 0 →
    ∀ q : ℚ, f.eval₂ (Int.castRingHom ℚ) q ≠ 0

/-- A reduced presentation of the zero root has denominator ±1, and its
constant coefficient vanishes. In particular the numerator 0 divides a_0. -/
def ZeroRootReduced : Prop :=
  ∀ (f : Polynomial ℤ), f ≠ 0 → ∀ s : ℤ,
    Int.gcd 0 s = 1 → s ≠ 0 →
    f.eval₂ (Int.castRingHom ℚ) ((0 : ℚ) / (s : ℚ)) = 0 →
    (s = 1 ∨ s = -1) ∧ f.coeff 0 = 0 ∧
      (0 : ℤ) ∣ f.coeff 0 ∧ s ∣ f.leadingCoeff

/-- Monicity forces every reduced denominator to divide 1. -/
def MonicDenominator : Prop :=
  ∀ (f : Polynomial ℤ), f.Monic → ∀ (r s : ℤ),
    Int.gcd r s = 1 → s ≠ 0 →
    f.eval₂ (Int.castRingHom ℚ) ((r : ℚ) / (s : ℚ)) = 0 →
    s ∣ (1 : ℤ) ∧ (s = 1 ∨ s = -1)

/-- Every rational root of a monic integer polynomial is an integer. -/
def MonicRationalRoot : Prop :=
  ∀ (f : Polynomial ℤ), f.Monic → ∀ q : ℚ,
    f.eval₂ (Int.castRingHom ℚ) q = 0 → ∃ z : ℤ, q = (z : ℚ)

end Specs.D07.Ch11.RationalRoot
