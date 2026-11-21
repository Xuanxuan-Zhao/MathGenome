import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.PartialFractionInterface
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.QuadraticPrimitives
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The analytic part of K03.09.partial_fractions, paper.tex:2676–2703.
Orders are natural numbers with an explicit positive-order hypothesis. Negative
integer powers are written as reciprocals of natural powers; thus all displayed
formulas use only rational functions, real logarithms, and the finite upstream
arctangent recurrence. `formulaOn` includes every pole-free interval and its
complete continuous primitive family, with a separate constant per interval.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch09.PartialFractions
open Polynomial
open scoped BigOperators
open ElementaryPrimitives

/-- Termwise polynomial integration, with no properness assumption. -/
def polynomialPrimitive (A : ℝ[X]) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (A.natDegree + 1), A.coeff j * (x ^ (j + 1) / ((j : ℝ) + 1))

/-- The order zero value merely totalizes this family. -/
def linearPrimitive (a r : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun x => a * Real.log |x - r|
  | n + 2 => fun x => -a / (((n : ℝ) + 1) * (x - r) ^ (n + 1))

/-- Primitive of the odd numerator By. -/
def oddQuadraticPrimitive (B d : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun y => (B / 2) * Real.log (y ^ 2 + d)
  | n + 2 => fun y => -B / (2 * ((n : ℝ) + 1) * (y ^ 2 + d) ^ (n + 1))

def centeredQuadraticPrimitive (B C d : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  oddQuadraticPrimitive B d k y + C * QuadraticPrimitives.quadraticPrimitiveValue d k y

/-- Completing the square also changes the constant numerator coefficient. -/
def shiftedQuadraticPrimitive (b c u v : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  centeredQuadraticPrimitive b (c - b * u / 2) (v - u ^ 2 / 4) k (x + u / 2)

/-- Finite output data of the real algebra interface, without assumed proofs. -/
structure RealData where
  n : ℕ
  p : Fin n → ℝ[X]
  e : Fin n → ℕ
  A : ℝ[X]
  a : (i : Fin n) → Fin (e i) → ℝ
  b : (i : Fin n) → Fin (e i) → ℝ
  c : (i : Fin n) → Fin (e i) → ℝ

def RealData.integrand (T : RealData) (x : ℝ) : ℝ :=
  T.A.eval x +
    (∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 1),
      ∑ k : Fin (T.e i), T.a i k / (x - (-(T.p i).coeff 0)) ^ (k.val + 1)) +
    (∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 2),
      ∑ k : Fin (T.e i), (T.b i k * x + T.c i k) /
        (x ^ 2 + (T.p i).coeff 1 * x + (T.p i).coeff 0) ^ (k.val + 1))

def RealData.primitive (T : RealData) (x : ℝ) : ℝ :=
  polynomialPrimitive T.A x +
    (∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 1),
      ∑ k : Fin (T.e i), linearPrimitive (T.a i k) (-(T.p i).coeff 0) (k.val + 1) x) +
    (∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 2),
      ∑ k : Fin (T.e i), shiftedQuadraticPrimitive (T.b i k) (T.c i k)
        ((T.p i).coeff 1) ((T.p i).coeff 0) (k.val + 1) x)

/-- The entire algebraic output is a conclusion of the main theorem. -/
def RealData.Valid (T : RealData) (P Q : ℝ[X]) : Prop :=
  (∀ i, (T.p i).Monic) ∧ (∀ i, Irreducible (T.p i)) ∧ Function.Injective T.p ∧
  (∀ i, 0 < T.e i) ∧ Q = C Q.leadingCoeff * ∏ i, T.p i ^ T.e i ∧
  (∀ i,
    ((T.p i).natDegree = 1 ∧ T.p i = X - C (-(T.p i).coeff 0)) ∨
    ((T.p i).natDegree = 2 ∧
      T.p i = X ^ 2 + C ((T.p i).coeff 1) * X + C ((T.p i).coeff 0) ∧
      (T.p i).coeff 1 ^ 2 - 4 * (T.p i).coeff 0 < 0)) ∧
  ∀ x : ℝ, Q.eval x ≠ 0 → P.eval x / Q.eval x = T.integrand x

def polynomialPrimitiveFormula : Prop :=
  ∀ A : ℝ[X], formulaOn (polynomialPrimitive A) A.eval Set.univ

def linearPrimitiveFormula : Prop :=
  ∀ (a r : ℝ) (k : ℕ), 1 ≤ k → formulaOn (linearPrimitive a r k)
    (fun x => a / (x - r) ^ k) {x | x ≠ r}

def centeredQuadraticPrimitiveFormula : Prop :=
  ∀ (B C d : ℝ) (k : ℕ), 0 < d → 1 ≤ k →
    formulaOn (centeredQuadraticPrimitive B C d k)
      (fun y => (B * y + C) / (y ^ 2 + d) ^ k) Set.univ

def completingSquare : Prop :=
  ∀ b c u v : ℝ, u ^ 2 - 4 * v < 0 →
    0 < v - u ^ 2 / 4 ∧ ∀ x : ℝ,
      x ^ 2 + u * x + v = (x + u / 2) ^ 2 + (v - u ^ 2 / 4) ∧
      b * x + c = b * (x + u / 2) + (c - b * u / 2)

def shiftedQuadraticPrimitiveFormula : Prop :=
  ∀ (b c u v : ℝ) (k : ℕ), u ^ 2 - 4 * v < 0 → 1 ≤ k →
    formulaOn (shiftedQuadraticPrimitive b c u v k)
      (fun x => (b * x + c) / (x ^ 2 + u * x + v) ^ k) Set.univ

def realRationalPrimitive : Prop :=
  ∀ P Q : ℝ[X], Q ≠ 0 → ∃ T : RealData, T.Valid P Q ∧
    formulaOn T.primitive (fun x => P.eval x / Q.eval x) {x | Q.eval x ≠ 0}

/-- Real and imaginary rational parts share a real denominator, whose nonzero
set is exactly the original one. Both primitives are explicit real finite
reductions; their complex combination uses no complex logarithm. -/
def complexRationalPrimitive : Prop :=
  ∀ P Q : ℂ[X], Q ≠ 0 →
    ∃ (R S D : ℝ[X]) (U V : RealData), D ≠ 0 ∧ U.Valid R D ∧ V.Valid S D ∧
      (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0 ↔ D.eval x ≠ 0) ∧
      (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0 →
        (P.eval (x : ℂ) / Q.eval (x : ℂ)).re = R.eval x / D.eval x ∧
        (P.eval (x : ℂ) / Q.eval (x : ℂ)).im = S.eval x / D.eval x) ∧
      formulaOn U.primitive (fun x => R.eval x / D.eval x) {x | D.eval x ≠ 0} ∧
      formulaOn V.primitive (fun x => S.eval x / D.eval x) {x | D.eval x ≠ 0} ∧
      complexFormulaOn (fun x => (U.primitive x : ℂ) + (V.primitive x : ℂ) * Complex.I)
        (fun x => P.eval (x : ℂ) / Q.eval (x : ℂ)) {x | Q.eval (x : ℂ) ≠ 0}

end Specs.SingleVariableAnalysis.Ch09.PartialFractions
