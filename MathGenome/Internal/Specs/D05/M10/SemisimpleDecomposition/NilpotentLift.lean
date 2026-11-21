import MathGenome.Internal.Specs.D05.M10.SemisimpleDecomposition.Units
import MathGenome.Internal.Specs.D05.Foundations.QuotientBasisUnits
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! The finite Newton lift of paper.tex:1594–1600. Characteristic zero is
sufficient, so the statements cover every named subfield of ℂ. No operator or
semisimple decomposition is an input. The quotient is the actual polynomial
quotient `AdjoinRoot`, and all powers of ideals are ordinary ideal powers.
The finite index `Fin n` records the distinct irreducible factors. -/

noncomputable section
namespace D05.Specs.M10.SemisimpleDecomposition.NilpotentLift
open Polynomial

abbrev squarefreePart {K : Type*} [Field K] {n : ℕ}
    (p : Fin n → K[X]) : K[X] := ∏ i, p i
abbrev modulus {K : Type*} [Field K] {n : ℕ}
    (p : Fin n → K[X]) (a : Fin n → ℕ) : K[X] := ∏ i, p i ^ a i
abbrev maxExponent {n : ℕ} (a : Fin n → ℕ) : ℕ := Finset.univ.sup a
abbrev radicalIdeal {K : Type*} [Field K] {n : ℕ}
    (p : Fin n → K[X]) (a : Fin n → ℕ) : Ideal (AdjoinRoot (modulus p a)) :=
  Ideal.span {AdjoinRoot.mk (modulus p a) (squarefreePart p)}

/-- Total ring inverse is used only at elements proved to be units. -/
def newtonStep {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X]) (y : A) : A :=
  y - aeval y f * Ring.inverse (aeval y f.derivative)
def newtonIter {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X]) (x : A) : ℕ → A
  | 0 => x
  | k + 1 => newtonStep f (newtonIter f x k)

def factorizationProperties : Prop :=
  ∀ (K : Type*) [Field K] [CharZero K] (n : ℕ), 0 < n →
    ∀ (p : Fin n → K[X]) (a : Fin n → ℕ),
      (∀ i, (p i).Monic) → (∀ i, Irreducible (p i)) →
      Function.Injective p → (∀ i, 1 ≤ a i) →
      (modulus p a).Monic ∧ 0 < (modulus p a).natDegree ∧
      (squarefreePart p).Monic ∧ IsCoprime (squarefreePart p) (squarefreePart p).derivative ∧
      squarefreePart p ∣ modulus p a ∧
      modulus p a ∣ squarefreePart p ^ maxExponent a ∧ 0 < maxExponent a

def idealNilpotent : Prop :=
  ∀ (K : Type*) [Field K] (n : ℕ) (p : Fin n → K[X]) (a : Fin n → ℕ),
    radicalIdeal p a ^ maxExponent a = ⊥

def derivativeUnit : Prop :=
  ∀ (K : Type*) [Field K] [CharZero K] (n : ℕ)
    (p : Fin n → K[X]) (a : Fin n → ℕ),
    (∀ i, (p i).Monic) → (∀ i, Irreducible (p i)) → Function.Injective p →
    ∀ y : AdjoinRoot (modulus p a),
      y - AdjoinRoot.root (modulus p a) ∈ radicalIdeal p a →
      IsUnit (aeval y (squarefreePart p).derivative)

/-- The exponent doubles at each step, for every positive s, without
characteristic or finite dimensionality restrictions on the algebra. -/
def newtonImproves : Prop :=
  ∀ (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (f : K[X]) (J : Ideal A) (y : A) (s : ℕ), 1 ≤ s →
    IsUnit (aeval y f.derivative) → aeval y f ∈ J ^ s →
    newtonStep f y - y ∈ J ^ s ∧ aeval (newtonStep f y) f ∈ J ^ (2 * s)

/-- All iterates, their error bounds, an explicitly bounded stopping time,
a polynomial representative, and the nilpotent difference. Choosing k=r
is a finite bound; faster stopping is expressed by the 2^j error estimates. -/
def finiteLift : Prop :=
  ∀ (K : Type*) [Field K] [CharZero K] (n : ℕ), 0 < n →
    ∀ (p : Fin n → K[X]) (a : Fin n → ℕ),
    (∀ i, (p i).Monic) → (∀ i, Irreducible (p i)) →
    Function.Injective p → (∀ i, 1 ≤ a i) →
    let m := modulus p a
    let f := squarefreePart p
    let r := maxExponent a
    let J := radicalIdeal p a
    let x := AdjoinRoot.root m
    (∀ j, newtonIter f x j - x ∈ J ∧
      IsUnit (aeval (newtonIter f x j) f.derivative) ∧
      aeval (newtonIter f x j) f ∈ J ^ (2 ^ j)) ∧
    ∃ (k : ℕ) (y : AdjoinRoot m) (g : K[X]),
      k ≤ r ∧ r ≤ 2 ^ k ∧ y = newtonIter f x k ∧
      y - x ∈ J ∧ aeval y f = 0 ∧ AdjoinRoot.mk m g = y ∧ (x - y) ^ r = 0

end D05.Specs.M10.SemisimpleDecomposition.NilpotentLift
