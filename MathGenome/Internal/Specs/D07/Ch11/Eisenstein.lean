import MathGenome.Internal.Specs.D07.Ch11.GaussFractionIrreducible
import Mathlib.RingTheory.Ideal.Operations

/-!
Independent statements for K07.11.eisenstein, paper.tex:2684–2726.
The coefficient ring is a commutative nontrivial domain. Ideals and their
squares are ordinary ideals, not symbolic powers. Positive natural degree
excludes both zero and constant polynomials. The integer prime in the final
example is a positive prime, as in the preceding integer specialization.
-/

universe u v

namespace Specs.D07.Ch11.Eisenstein

open Polynomial

def MonicCriterion : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (P : Ideal R) (f : R[X]),
    P.IsPrime → f.Monic → 0 < f.natDegree →
    (∀ i : ℕ, i < f.natDegree → f.coeff i ∈ P) →
    f.coeff 0 ∉ P ^ 2 → Irreducible f

/-- This includes nonmonic primitive polynomials; monicity is not required. -/
def PrimitiveCriterion : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (P : Ideal R) (f : R[X]), P.IsPrime → f.IsPrimitive →
    0 < f.natDegree → f.leadingCoeff ∉ P →
    (∀ i : ℕ, i < f.natDegree → f.coeff i ∈ P) →
    f.coeff 0 ∉ P ^ 2 → Irreducible f

def MonicFractionCriterion : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (f : R[X]), P.IsPrime → f.Monic → 0 < f.natDegree →
    (∀ i : ℕ, i < f.natDegree → f.coeff i ∈ P) →
    f.coeff 0 ∉ P ^ 2 →
      Irreducible f ∧ Irreducible (f.map (algebraMap R K))

def PrimitiveFractionCriterion : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (f : R[X]), P.IsPrime → f.IsPrimitive →
    0 < f.natDegree → f.leadingCoeff ∉ P →
    (∀ i : ℕ, i < f.natDegree → f.coeff i ∈ P) →
    f.coeff 0 ∉ P ^ 2 →
      Irreducible f ∧ Irreducible (f.map (algebraMap R K))

/-- Identifies the ideal hypotheses with the stated integer divisibilities. -/
def IntegerIdealConditions : Prop :=
  ∀ (p : ℕ) (f : ℤ[X]),
    let P : Ideal ℤ := Ideal.span {(p : ℤ)}
    (f.leadingCoeff ∉ P ∧
      (∀ i : ℕ, i < f.natDegree → f.coeff i ∈ P) ∧ f.coeff 0 ∉ P ^ 2) ↔
    (¬(p : ℤ) ∣ f.leadingCoeff ∧
      (∀ i : ℕ, i < f.natDegree → (p : ℤ) ∣ f.coeff i) ∧
      ¬(p : ℤ) ^ 2 ∣ f.coeff 0)

/-- Primitivity is required only for the nonmonic form. -/
def IntegerCriterion : Prop :=
  ∀ (p : ℕ) (f : ℤ[X]), p.Prime → (f.Monic ∨ f.IsPrimitive) →
    0 < f.natDegree → ¬(p : ℤ) ∣ f.leadingCoeff →
    (∀ i : ℕ, i < f.natDegree → (p : ℤ) ∣ f.coeff i) →
    ¬(p : ℤ) ^ 2 ∣ f.coeff 0 →
      Irreducible f ∧ Irreducible (f.map (algebraMap ℤ ℚ))

def XPowSubPrime : Prop :=
  ∀ (p n : ℕ), p.Prime → 1 ≤ n →
    Irreducible (X ^ n - C (p : ℤ)) ∧
      Irreducible (X ^ n - C (p : ℚ))

end Specs.D07.Ch11.Eisenstein
