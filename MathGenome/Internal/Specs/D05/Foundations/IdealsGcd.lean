import MathGenome.Internal.Specs.D05.Foundations.Division
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Independent statements for paper.tex:368. The polynomials are formal
coefficient polynomials. A run records actual successive Euclidean remainders,
its final value, and its finite number of divisions; it contains no assumed gcd
or Bézout certificate. -/

noncomputable section

namespace D05.Foundations

/-- Monic normalization of the ordinary Euclidean gcd; zero stays zero. -/
def monicGcd {K : Type*} [Field K] (a b : Polynomial K) : Polynomial K := by
  classical
  exact normalize (EuclideanDomain.gcd a b)

/-- Zero has size zero; every nonzero polynomial has positive size. -/
def remainderSize {K : Type*} [Field K] (p : Polynomial K) : ℕ := by
  classical
  exact if p = 0 then 0 else p.natDegree + 1

/-- Operational semantics of repeated division, stopping exactly when the
second polynomial is zero. The output is the preceding polynomial. -/
inductive EuclideanRun {K : Type*} [Field K] :
    Polynomial K → Polynomial K → Polynomial K → ℕ → Prop
  | stop (a) : EuclideanRun a 0 a 0
  | divide (a b d) (n) (hb : b ≠ 0) (tail : EuclideanRun b (a % b) d n) :
      EuclideanRun a b d (n + 1)

end D05.Foundations

namespace D05.Specs.IdealsGcd

open D05.Foundations

/-- Uniqueness is among all monic generators. Least degree is compared only
against nonzero members of the ideal, as in the manuscript. -/
def idealMonicGenerator : Prop :=
  ∀ (K : Type*) [Field K] (I : Ideal (Polynomial K)), I ≠ ⊥ →
    ∃! d : Polynomial K, d.Monic ∧ d ∈ I ∧ Ideal.span {d} = I ∧
      ∀ f ∈ I, f ≠ 0 → d.natDegree ≤ f.natDegree

/-- Divisibility, the generated ideal, Bézout, and monicity for every nonzero
pair, without a positive-degree assumption. -/
def gcdProperties : Prop :=
  ∀ (K : Type*) [Field K] (a b : Polynomial K), a ≠ 0 ∨ b ≠ 0 →
    (monicGcd a b).Monic ∧
    Ideal.span {monicGcd a b} = Ideal.span {a, b} ∧
    monicGcd a b ∣ a ∧ monicGcd a b ∣ b ∧
    (∀ c : Polynomial K, c ∣ a → c ∣ b → c ∣ monicGcd a b) ∧
    ∃ u v : Polynomial K, monicGcd a b = u * a + v * b

/-- The common-divisor characterization uniquely determines the monic gcd. -/
def gcdUnique : Prop :=
  ∀ (K : Type*) [Field K] (a b d : Polynomial K), d.Monic →
    d ∣ a → d ∣ b →
    (∀ c : Polynomial K, c ∣ a → c ∣ b → c ∣ d) → d = monicGcd a b

/-- The exceptional pair has gcd zero and generates the zero ideal. -/
def zeroGcd : Prop :=
  ∀ (K : Type*) [Field K],
    monicGcd (0 : Polynomial K) 0 = 0 ∧
    Ideal.span ({(0 : Polynomial K), 0} : Set (Polynomial K)) = ⊥ ∧
    ¬ (monicGcd (0 : Polynomial K) 0).Monic

/-- A division step strictly decreases a natural measure, preserves the ideal,
and expresses the new remainder in terms of the preceding pair. -/
def euclideanStep : Prop :=
  ∀ (K : Type*) [Field K] (a b : Polynomial K), b ≠ 0 →
    remainderSize (a % b) < remainderSize b ∧
    (a % b = 0 ∨ (a % b).natDegree < b.natDegree) ∧
    a % b = a - (a / b) * b ∧
    Ideal.span {b, a % b} = Ideal.span {a, b}

/-- Every execution terminates after at most size(b) divisions. -/
def euclideanTermination : Prop :=
  ∀ (K : Type*) [Field K] (a b : Polynomial K),
    ∃ d n, EuclideanRun a b d n ∧ n ≤ remainderSize b

/-- Back substitution for every completed run. The last value generates the
initial ideal and has a Bézout expression; for a nonzero input pair it is
nonzero, and normalization by its inverse leading coefficient gives the monic
gcd. This includes executions with an initially zero second input. -/
def euclideanRunCorrect : Prop :=
  ∀ (K : Type*) [Field K] (a b d : Polynomial K) (n : ℕ),
    EuclideanRun a b d n →
    Ideal.span {d} = Ideal.span {a, b} ∧
    (∃ u v : Polynomial K, d = u * a + v * b) ∧
    ((d = 0) ↔ a = 0 ∧ b = 0) ∧
    (a ≠ 0 ∨ b ≠ 0 →
      d ≠ 0 ∧ (d * Polynomial.C d.leadingCoeff⁻¹).Monic ∧
      d * Polynomial.C d.leadingCoeff⁻¹ = monicGcd a b)

end D05.Specs.IdealsGcd
