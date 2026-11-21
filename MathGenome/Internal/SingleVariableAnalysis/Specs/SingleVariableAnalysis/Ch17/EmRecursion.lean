import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Higher
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval

/-! The integral recursion in K03.17.euler_maclaurin, paper.tex:4432–4471.
All integral predicates and values are the proper Darboux objects. Derivatives
are continuous closed-interval extensions, with real increments for both scalar
choices. No ambient two-sided endpoint derivatives are required.
These generic expressions are specialized below to exactly ℝ and ℂ. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.EmRecursion
open Set
open scoped BigOperators
open Ch08.Integral Ch17.Bernoulli Ch04.Higher

/-- Normalized Bernoulli polynomial; index one has value x−1/2. -/
def weight (j : ℕ) (x : ℝ) : ℝ :=
  (bernoulliPolynomialValue j).eval x / (j.factorial : ℝ)

/-- The periodic normalized integrand defining T_j. -/
def integrand {E : Type*} [AddCommGroup E] [Module ℝ E]
    (j : ℕ) (D : ℕ → ℝ → E) (x : ℝ) : E :=
  weight j (Int.fract x) • D j x

/-- Endpoint halves and the sum over strictly interior integer nodes. -/
def trapezoid {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℝ → E) (a b : ℤ) : E :=
  (1 / 2 : ℝ) • f a + (∑ k ∈ Finset.Ioo a b, f k) + (1 / 2 : ℝ) • f b

/-- Full recursion, with existence of f's integral and all T_j integrals.
The family hypothesis represents the source C^(2m) regularity and endpoint
values; it does not assume any integral identity. -/
def normalizedRecursion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : (ℝ → E) → ℝ → ℝ → Prop)
    (J : (f : ℝ → E) → {a b : ℝ} → I f a b → E) : Prop :=
  ∀ (a b : ℤ), a < b → ∀ (m : ℕ) (hm : 1 ≤ m),
    ∀ (f : ℝ → E) (D : ℕ → ℝ → E),
    closedDerivativeFamilyValue (2 * m) f a b D →
    ∃ hf : I f a b,
    ∃ hT : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * m → I (integrand j D) a b,
      (trapezoid f a b - J f hf = J (integrand 1 D) (hT 1 (by omega) (by omega))) ∧
      ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j < 2 * m),
        J (integrand j D) (hT j hj hjm.le) =
          (bernoulliNumberValue (j + 1) / ((j + 1).factorial : ℝ)) •
            (D j b - D j a) -
          J (integrand (j + 1) D) (hT (j + 1) (by omega) (by omega))

/-- The unnormalized integrand appearing inside the paper's integral. -/
def rawIntegrand {E : Type*} [AddCommGroup E] [Module ℝ E]
    (j : ℕ) (D : ℕ → ℝ → E) (x : ℝ) : E :=
  (bernoulliPolynomialValue j).eval (Int.fract x) • D j x

/-- T_j is the proper integral divided by j!, with the division outside. -/
def term {E : Type*} [AddCommGroup E] [Module ℝ E]
    {I : (ℝ → E) → ℝ → ℝ → Prop}
    (J : (f : ℝ → E) → {a b : ℝ} → I f a b → E)
    (j : ℕ) (D : ℕ → ℝ → E) {a b : ℝ} (h : I (rawIntegrand j D) a b) : E :=
  (1 / (j.factorial : ℝ)) • J (rawIntegrand j D) h

/-- Source form of the complete integral recursion, with proper integrability
of the unnormalized integrands explicitly asserted. -/
def recursion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : (ℝ → E) → ℝ → ℝ → Prop)
    (J : (f : ℝ → E) → {a b : ℝ} → I f a b → E) : Prop :=
  ∀ (a b : ℤ), a < b → ∀ (m : ℕ) (hm : 1 ≤ m),
    ∀ (f : ℝ → E) (D : ℕ → ℝ → E),
    closedDerivativeFamilyValue (2 * m) f a b D →
    ∃ hf : I f a b,
    ∃ hB : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * m → I (rawIntegrand j D) a b,
      (trapezoid f a b - J f hf = term J 1 D (hB 1 (by omega) (by omega))) ∧
      ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j < 2 * m),
        term J j D (hB j hj hjm.le) =
          (bernoulliNumberValue (j + 1) / ((j + 1).factorial : ℝ)) •
            (D j b - D j a) -
          term J (j + 1) D (hB (j + 1) (by omega) (by omega))

/-- The first cell identity retains the exceptional, discontinuous B₁ values
at integer nodes. Those values have no effect on the proper integral. -/
def unitCell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : (ℝ → E) → ℝ → ℝ → Prop)
    (J : (f : ℝ → E) → {a b : ℝ} → I f a b → E) : Prop :=
  ∀ (k : ℤ) (f df : ℝ → E),
    ContinuousOn f (Icc (k : ℝ) ((k : ℝ) + 1)) →
    ContinuousOn df (Icc (k : ℝ) ((k : ℝ) + 1)) →
    (∀ x ∈ Ioo (k : ℝ) ((k : ℝ) + 1), HasDerivAt f (df x) x) →
    ∃ hf : I f k ((k : ℝ) + 1),
    ∃ hT : I (fun x => weight 1 (Int.fract x) • df x) k ((k : ℝ) + 1),
      (1 / 2 : ℝ) • (f k + f ((k : ℝ) + 1)) - J f hf =
        J (fun x => weight 1 (Int.fract x) • df x) hT

/-- Arbitrary finite assignments at any of the integer nodes preserve both
proper integrability and value, including the two outer endpoints. -/
def nodeChanges {E : Type*} [NormedAddCommGroup E]
    (I : (ℝ → E) → ℝ → ℝ → Prop)
    (J : (f : ℝ → E) → {a b : ℝ} → I f a b → E) : Prop :=
  ∀ (a b : ℤ), a < b → ∀ f g : ℝ → E,
    (∀ x ∈ Icc (a : ℝ) (b : ℝ),
      (∀ k : ℤ, k ∈ Finset.Icc a b → x ≠ (k : ℝ)) → f x = g x) →
    ∀ hf : I f a b, ∃ hg : I g a b, J g hg = J f hf

def realRecursion : Prop := recursion realIntegrableValue (@realIntegralValue)
def complexRecursion : Prop := recursion complexIntegrableValue (@complexIntegralValue)
def realUnitCell : Prop := unitCell realIntegrableValue (@realIntegralValue)
def complexUnitCell : Prop := unitCell complexIntegrableValue (@complexIntegralValue)
def realNodeChanges : Prop := nodeChanges realIntegrableValue (@realIntegralValue)
def complexNodeChanges : Prop := nodeChanges complexIntegrableValue (@complexIntegralValue)

end Specs.SingleVariableAnalysis.Ch17.EmRecursion
