import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BisectionInvariants
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

/-! Independent statements for paper.tex, p206:W64 and the stored-output paragraph.
All arithmetic is exact real arithmetic. The natural ceiling clamps negative
integer ceilings to zero. Run indices count completed exact half updates only. -/
namespace Specs.NumAnalysis206.Iterations.BisectionCertificates
open Specs.NumAnalysis206.Iterations.BisectionInvariants

noncomputable def updateCount (a b ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ((b-a)/(2*ε))⌉₊

def countFormula : Prop :=
  ∀ a b ε : ℝ, (updateCount a b ε : ℤ) =
    max 0 ⌈Real.logb 2 ((b-a)/(2*ε))⌉

/-- (1/2)^(n+1) is the source's 2^(-n-1). -/
def exactThreshold : Prop :=
  ∀ (a b ε : ℝ), a < b → 0 < ε → ∀ n : ℕ,
    (1/2 : ℝ)^(n+1) * (b-a) ≤ ε ↔ updateCount a b ε ≤ n

def initialThreshold : Prop :=
  ∀ (a b ε : ℝ), a < b → 0 < ε →
    (updateCount a b ε = 0 ↔ (b-a)/2 ≤ ε)

/-- No hypothesis about evaluating the midpoint at index n is needed. -/
def midpointCertificate : Prop :=
  ∀ (f : ℝ → ℝ) (a b ε : ℝ) (K : ℕ), a < b → 0 < ε →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    ∀ (r : FiniteRun f a b K) (n : ℕ), n ≤ K → updateCount a b ε ≤ n →
      ∃ p ∈ Set.Icc (r.left n) (r.right n), f p = 0 ∧
        |midpoint (r.left n) (r.right n) - p| ≤ ε

/-- Exact real arithmetic can complete the budget of halvings, including when
an encountered zero is kept as an endpoint instead of returned early. -/
def budgetAttainable : Prop :=
  ∀ (f : ℝ → ℝ) (a b ε : ℝ), a < b → 0 < ε →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    ∃ r : FiniteRun f a b (updateCount a b ε),
      ∃ p ∈ Set.Icc (r.left (updateCount a b ε)) (r.right (updateCount a b ε)),
        f p = 0 ∧
        |midpoint (r.left (updateCount a b ε)) (r.right (updateCount a b ε)) - p| ≤ ε

/-- An exact run reaching the budget has a certificate there. A run stopped
before the budget is successful provided it returned a known root. The premise
about early stopping deliberately makes no progress promise for uncertain signs
or a number format unable to represent another midpoint. -/
def stoppingGuarantee : Prop :=
  ∀ (f : ℝ → ℝ) (a b ε : ℝ) (K : ℕ), a < b → 0 < ε →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    ∀ r : FiniteRun f a b K,
    (K < updateCount a b ε →
      ∃ p, SuccessfulReturn f (r.left K) (r.right K) p) →
    (K < updateCount a b ε ∧ ∃ p ∈ Set.Icc a b,
      SuccessfulReturn f (r.left K) (r.right K) p ∧ f p = 0) ∨
    (updateCount a b ε ≤ K ∧
      ∃ p ∈ Set.Icc (r.left (updateCount a b ε)) (r.right (updateCount a b ε)),
        f p = 0 ∧
        |midpoint (r.left (updateCount a b ε)) (r.right (updateCount a b ε)) - p| ≤ ε)

def enclosureCertificates : Prop :=
  ∀ (f : ℝ → ℝ) (x l u : ℝ), l ≤ f x → f x ≤ u →
    (0 < l → 0 < f x) ∧ (u < 0 → f x < 0) ∧
    (l = 0 → u = 0 → f x = 0)

/-- Necessary and sufficient conditions for a strict sign, or a zero, to follow
from enclosure membership alone. Nonempty enclosures are required. -/
def universalCertificates : Prop :=
  ∀ (l u : ℝ), l ≤ u →
    ((∀ y ∈ Set.Icc l u, 0 < y) ↔ 0 < l) ∧
    ((∀ y ∈ Set.Icc l u, y < 0) ↔ u < 0) ∧
    ((∀ y ∈ Set.Icc l u, y = 0) ↔ l = 0 ∧ u = 0)

def ambiguousEnclosure : Prop :=
  ∀ (l u : ℝ), l ≤ 0 → 0 ≤ u → ¬(l = 0 ∧ u = 0) →
    0 ∈ Set.Icc l u ∧ (∃ y ∈ Set.Icc l u, y ≠ 0) ∧
    ¬(∀ y ∈ Set.Icc l u, 0 < y) ∧
    ¬(∀ y ∈ Set.Icc l u, y < 0) ∧
    ¬(∀ y ∈ Set.Icc l u, y = 0)

/-- A certified sign at x permits the half adjacent to an opposite-sign endpoint.
The four implications cover both orientations of the original sign bracket. -/
def strictSignUpdates : Prop :=
  ∀ (f : ℝ → ℝ) (a b x l u : ℝ), l ≤ f x → f x ≤ u →
    (f a < 0 → 0 < l → f a * f x < 0) ∧
    (0 < f a → u < 0 → f a * f x < 0) ∧
    (0 < l → f b < 0 → f x * f b < 0) ∧
    (u < 0 → 0 < f b → f x * f b < 0)

def storedDistance : Prop :=
  ∀ (a b z p : ℝ), z ∈ Set.Icc a b → p ∈ Set.Icc a b →
    |z-p| ≤ max (z-a) (b-z)

/-- The existing bracket certifies any stored point inside it, independently of
whether another sign evaluation or another representable midpoint is available. -/
def storedRootCertificate : Prop :=
  ∀ (f : ℝ → ℝ) (a b z R : ℝ), a < b →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    z ∈ Set.Icc a b → max (z-a) (b-z) ≤ R →
    ∃ p ∈ Set.Icc a b, f p = 0 ∧ |z-p| ≤ R

def rootRadius : Prop :=
  ∀ (f : ℝ → ℝ) (a b z p R : ℝ), z ∈ Set.Icc a b → p ∈ Set.Icc a b →
    f p = 0 → max (z-a) (b-z) ≤ R → f p = 0 ∧ |z-p| ≤ R

def unavailableMidpoint : Prop :=
  ∀ (F : Set ℝ) (a b : ℝ), a < b →
    (∀ x ∈ F, x ∉ Set.Ioo a b) → midpoint a b ∉ F

end Specs.NumAnalysis206.Iterations.BisectionCertificates
