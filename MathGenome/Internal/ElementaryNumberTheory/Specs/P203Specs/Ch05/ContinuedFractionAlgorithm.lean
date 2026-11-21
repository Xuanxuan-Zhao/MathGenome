import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
The algorithm and notation in paper.tex, §nt:E02, lines 2088–2102.
Indices include the initial quotient at zero. An absent entry remains absent;
no digit or complete quotient is assigned after termination.
-/
namespace P203Specs

/-- The standard Mathlib continued fraction, with head digit at index zero. -/
noncomputable def simpleContinuedFraction (x : ℝ) : GenContFract ℝ :=
  GenContFract.of x

/-- Recover the complete quotient from Mathlib's integer/fractional-part stream. -/
noncomputable def completeQuotient (x : ℝ) (j : ℕ) : Option ℝ :=
  (GenContFract.IntFractPair.stream x j).map (fun p => (p.b : ℝ) + p.fr)

/-- Integer digits at the same zero-based indices, only while defined. -/
noncomputable def partialQuotient (x : ℝ) (j : ℕ) : Option ℤ :=
  (GenContFract.IntFractPair.stream x j).map (fun p => p.b)

/-- Evaluation of the nonempty integer list with head `a₀` and tail `as`.
As usual in Lean, division is total; on the source's admissible digit lists
all denominators in this expression are nonzero. The empty list is not an input. -/
noncomputable def finiteContinuedFraction : ℤ → List ℤ → ℝ
  | a, [] => (a : ℝ)
  | a, b :: bs => (a : ℝ) + 1 / finiteContinuedFraction b bs

def SimpleContinuedFractionType := ℝ → GenContFract ℝ
def CompleteQuotientType := ℝ → ℕ → Option ℝ
def PartialQuotientType := ℝ → ℕ → Option ℤ
def FiniteContinuedFractionType := ℤ → List ℤ → ℝ

/-- The source's initial conditions, with no sign restriction on `x`. -/
def AlgorithmInitial : Prop :=
  ∀ x : ℝ, completeQuotient x 0 = some x ∧ partialQuotient x 0 = some ⌊x⌋

def AlgorithmDigits : Prop :=
  ∀ (x : ℝ) (j : ℕ), partialQuotient x j = (completeQuotient x j).map Int.floor

/-- This also propagates absence, rather than applying a reciprocal at a stopped state. -/
def AlgorithmStep : Prop :=
  ∀ (x : ℝ) (j : ℕ), completeQuotient x (j + 1) =
    (completeQuotient x j).bind (fun α =>
      if α = (⌊α⌋ : ℝ) then none else some (1 / (α - (⌊α⌋ : ℝ))))

def AlgorithmStopping : Prop :=
  ∀ (x α : ℝ) (j : ℕ), completeQuotient x j = some α →
    (completeQuotient x (j + 1) = none ↔ α = (⌊α⌋ : ℝ))

def AlgorithmNoRestart : Prop :=
  ∀ (x : ℝ) (j k : ℕ), completeQuotient x j = none →
    completeQuotient x (j + k) = none

def LaterCompleteQuotients : Prop :=
  ∀ (x α : ℝ) (j : ℕ), 1 ≤ j → completeQuotient x j = some α → 1 < α

def LaterPartialQuotients : Prop :=
  ∀ (x : ℝ) (a : ℤ) (j : ℕ), 1 ≤ j → partialQuotient x j = some a → 1 ≤ a

/-- Mathlib stores `a₀` in the head and the pair `(1,a_{j+1})` at tail index `j`.
The equality of options includes absence of every digit after termination. -/
def StandardContinuedFractionBridge : Prop :=
  ∀ x : ℝ, (simpleContinuedFraction x).h = (⌊x⌋ : ℝ) ∧
    ∀ j : ℕ, (simpleContinuedFraction x).s.get? j =
      (partialQuotient x (j + 1)).map (fun a : ℤ => (⟨1, (a : ℝ)⟩ : GenContFract.Pair ℝ))

def StandardTerminationBridge : Prop :=
  ∀ (x : ℝ) (j : ℕ), (simpleContinuedFraction x).TerminatedAt j ↔
    completeQuotient x (j + 1) = none

/-- An additional explicit bridge for the complete quotients themselves. -/
def CompleteQuotientStreamBridge : Prop :=
  ∀ (x α : ℝ) (j : ℕ), completeQuotient x j = some α ↔
    GenContFract.IntFractPair.stream x j = some (GenContFract.IntFractPair.of α)

def FiniteEvaluation : Prop :=
  (∀ a : ℤ, finiteContinuedFraction a [] = (a : ℝ)) ∧
  (∀ (a b : ℤ) (bs : List ℤ), finiteContinuedFraction a (b :: bs) =
    (a : ℝ) + 1 / finiteContinuedFraction b bs)

end P203Specs
