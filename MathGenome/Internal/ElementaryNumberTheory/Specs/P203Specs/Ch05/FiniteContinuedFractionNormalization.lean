import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.ContinuedFractionAlgorithm
import Mathlib.NumberTheory.Real.Irrational

/-! The full finite expansion and normalization theorem, paper.tex §nt:E02.
A nonempty list is represented by its integer head and integer tail. -/
namespace P203Specs

/-- The source's digit convention, without the normalization at the final digit. -/
def Admissible (_a : ℤ) (t : List ℤ) : Prop := ∀ b ∈ t, 1 ≤ b

/-- A tail beginning at a positive index, with last digit at least two. -/
def CanonicalTail : ℤ → List ℤ → Prop
  | a, [] => 2 ≤ a
  | a, b :: t => 1 ≤ a ∧ CanonicalTail b t

/-- The initial digit is unrestricted, including in a one-digit expansion. -/
def Canonical (_a : ℤ) (t : List ℤ) : Prop :=
  match t with
  | [] => True
  | b :: s => CanonicalTail b s

/-- Exactly these digits are produced, and there is no digit after the list. -/
def AlgorithmExpansion (x : ℝ) (a : ℤ) (t : List ℤ) : Prop :=
  (∀ j : ℕ, partialQuotient x j = (a :: t)[j]?) ∧
    completeQuotient x (t.length + 1) = none

/-- Termination includes a defined final quotient and the stopping condition. -/
def AlgorithmTerminates (x : ℝ) : Prop :=
  ∃ (n : ℕ) (α : ℝ), completeQuotient x n = some α ∧
    α = (⌊α⌋ : ℝ) ∧ completeQuotient x (n + 1) = none

/-- Split the final digit into `last - 1, 1`, including the integer case. -/
def alternativeExpansion : ℤ → List ℤ → List ℤ
  | a, [] => [a - 1, 1]
  | a, b :: t => a :: alternativeExpansion b t

/-- Value of a list, used below only for the nonempty alternative list. -/
noncomputable def expansionValue : List ℤ → ℝ
  | [] => 0
  | a :: t => finiteContinuedFraction a t

def TerminationIffRational : Prop :=
  ∀ x : ℝ, AlgorithmTerminates x ↔ ∃ q : ℚ, (q : ℝ) = x

def IrrationalNontermination : Prop :=
  ∀ x : ℝ, Irrational x → ¬ AlgorithmTerminates x

def RationalCanonicalExistence : Prop :=
  ∀ q : ℚ, ∃ (a : ℤ) (t : List ℤ), Canonical a t ∧
    finiteContinuedFraction a t = (q : ℝ) ∧ AlgorithmExpansion (q : ℝ) a t

def CanonicalUniqueness : Prop :=
  ∀ (a b : ℤ) (s t : List ℤ), Canonical a s → Canonical b t →
    finiteContinuedFraction a s = finiteContinuedFraction b t → a = b ∧ s = t

def CanonicalAlgorithmIdentification : Prop :=
  ∀ (a : ℤ) (t : List ℤ), Canonical a t →
    AlgorithmExpansion (finiteContinuedFraction a t) a t

def FinalDigitSplitting : Prop :=
  (∀ (a b : ℤ) (t : List ℤ), Canonical a (t ++ [b]) →
    finiteContinuedFraction a (t ++ [b]) =
      finiteContinuedFraction a (t ++ [b - 1, 1])) ∧
  (∀ a : ℤ, finiteContinuedFraction a [] = finiteContinuedFraction (a - 1) [1])

/-- Every admissible expansion of a rational is either its unique canonical
list or that list with its last digit split (the integer case is included). -/
def AllFiniteExpansions : Prop :=
  ∀ (a : ℤ) (t : List ℤ), Admissible a t →
    ∃ (b : ℤ) (s : List ℤ), Canonical b s ∧
      finiteContinuedFraction a t = finiteContinuedFraction b s ∧
      ((a = b ∧ t = s) ∨ a :: t = alternativeExpansion b s)

/-- Explicitly record the final-1 and merging characterization. -/
def NoncanonicalMerging : Prop :=
  ∀ (a : ℤ) (t : List ℤ), Admissible a t → ¬ Canonical a t →
    (t = [1] ∧ Canonical (a + 1) [] ∧
      finiteContinuedFraction a t = finiteContinuedFraction (a + 1) []) ∨
    ∃ (s : List ℤ) (b : ℤ), t = s ++ [b, 1] ∧
      Canonical a (s ++ [b + 1]) ∧
      finiteContinuedFraction a t = finiteContinuedFraction a (s ++ [b + 1])

/-- Both lists really are admissible expansions, and they are distinct. -/
def AlternativeExpansionProperties : Prop :=
  ∀ (a : ℤ) (t : List ℤ), Canonical a t →
    ∃ (b : ℤ) (s : List ℤ), alternativeExpansion a t = b :: s ∧
      Admissible b s ∧ expansionValue (alternativeExpansion a t) =
        finiteContinuedFraction a t ∧ alternativeExpansion a t ≠ a :: t

/-- Combined existence, uniqueness, algorithm agreement, and exact classification
of all admissible finite expansions of each rational. -/
def FiniteNormalization : Prop :=
  ∀ q : ℚ, ∃ (a : ℤ) (t : List ℤ), Canonical a t ∧ Admissible a t ∧
    finiteContinuedFraction a t = (q : ℝ) ∧ AlgorithmExpansion (q : ℝ) a t ∧
    (∀ (b : ℤ) (s : List ℤ), Canonical b s →
      finiteContinuedFraction b s = (q : ℝ) → b = a ∧ s = t) ∧
    (∀ (b : ℤ) (s : List ℤ), Admissible b s →
      (finiteContinuedFraction b s = (q : ℝ) ↔
        b :: s = a :: t ∨ b :: s = alternativeExpansion a t))

end P203Specs
