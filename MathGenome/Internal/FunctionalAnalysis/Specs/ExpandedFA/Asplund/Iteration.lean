import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates
import Mathlib.Analysis.Convex.Function

/-! Independent specification for the definitions in
`fa2:p1:asplund-convex-iteration`, paper.tex 6823–6848.

The primal functions are real-valued, expressing finiteness everywhere.
The infimum is a real conditional infimum; `IterationInfima` requires that
it be the actual greatest lower bound under the manuscript hypotheses.
Conjugates use the existing full-extended-real, continuous-real-dual interface.
No completeness or continuity of the initial functions is assumed.
The order/limit and conjugate recurrence theorems are separate goals. -/
namespace ExpandedFA.Asplund.Iteration.Spec

/-- Precisely the initial hypotheses, with finiteness encoded by `E → ℝ`. -/
def InitialDataType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (E → ℝ) → (E → ℝ) → Prop

def InitialDataValue : InitialDataType := fun _ _ _ φ ψ =>
  ConvexOn ℝ Set.univ φ ∧ ConvexOn ℝ Set.univ ψ ∧
    (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ φ x) ∧ φ 0 = 0 ∧ ψ 0 = 0

def MeanType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (E → ℝ) → (E → ℝ) → E → ℝ

noncomputable def arithmeticMeanValue : MeanType :=
  fun _ _ _ φ ψ x => (φ x + ψ x) / 2

noncomputable def infimalMeanValue : MeanType :=
  fun _ _ _ φ ψ x => sInf (Set.range fun y => φ (x + y) + ψ (x - y)) / 2

def IteratePairType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (E → ℝ) → (E → ℝ) → ℕ → (E → ℝ) × (E → ℝ)

noncomputable def iteratePairValue : IteratePairType := fun E _ _ φ ψ =>
  Nat.rec (φ, ψ) (fun _ p =>
    (arithmeticMeanValue E p.1 p.2, infimalMeanValue E p.1 p.2))

def SequenceType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (E → ℝ) → (E → ℝ) → ℕ → E → ℝ

noncomputable def phiValue : SequenceType :=
  fun E _ _ φ ψ n => (iteratePairValue E φ ψ n).1

noncomputable def psiValue : SequenceType :=
  fun E _ _ φ ψ n => (iteratePairValue E φ ψ n).2

def FiniteExtensionType :=
  ∀ (E : Type*), (E → ℝ) → P1.ExtendedConvexFunctions.ExtendedFunction E

def finiteExtensionValue : FiniteExtensionType := fun _ q x => (q x : WithTop ℝ)

def ConjugateType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (E → ℝ) → (E →L[ℝ] ℝ) → EReal

noncomputable def conjugateValue : ConjugateType := fun E _ _ q f =>
  P1.C06Conjugates.Spec.ConvexConjugateValue E (finiteExtensionValue E q) f

/-- Both initial functions and both recurrences, including the unscaled
infimum appearing in the manuscript. -/
def IterationEquations : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ),
    (∀ x, phiValue E φ₀ ψ₀ 0 x = φ₀ x) ∧
    (∀ x, psiValue E φ₀ ψ₀ 0 x = ψ₀ x) ∧
    (∀ n x, phiValue E φ₀ ψ₀ (n + 1) x =
      (phiValue E φ₀ ψ₀ n x + psiValue E φ₀ ψ₀ n x) / 2) ∧
    (∀ n x, psiValue E φ₀ ψ₀ (n + 1) x =
      sInf (Set.range fun y =>
        phiValue E φ₀ ψ₀ n (x + y) + psiValue E φ₀ ψ₀ n (x - y)) / 2)

/-- A nonnegative pair has a genuine, finite infimum, without compactness
or an assumption that a minimizing splitting variable exists. -/
def InfimalMeanIsGLB : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : E → ℝ), (∀ x, 0 ≤ φ x) → (∀ x, 0 ≤ ψ x) →
    ∀ x, IsGLB (Set.range fun y => φ (x + y) + ψ (x - y))
      (2 * infimalMeanValue E φ ψ x)

/-- Conditional-infimum totalization is never used in an invalid case
along any sequence satisfying the original initial hypotheses. -/
def IterationInfima : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ → ∀ n,
    (∀ x, 0 ≤ phiValue E φ₀ ψ₀ n x) ∧
    (∀ x, 0 ≤ psiValue E φ₀ ψ₀ n x) ∧
    (∀ x, IsGLB (Set.range fun y =>
      phiValue E φ₀ ψ₀ n (x + y) + psiValue E φ₀ ψ₀ n (x - y))
      (2 * psiValue E φ₀ ψ₀ (n + 1) x))

/-- The finite-valued input is proper in exactly the shared sense. -/
def FiniteExtensionProper : Prop :=
  ∀ (E : Type*) [Nonempty E] (q : E → ℝ),
    P1.ExtendedConvexFunctions.Spec.finiteDomainValue E (finiteExtensionValue E q) =
      Set.univ ∧
    P1.ExtendedConvexFunctions.Spec.ProperValue E (finiteExtensionValue E q)

def ConjugateFormula : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E → ℝ) (f : E →L[ℝ] ℝ),
    conjugateValue E q f = ⨆ x, ((f x - q x : ℝ) : EReal)

/-- This does not assert finiteness at any dual point or properness of the
conjugate. Values +∞ remain allowed. -/
def ConjugateNeverBottom : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E → ℝ) (f : E →L[ℝ] ℝ), conjugateValue E q f ≠ ⊥

end ExpandedFA.Asplund.Iteration.Spec
