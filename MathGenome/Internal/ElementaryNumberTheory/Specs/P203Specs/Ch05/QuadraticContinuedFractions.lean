import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.ContinuedFractionAlgorithm
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Logic.Function.Iterate

/-! Canonical objects for paper.tex, §Periodicity and reduced complete quotients
(lines 2408–2413). Quadraticity means algebraic degree exactly two over ℚ.
No periodicity or choice of a quadratic equation enters this definition. -/
namespace P203Specs

/-- A real algebraic number of degree exactly two over ℚ. -/
def QuadraticIrrational (x : ℝ) : Prop :=
  IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree = 2

/-- The other root of the monic minimal quadratic, by the sum of roots.
Only its values on quadratic irrationals are used. -/
noncomputable def quadraticConjugate (x : ℝ) : ℝ :=
  -((minpoly ℚ x).coeff 1 : ℝ) - x

/-- Reducedness includes quadratic irrationality. -/
def ReducedQuadratic (x : ℝ) : Prop :=
  QuadraticIrrational x ∧ 1 < x ∧ -1 < quadraticConjugate x ∧ quadraticConjugate x < 0

/-- The quotient map, used on irrational inputs; total real division supplies
an irrelevant extension to other reals. The algorithm itself still stops. -/
noncomputable def continuedFractionStep (x : ℝ) : ℝ :=
  1 / (x - (⌊x⌋ : ℝ))

/-- A digit sequence is attached only when every canonical digit exists. -/
def IsDigitSequence (x : ℝ) (a : ℕ → ℤ) : Prop :=
  ∀ n, partialQuotient x n = some (a n)

/-- Periodicity after a finite number of entries, with a positive period. -/
def EventuallyPeriodicDigits (a : ℕ → ℤ) : Prop :=
  ∃ m r : ℕ, 0 < r ∧ ∀ n, m ≤ n → a (n + r) = a n

/-- Periodicity from entry zero, with a positive period. -/
def PurelyPeriodicDigits (a : ℕ → ℤ) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∀ n, a (n + r) = a n

/-- Eventual periodicity of the infinite canonical simple continued fraction. -/
def EventuallyPeriodicCF (x : ℝ) : Prop :=
  ∃ a : ℕ → ℤ, IsDigitSequence x a ∧ EventuallyPeriodicDigits a

/-- Pure periodicity of the infinite canonical simple continued fraction. -/
def PurelyPeriodicCF (x : ℝ) : Prop :=
  ∃ a : ℕ → ℤ, IsDigitSequence x a ∧ PurelyPeriodicDigits a

def QuadraticIrrationalType := ℝ → Prop
def QuadraticConjugateType := ℝ → ℝ
def ReducedQuadraticType := ℝ → Prop
def ContinuedFractionStepType := ℝ → ℝ
def IsDigitSequenceType := ℝ → (ℕ → ℤ) → Prop
def PeriodicDigitsType := (ℕ → ℤ) → Prop
def PeriodicCFType := ℝ → Prop

/-- Degree two really implies irrationality. -/
def QuadraticIsIrrational : Prop :=
  ∀ x : ℝ, QuadraticIrrational x → Irrational x

/-- The conjugate is irrational, distinct, and exactly the other real root. -/
def QuadraticOtherRoot : Prop :=
  ∀ x : ℝ, QuadraticIrrational x →
    Irrational (quadraticConjugate x) ∧ quadraticConjugate x ≠ x ∧
      ∀ y : ℝ, Polynomial.aeval y (minpoly ℚ x) = 0 ↔
        y = x ∨ y = quadraticConjugate x

/-- Independence of every defining irreducible polynomial, including nonmonic ones.
In particular its degree is two, and its other root gives the same conjugate. -/
def ConjugateIndependent : Prop :=
  ∀ (x : ℝ), QuadraticIrrational x → ∀ p : Polynomial ℚ,
    Irreducible p → Polynomial.aeval x p = 0 →
      p.natDegree = 2 ∧
      quadraticConjugate x = -((p.coeff 1 : ℝ) / (p.coeff 2 : ℝ)) - x ∧
      ∀ y : ℝ, Polynomial.aeval y p = 0 ↔ y = x ∨ y = quadraticConjugate x

def ConjugateQuadratic : Prop :=
  ∀ x : ℝ, QuadraticIrrational x →
    QuadraticIrrational (quadraticConjugate x) ∧
    minpoly ℚ (quadraticConjugate x) = minpoly ℚ x ∧
    quadraticConjugate (quadraticConjugate x) = x

def StepIrrational : Prop :=
  ∀ x : ℝ, Irrational x → Irrational (continuedFractionStep x)

/-- All iterates are the actual zero-based complete quotients; none is fabricated
past a termination. -/
def QuotientIterates : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ n : ℕ,
    Irrational (continuedFractionStep^[n] x) ∧
    completeQuotient x n = some (continuedFractionStep^[n] x) ∧
    partialQuotient x n = some ⌊continuedFractionStep^[n] x⌋

def InfiniteDigitsIff : Prop :=
  ∀ x : ℝ, (∃ a : ℕ → ℤ, IsDigitSequence x a) ↔ Irrational x

def DigitSequenceUnique : Prop :=
  ∀ (x : ℝ) (a b : ℕ → ℤ), IsDigitSequence x a → IsDigitSequence x b → a = b

/-- These interfaces expose the quantifiers of periodicity directly on the
canonical digit options, with infinitude explicitly required. -/
def EventualPeriodicityBridge : Prop :=
  ∀ x : ℝ, EventuallyPeriodicCF x ↔
    Irrational x ∧ ∃ m r : ℕ, 0 < r ∧
      ∀ n, m ≤ n → partialQuotient x (n + r) = partialQuotient x n

def PurePeriodicityBridge : Prop :=
  ∀ x : ℝ, PurelyPeriodicCF x ↔
    Irrational x ∧ ∃ r : ℕ, 0 < r ∧
      ∀ n, partialQuotient x (n + r) = partialQuotient x n

def PureIsEventual : Prop :=
  ∀ x : ℝ, PurelyPeriodicCF x → EventuallyPeriodicCF x

end P203Specs
