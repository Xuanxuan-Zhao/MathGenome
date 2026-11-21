import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.HyperbolicInverses
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Substitution

/-! K03.09.algebraic_substitution, paper.tex:2584–2619.
The elementary functions and π are the already fixed series/inverse objects.
`regularChangeOn` includes the bijection and continuous differential, so it
can be restricted to any compact subinterval for the proper substitution rule.
Quadratic classification is stated in completed-square coordinates, together
with the identity giving those coordinates for every nonzero leading coefficient.
No positive branch is inferred from the totalized value of `Real.sqrt`.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch09.AlgebraicSubstitution
open Set
open Ch07.SinCos Ch07.PiPeriod Ch07.Hyperbolic Ch07.HyperbolicInverses
open Ch08

def regularChangeOn (φ dφ : ℝ → ℝ) (D T : Set ℝ) : Prop :=
  BijOn φ D T ∧ ContinuousOn φ D ∧ ContinuousOn dφ D ∧
    ∀ u ∈ D, HasDerivAt φ (dφ u) u

def sineChange : Prop := ∀ A : ℝ, 0 < A →
  regularChangeOn (fun u => A * realSeriesSinValue u)
    (fun u => A * realSeriesCosValue u)
    (Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2)) (Ioo (-A) A) ∧
  ∀ u ∈ Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2),
    Real.sqrt (A ^ 2 - (A * realSeriesSinValue u) ^ 2) = A * realSeriesCosValue u ∧
      0 < A * realSeriesCosValue u

def coshChange : Prop := ∀ A : ℝ, 0 < A →
  regularChangeOn (fun u => A * realCoshValue u) (fun u => A * realSinhValue u)
    (Ioi 0) (Ioi A) ∧
  ∀ u ∈ Ioi 0,
    Real.sqrt ((A * realCoshValue u) ^ 2 - A ^ 2) = A * realSinhValue u ∧
      0 < A * realSinhValue u

def sinhChange : Prop := ∀ A : ℝ, 0 < A →
  regularChangeOn (fun u => A * realSinhValue u) (fun u => A * realCoshValue u)
    univ univ ∧
  ∀ u : ℝ,
    Real.sqrt ((A * realSinhValue u) ^ 2 + A ^ 2) = A * realCoshValue u ∧
      0 < A * realCoshValue u

def linearRootChange : Prop := ∀ α β : ℝ, α ≠ 0 →
  regularChangeOn (fun y => (y ^ 2 - β) / α) (fun y => 2 * y / α)
    (Ioi 0) {x | 0 < α * x + β} ∧
  (∀ y : ℝ, 0 < y → Real.sqrt (α * ((y ^ 2 - β) / α) + β) = y) ∧
  (∀ x : ℝ, 0 < α * x + β →
    0 < Real.sqrt (α * x + β) ∧ (Real.sqrt (α * x + β) ^ 2 - β) / α = x)

def completingSquare : Prop := ∀ a b c : ℝ, a ≠ 0 → ∀ x : ℝ,
  a * x ^ 2 + b * x + c =
    a * (x - (-b / (2 * a))) ^ 2 + (c - b ^ 2 / (4 * a))

/-- Positive leading coefficient and positive residual: the sinh type. -/
def positivePositiveQuadratic : Prop := ∀ a h r : ℝ, 0 < a → 0 < r →
  ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ,
    a * (x - h) ^ 2 + r = a * ((x - h) ^ 2 + A ^ 2) ∧
    0 < a * (x - h) ^ 2 + r ∧
    Real.sqrt (a * (x - h) ^ 2 + r) =
      Real.sqrt a * Real.sqrt ((x - h) ^ 2 + A ^ 2)

/-- Positive leading coefficient and negative residual: both exterior branches. -/
def positiveNegativeQuadratic : Prop := ∀ a h r : ℝ, 0 < a → r < 0 →
  ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ,
    a * (x - h) ^ 2 + r = a * ((x - h) ^ 2 - A ^ 2) ∧
    (0 < a * (x - h) ^ 2 + r ↔ x < h - A ∨ h + A < x) ∧
    Real.sqrt (a * (x - h) ^ 2 + r) =
      Real.sqrt a * Real.sqrt ((x - h) ^ 2 - A ^ 2)

/-- Negative leading coefficient and positive residual: the bounded sine type. -/
def negativePositiveQuadratic : Prop := ∀ a h r : ℝ, a < 0 → 0 < r →
  ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ,
    a * (x - h) ^ 2 + r = (-a) * (A ^ 2 - (x - h) ^ 2) ∧
    (0 < a * (x - h) ^ 2 + r ↔ h - A < x ∧ x < h + A) ∧
    Real.sqrt (a * (x - h) ^ 2 + r) =
      Real.sqrt (-a) * Real.sqrt (A ^ 2 - (x - h) ^ 2)

def negativeNonpositiveQuadratic : Prop :=
  ∀ a h r : ℝ, a < 0 → r ≤ 0 → ∀ x : ℝ, a * (x - h) ^ 2 + r ≤ 0

def zeroResidualQuadratic : Prop := ∀ a h : ℝ, 0 < a → ∀ x : ℝ,
  Real.sqrt (a * (x - h) ^ 2) = Real.sqrt a * |x - h| ∧
  (0 < a * (x - h) ^ 2 ↔ x ≠ h) ∧
  (x < h → Real.sqrt (a * (x - h) ^ 2) = Real.sqrt a * (h - x)) ∧
  (h < x → Real.sqrt (a * (x - h) ^ 2) = Real.sqrt a * (x - h))

def arsinhPrimitive : Prop := ∀ A : ℝ, 0 < A →
  ElementaryPrimitives.formulaOn (fun x => realArsinhValue (x / A))
    (fun x => 1 / Real.sqrt (x ^ 2 + A ^ 2)) univ

/-- A certified change may be used with any continuous real or complex
integrand on any interval containing its compact image. Orientation is retained. -/
def compactSubstitution : Prop :=
  ∀ (φ dφ : ℝ → ℝ) (D T : Set ℝ), regularChangeOn φ dφ D T →
  ∀ a b : ℝ, a ≤ b → Icc a b ⊆ D →
  ∀ I : Set ℝ, I.OrdConnected → MapsTo φ (Icc a b) I →
  (∀ f : ℝ → ℝ, ContinuousOn f I →
    ∃ hg : Integral.realIntegrableValue (fun t => f (φ t) * dφ t) a b,
    ∃ hf : Oriented.realIntegrableValue f (φ a) (φ b),
      Integral.realIntegralValue _ hg = Oriented.realIntegralValue f hf) ∧
  (∀ f : ℝ → ℂ, ContinuousOn f I →
    ∃ hg : Integral.complexIntegrableValue (fun t => f (φ t) * (dφ t : ℂ)) a b,
    ∃ hf : Oriented.complexIntegrableValue f (φ a) (φ b),
      Integral.complexIntegralValue _ hg = Oriented.complexIntegralValue f hf)

end Specs.SingleVariableAnalysis.Ch09.AlgebraicSubstitution
