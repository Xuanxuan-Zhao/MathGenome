import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.ElementaryPrimitives

/-!
The constant-numerator quadratic primitives in K03.09.partial_fractions,
paper.tex:2685–2700. The parameter is real and strictly positive; all
natural orders k ≥ 1 and all real arguments are retained. Index zero is
only a totalization of the recursive family, and has no primitive claim.
The square-root inverse is the source's d^(-1/2), and arctangent is the
canonical representative identified by the upstream inverse construction.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch09.QuadraticPrimitives

def quadraticPrimitiveType := ℝ → ℕ → ℝ → ℝ

/-- The recurrence constructs a specific primitive, without additive constants. -/
def quadraticPrimitiveValue (d : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun y => (Real.sqrt d)⁻¹ * Real.arctan (y / Real.sqrt d)
  | n + 2 => fun y =>
      y / (2 * ((n : ℝ) + 1) * d * (y ^ 2 + d) ^ (n + 1)) +
      (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1) * d) *
        quadraticPrimitiveValue d (n + 1) y

def quadraticPrimitiveBase : Prop :=
  ∀ (d y : ℝ), 0 < d → quadraticPrimitiveValue d 1 y =
    (Real.sqrt d)⁻¹ * Real.arctan (y / Real.sqrt d)

def quadraticPrimitiveRecurrence : Prop :=
  ∀ (d : ℝ) (k : ℕ), 0 < d → 2 ≤ k → ∀ y : ℝ,
    quadraticPrimitiveValue d k y =
      y / (2 * ((k : ℝ) - 1) * d * (y ^ 2 + d) ^ (k - 1)) +
      (2 * (k : ℝ) - 3) / (2 * ((k : ℝ) - 1) * d) *
        quadraticPrimitiveValue d (k - 1) y

def quadraticReductionDerivative : Prop :=
  ∀ (d : ℝ) (k : ℕ), 0 < d → 2 ≤ k → ∀ y : ℝ,
    HasDerivAt (fun t : ℝ => t / (t ^ 2 + d) ^ (k - 1))
      (2 * ((k : ℝ) - 1) * d / (y ^ 2 + d) ^ k -
        (2 * (k : ℝ) - 3) / (y ^ 2 + d) ^ (k - 1)) y

/-- Differentiation of a recurrence step, for any previous primitive. -/
def quadraticRecurrenceStep : Prop :=
  ∀ (d : ℝ) (k : ℕ), 0 < d → 2 ≤ k → ∀ (J : ℝ → ℝ) (y : ℝ),
    HasDerivAt J (1 / (y ^ 2 + d) ^ (k - 1)) y →
    HasDerivAt (fun t : ℝ =>
      t / (2 * ((k : ℝ) - 1) * d * (t ^ 2 + d) ^ (k - 1)) +
        (2 * (k : ℝ) - 3) / (2 * ((k : ℝ) - 1) * d) * J t)
      (1 / (y ^ 2 + d) ^ k) y

def quadraticPrimitiveHasDerivAt : Prop :=
  ∀ (d : ℝ) (k : ℕ), 0 < d → 1 ≤ k → ∀ y : ℝ,
    HasDerivAt (quadraticPrimitiveValue d k) (1 / (y ^ 2 + d) ^ k) y

/-- On every interval, including endpoints, these give all primitive constants. -/
def quadraticPrimitiveFormula : Prop :=
  ∀ (d : ℝ) (k : ℕ), 0 < d → 1 ≤ k →
    ElementaryPrimitives.formulaOn (quadraticPrimitiveValue d k)
      (fun y => 1 / (y ^ 2 + d) ^ k) Set.univ

end Specs.SingleVariableAnalysis.Ch09.QuadraticPrimitives
