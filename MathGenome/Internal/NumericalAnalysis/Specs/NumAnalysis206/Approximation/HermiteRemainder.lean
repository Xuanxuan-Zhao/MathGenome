import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Convex.Hull

/-! The real part of W51. The derivative values of `f` are the supplied
closed-interval jet, including the one-sided values at the endpoints.
The auxiliary polynomial derivatives are algebraic derivatives; for real
polynomials these are also their ordinary analytic derivatives. -/
namespace NumAnalysis206.Approximation.HermiteRemainderSpec
open Polynomial Set
open scoped BigOperators

/-- The Taylor representative of a residue class, in powers of `X - z`. -/
noncomputable def taylorResidue (z : ℝ) (m : ℕ) (d : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range m, C (d j / (j.factorial : ℝ)) * (X - C z) ^ j

/-- The derivative data carried by a real polynomial. -/
noncomputable def polynomialJet (p : ℝ[X]) (j : ℕ) (t : ℝ) : ℝ :=
  (derivative^[j] p).eval t

def PolynomialDerivatives : Prop :=
  ∀ (p : ℝ[X]) (j : ℕ), polynomialJet p j = iteratedDeriv j (fun t => p.eval t)

def TaylorResidueEquivalence : Prop :=
  ∀ (p : ℝ[X]) (z : ℝ) (m : ℕ) (d : ℕ → ℝ),
    ((X - C z) ^ m ∣ p - taylorResidue z m d ↔
      ∀ j < m, polynomialJet p j z = d j)

def RealHermiteInterpolation : Prop :=
  ∀ (s : ℕ), 0 < s → ∀ (z : Fin s → ℝ), Function.Injective z →
    ∀ (m : Fin s → ℕ), (∀ i, 0 < m i) → ∀ (d : Fin s → ℕ → ℝ),
      ∃! p : ℝ[X], p.degree < (↑(∑ i, m i) : WithBot ℕ) ∧
        ∀ i j, j < m i → polynomialJet p j (z i) = d i j

/-- The error formula for a polynomial matching the jet at all marked nodes.
The witness is pointwise and belongs to the closed hull of the nodes and `x`. -/
def HermiteErrorFormula : Prop :=
  ∀ {a b : ℝ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (s : ℕ), 0 < s → ∀ (z : Fin s → ℝ), Function.Injective z →
    (∀ i, z i ∈ Icc a b) → ∀ (m : Fin s → ℕ), (∀ i, 0 < m i) →
    IntervalCalculusSpec.jetValue a b (∑ i, m i) f D →
    ∀ (p : ℝ[X]), p.degree < (↑(∑ i, m i) : WithBot ℕ) →
    (∀ i j, j < m i → polynomialJet p j (z i) = D j (z i)) →
    ∀ x ∈ Icc a b,
      ∃ ξ ∈ convexHull ℝ (insert x (Set.range z)),
        f x - p.eval x = D (∑ i, m i) ξ / ((∑ i, m i).factorial : ℝ) *
          ∏ i, (x - z i) ^ m i

/-- Existence and uniqueness, the Taylor residues and derivative matching,
and the remainder formula for every point of the original interval. -/
def RealHermiteWithRemainder : Prop :=
  ∀ {a b : ℝ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (s : ℕ), 0 < s → ∀ (z : Fin s → ℝ), Function.Injective z →
    (∀ i, z i ∈ Icc a b) → ∀ (m : Fin s → ℕ), (∀ i, 0 < m i) →
    IntervalCalculusSpec.jetValue a b (∑ i, m i) f D →
      ∃! p : ℝ[X], p.degree < (↑(∑ i, m i) : WithBot ℕ) ∧
        (∀ i, (X - C (z i)) ^ m i ∣
          p - taylorResidue (z i) (m i) (fun j => D j (z i))) ∧
        (∀ i j, j < m i → polynomialJet p j (z i) = D j (z i)) ∧
        ∀ x ∈ Icc a b,
          ∃ ξ ∈ convexHull ℝ (insert x (Set.range z)),
            f x - p.eval x = D (∑ i, m i) ξ / ((∑ i, m i).factorial : ℝ) *
              ∏ i, (x - z i) ^ m i

end NumAnalysis206.Approximation.HermiteRemainderSpec
