import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
open MeasureTheory Polynomial Matrix

namespace NumAnalysis206.Quadrature

/-- The finite absolute moment hypothesis; the ambient measures are Borel measures on ℝ. -/
def FiniteMoment (μ : Measure ℝ) (k : ℕ) : Prop :=
  Integrable (fun x : ℝ => |x| ^ k) μ

/-- Indices are exactly 0,…,n. -/
def gramMatrix (μ : Measure ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => ∫ x : ℝ, x ^ (i.val + j.val) ∂μ

/-- A cardinality condition which also counts infinite supports correctly. -/
def HasSupportPoints (μ : Measure ℝ) (n : ℕ) : Prop :=
  ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ μ.support ∧ s.card = n + 1

namespace Specs

/-- In fact the conclusions hold without restricting the measure to an interval,
and also for n=0. This stronger formulation includes all source hypotheses. -/
def lowerMoments : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), FiniteMoment μ (2 * n) →
    ∀ k ≤ 2 * n, Integrable (fun x : ℝ => |x| ^ k) μ ∧
      Integrable (fun x : ℝ => x ^ k) μ

def polynomialIntegrable : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), FiniteMoment μ (2 * n) →
    ∀ p : ℝ[X], p.natDegree ≤ 2 * n → Integrable (fun x => p.eval x) μ

def polynomialProducts : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), FiniteMoment μ (2 * n) →
    ∀ p q : ℝ[X], p.natDegree + q.natDegree ≤ 2 * n →
      Integrable (fun x => p.eval x * q.eval x) μ

def closedSupport : Prop :=
  ∀ μ : Measure ℝ,
    (∀ x : ℝ, x ∈ μ.support ↔
      ∀ U : Set ℝ, x ∈ U → IsOpen U → 0 < μ U) ∧
    IsClosed μ.support ∧ μ μ.supportᶜ = 0

def gramIdentity : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), FiniteMoment μ (2 * n) →
    ∀ c : Fin (n + 1) → ℝ,
      c ⬝ᵥ ((gramMatrix μ n) *ᵥ c) =
        ∫ x : ℝ, (∑ j : Fin (n + 1), c j * x ^ j.val) ^ 2 ∂μ

def gramSupport : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), FiniteMoment μ (2 * n) →
    ((gramMatrix μ n).PosDef ↔ HasSupportPoints μ n)

def polynomialSquarePositive : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), FiniteMoment μ (2 * n) →
    (gramMatrix μ n).PosDef → ∀ p : ℝ[X], p ≠ 0 → p.natDegree ≤ n →
      0 < ∫ x : ℝ, (p.eval x) ^ 2 ∂μ

end Specs
end NumAnalysis206.Quadrature
