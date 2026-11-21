import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.MaximalWeakBound

/-!
Independent statements for the remaining clauses of paper.tex:18180–18210.
The centered maximal function is the accepted supremum over Euclidean open
balls. Finite-p bounds retain extended values. The L¹ counterexample requires
positive dimension; in dimension zero Lebesgue space is a single point.
-/
noncomputable section
open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology
universe v

namespace ExpandedFA.SingularIntegrals.MaximalStrongBoundsAndDifferentiationSpec

/-- Uniform strong estimate for every finite exponent strictly above one.
The extended moment formulation includes finiteness and does not replace an
infinite maximal value by zero. -/
def FiniteStrongBound : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∃ C : ℝ≥0,
    ∀ {F : Type v} [NormedAddCommGroup F]
      (f : EuclideanSpace ℝ (Fin d) → F), MemLp f (ENNReal.ofReal p) volume →
      (∫⁻ x, MaximalWeakBoundSpec.MaximalValue volume f x ^ p) ^ (1 / p) ≤
        (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) volume

/-- The endpoint p=∞ has norm bound one. -/
def InfinityStrongBound : Prop := MaximalWeakBoundSpec.InfinityBound.{v}

/-- Almost everywhere finiteness, together with membership and the usual
norm estimate for the real representative, makes quotient applicability explicit. -/
def FiniteStrongMembership : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∃ C : ℝ≥0,
    ∀ {F : Type v} [NormedAddCommGroup F]
      (f : EuclideanSpace ℝ (Fin d) → F), MemLp f (ENNReal.ofReal p) volume →
      (∀ᵐ x ∂volume, MaximalWeakBoundSpec.MaximalValue volume f x < ∞) ∧
      MemLp (fun x => (MaximalWeakBoundSpec.MaximalValue volume f x).toReal)
        (ENNReal.ofReal p) volume ∧
      eLpNorm (fun x => (MaximalWeakBoundSpec.MaximalValue volume f x).toReal)
        (ENNReal.ofReal p) volume ≤ (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) volume

/-- The paper's unit-ball indicator, as a real-valued measurable function. -/
def unitBallIndicator (d : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (ball 0 1).indicator (fun _ => 1)

/-- Explicit tail estimate, equivalent to 2⁻ᵈ‖x‖⁻ᵈ outside the unit ball. -/
def IndicatorBallTail : Prop :=
  ∀ (d : ℕ) (x : EuclideanSpace ℝ (Fin d)), 1 ≤ ‖x‖ →
    ((ENNReal.ofReal (2 * ‖x‖)) ^ d)⁻¹ ≤
      MaximalWeakBoundSpec.MaximalValue volume (unitBallIndicator d) x

/-- One L¹ function has infinite maximal integral in every positive dimension;
thus no finite L¹ operator bound can hold. -/
def NotStrongOne : Prop :=
  ∀ (d : ℕ), 0 < d → Integrable (unitBallIndicator d) volume ∧
    (∫⁻ x, MaximalWeakBoundSpec.MaximalValue volume (unitBallIndicator d) x) = ∞

/-- Mean absolute oscillation about the actual a.e. value tends to zero as
all positive radii decrease to zero. No global integrability is imposed. -/
def LebesgueDifferentiation : Prop :=
  ∀ (d : ℕ) {F : Type v} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin d) → F), LocallyIntegrable f volume →
    ∀ᵐ x ∂volume, Tendsto
      (fun r : ℝ => (volume.real (ball x r))⁻¹ * ∫ y in ball x r, ‖f y - f x‖)
      (𝓝[>] 0) (𝓝 0)

end ExpandedFA.SingularIntegrals.MaximalStrongBoundsAndDifferentiationSpec
