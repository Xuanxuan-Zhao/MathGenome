import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.Gronwall

/-! Independent statements for paper.tex, d13:05:perturbation (lines 1005–1031).
The state space can be any finite-dimensional real normed space, with any norm.
An ambient curve is used only on its actual closed time interval.

A C¹ curve on the closed interval is expressed by a continuous curve and a
continuous specified velocity, with within derivatives at every included point.
This retains one-sided endpoint derivatives and also allows a singleton interval;
it imposes no extension or regularity outside the interval. The second statement
uses the velocity prescribed by a second field. That field needs no Lipschitz
assumption, or even continuity away from the comparison curve.
-/

noncomputable section
open Set D13Unified

namespace Specs.D13Unified.Ch05.PerturbationResidual

universe u

/-- The residual estimate, in both time directions and also at L = 0. -/
def residualExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (a b s L δ : ℝ)
    (x y v : ℝ → E),
    Ch01.SolutionConcepts.compactSolutionOnValue F a b x →
    s ∈ Icc a b → 0 ≤ L → 0 ≤ δ →
    ContinuousOn y (Icc a b) → ContinuousOn v (Icc a b) →
    (∀ r ∈ Icc a b, HasDerivWithinAt y (v r) (Icc a b) r) →
    (∀ r ∈ Icc a b, (r, y r) ∈ F.domain) →
    (∀ r ∈ Icc a b,
      ‖F.eval r (x r) - F.eval r (y r)‖ ≤ L * ‖x r - y r‖) →
    (∀ r ∈ Icc a b, ‖v r - F.eval r (y r)‖ ≤ δ) →
    ∀ t ∈ Icc a b,
      ‖x t - y t‖ ≤ Real.exp (L * |t - s|) * ‖x s - y s‖ +
        δ * Gronwall.EValue L |t - s|

/-- Comparison of two fields on a set containing the second curve's graph.
The continuous velocity along y is the closed-interval C¹ hypothesis;
no regularity or state-difference estimate for g away from that graph is needed.
S need not be open, compact, or contain the first curve's graph. -/
def twoFieldsExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (g : ℝ → E → E)
    (S : Set (ℝ × E)) (a b s L δ : ℝ) (x y : ℝ → E),
    Ch01.SolutionConcepts.compactSolutionOnValue F a b x →
    s ∈ Icc a b → 0 ≤ L → 0 ≤ δ →
    ContinuousOn y (Icc a b) →
    ContinuousOn (fun r => g r (y r)) (Icc a b) →
    (∀ r ∈ Icc a b, HasDerivWithinAt y (g r (y r)) (Icc a b) r) →
    (∀ r ∈ Icc a b, (r, y r) ∈ F.domain) →
    (∀ r ∈ Icc a b, (r, y r) ∈ S) →
    (∀ r ∈ Icc a b,
      ‖F.eval r (x r) - F.eval r (y r)‖ ≤ L * ‖x r - y r‖) →
    (∀ p ∈ S, ‖F.eval p.1 p.2 - g p.1 p.2‖ ≤ δ) →
    ∀ t ∈ Icc a b,
      ‖x t - y t‖ ≤ Real.exp (L * |t - s|) * ‖x s - y s‖ +
        δ * Gronwall.EValue L |t - s|

end Specs.D13Unified.Ch05.PerturbationResidual
