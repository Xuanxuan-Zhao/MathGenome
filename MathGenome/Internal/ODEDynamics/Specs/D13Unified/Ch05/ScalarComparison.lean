import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz

/-! Independent specification of paper.tex, d13:05:comparison.
Ambient representatives are used only on `[a,b] × J`. Local control is
relative to this closed time interval and uses the shared state-difference
predicate. Thus no extension of the field past either endpoint is required.
The derivative witnesses are within derivatives on the actual closed interval;
on a nondegenerate interval these give the right/left endpoint derivatives.
-/

noncomputable section
open Set Metric

namespace Specs.D13Unified.Ch05.ScalarComparison

/-- The same local state Lipschitz estimate as for the shared open-domain ODE,
restricted to the permitted times. Constants and radii depend on the center. -/
def localControl (f : ℝ → ℝ → ℝ) (T J : Set ℝ) : Prop :=
  ∀ s ∈ T, ∀ ξ ∈ J, ∃ δ ρ L : ℝ,
    0 < δ ∧ 0 < ρ ∧ 0 ≤ L ∧ ball ξ ρ ⊆ J ∧
    Specs.D13Unified.Ch03.LocalLipschitz.stateLipschitzOnValue f
      (T ∩ ball s δ) (ball ξ ρ) L

/-- Subsolutions and supersolutions, with no monotonicity assumption and
no globally specified Lipschitz constant. `J` may have infinite endpoints.
A singleton time interval is allowed. Values off the stated domains have no
mathematical role. -/
def scalarComparisonExpected : Prop :=
  ∀ (J : Set ℝ), IsOpen J → OrdConnected J →
  ∀ (a b : ℝ), a ≤ b → ∀ (f : ℝ → ℝ → ℝ),
    ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) (Icc a b ×ˢ J) →
    localControl f (Icc a b) J →
    ∀ (u v u' v' : ℝ → ℝ),
      ContDiffOn ℝ 1 u (Icc a b) → ContDiffOn ℝ 1 v (Icc a b) →
      MapsTo u (Icc a b) J → MapsTo v (Icc a b) J →
      (∀ t ∈ Icc a b, HasDerivWithinAt u (u' t) (Icc a b) t) →
      (∀ t ∈ Icc a b, HasDerivWithinAt v (v' t) (Icc a b) t) →
      (∀ t ∈ Icc a b, u' t ≤ f t (u t)) →
      (∀ t ∈ Icc a b, f t (v t) ≤ v' t) →
      u a ≤ v a → ∀ t ∈ Icc a b, u t ≤ v t

end Specs.D13Unified.Ch05.ScalarComparison
