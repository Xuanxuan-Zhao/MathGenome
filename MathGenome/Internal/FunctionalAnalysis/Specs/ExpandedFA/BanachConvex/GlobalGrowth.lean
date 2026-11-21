import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent statements of the growth clause of
`fa2:p2:subgradient-slater` (paper.tex:8155–8157).

A finite function is represented by `φ : X → ℝ`. Its conjugate is exactly
the shared full-`EReal` conjugate of its canonical `WithTop ℝ` inclusion.
The conjugate domain is expressed by exclusion of +∞: for this finite
primal, −∞ is already excluded by the upstream conjugate theorem.
No continuity, lower semicontinuity, or completeness is assumed.
-/
namespace ExpandedFA.BanachConvex.Spec

universe u

/-- The exact constant k, including k = 0 and the zero space. -/
def GlobalGrowthLipschitz : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : X → ℝ) (k C : ℝ) (hk : 0 ≤ k),
    ConvexOn ℝ Set.univ φ → (∀ x, φ x ≤ k * ‖x‖ + C) →
    LipschitzWith ⟨k, hk⟩ φ ∧ Continuous φ

/-- D(φ*) is contained in the closed dual ball of radius k. -/
def GlobalGrowthConjugateDomain : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : X → ℝ) (k C : ℝ), 0 ≤ k →
    ConvexOn ℝ Set.univ φ → (∀ x, φ x ≤ k * ‖x‖ + C) →
    {f : X →L[ℝ] ℝ |
      ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue X
        (fun x => (φ x : WithTop ℝ)) f ≠ ⊤} ⊆ Metric.closedBall 0 k

/-- The same conclusion for the manuscript's shared extended-valued
objects, with finiteness everywhere. The real representative is produced
together with its pointwise identification, so no representation bridge
or regularity assumption is implicit. -/
def GlobalGrowthFiniteExtended : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExpandedFA.P1.ExtendedConvexFunctions.ExtendedFunction X)
    (k C : ℝ) (hk : 0 ≤ k), (∀ x, φ x ≠ ⊤) →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    (∀ x, φ x ≤ ((k * ‖x‖ + C : ℝ) : WithTop ℝ)) →
    ∃ ψ : X → ℝ, (∀ x, φ x = (ψ x : WithTop ℝ)) ∧
      LipschitzWith ⟨k, hk⟩ ψ ∧ Continuous ψ ∧
      {f : X →L[ℝ] ℝ |
        ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue X φ f ≠ ⊤} ⊆
        Metric.closedBall 0 k

end ExpandedFA.BanachConvex.Spec
