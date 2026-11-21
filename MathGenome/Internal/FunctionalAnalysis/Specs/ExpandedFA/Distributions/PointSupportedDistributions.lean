import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing

/-! The scalar-linear version of the point-support assertion at
`paper.tex`, `fa2:p4:point-support`. Coordinate words index mixed partials,
as in the accepted compact-step seminorms. Repeated words are harmless:
the assertion is existence of a finite sum, without uniqueness of its
coefficients. The order is chosen separately for each distribution. -/

open Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace ExpandedFA.Distributions

/-- All coordinate words of length at most `m`. The empty word is included,
also when the ambient dimension is zero. -/
abbrev JetIndex (d m : ℕ) := Σ k : Fin (m + 1), (Fin k.val → Fin d)

/-- Evaluation of a coordinate partial derivative at a point. Continuity is
proved on every compact step, using exactly the accepted derivative maps. -/
noncomputable def coordinateJet (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (a : Domain d) {k : ℕ} (w : Fin k → Fin d) :
    ScalarDistribution 𝕜 Ω :=
  TestFunction.limitCLM 𝕜
    (fun φ => iteratedFDeriv ℝ k φ a (fun j => coordinateVector (w j)))
    (fun K _ => (BoundedContinuousFunction.evalCLM 𝕜 a).comp
      (coordinateDerivative 𝕜 K w))
    (fun _ _ _ => rfl)

/-- The derivative of the Dirac distribution, with the distributional sign.
Its value on a test is `(-1)^k` times that test's coordinate partial at `a`.
In particular the empty word gives the Dirac distribution itself. -/
noncomputable def deltaCoordinateDerivative (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (a : Domain d) {k : ℕ} (w : Fin k → Fin d) :
    ScalarDistribution 𝕜 Ω :=
  (-1 : 𝕜) ^ k • coordinateJet 𝕜 Ω a w

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.PointSupportedDistributions
open _root_.ExpandedFA.Distributions

/-- Support containment includes the zero distribution. No order is fixed
before the distribution is quantified. Both real and complex scalar fields,
and every Euclidean dimension, are included. -/
def pointSupportType : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (a : Domain d), a ∈ Ω → ∀ u : ScalarDistribution 𝕜 Ω,
    distributionSupport u ⊆ {a} →
    ∃ (m : ℕ) (c : JetIndex d m → 𝕜),
      u = ∑ i, c i • deltaCoordinateDerivative 𝕜 Ω a i.2

end Specs.ExpandedFA.Distributions.PointSupportedDistributions
