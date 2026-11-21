import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WholeSpaceW2p
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DifferenceQuotientConverse

/-! Independent original targets for `pde:elliptic-poisson-w2p`,
paper.tex:1833–1847. The input functions have only local Lᵖ regularity.
The canonical Sobolev space retains every distributional derivative and uses
the sum norm fixed by the common spatial interface. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace P201Specs.Elliptic.LocalW2p

/-- Compact containment includes compactness of the closure. -/
abbrev RelativelyCompactIn {n : ℕ} (V Ω : Domain n) : Prop :=
  P102.U4.DifferenceQuotient.RelativelyCompactIn V Ω

/-- Local Lᵖ is tested on every relatively compact open subset. -/
abbrev LocallyMemLp {n : ℕ} (Ω : Domain n) (p : ℝ≥0∞)
    (u : Space n → ℝ) : Prop :=
  P102.U4.DifferenceQuotient.LocallyMemLp Ω p u

/-- The canonical Sobolev representative is the original function almost
 everywhere. Its distributional derivatives are therefore derivatives of the
 original distribution, not of a newly selected unrelated representative. -/
def RepresentsOn {n : ℕ} {V : Domain n} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Space n → ℝ) (w : W ℝ V 2 p) : Prop :=
  (P102.U4.sobolevUnderlying w : Space n → ℝ) =ᵐ[domainMeasure V] u ∧
  regularDistribution V (P102.U4.sobolevUnderlying w) = regularDistribution V u ∧
  ∀ α : P102.U4.SobolevIndex n 2,
    distributionDerivative α.val (regularDistribution V u) =
      regularDistribution V (P102.U4.sobolevDerivative w α)

/-- No first weak derivative or classical representative is assumed. -/
def LocalRegularityStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      simpa using ENNReal.ofReal_le_ofReal hp.le⟩
    ∀ (Ω : Domain n) (u f : Space n → ℝ),
      LocallyMemLp Ω (ENNReal.ofReal p) u →
      LocallyMemLp Ω (ENNReal.ofReal p) f →
      -distributionLaplacian (regularDistribution Ω u) = regularDistribution Ω f →
      ∀ (V : Domain n), RelativelyCompactIn V Ω →
        ∃ w : W ℝ V 2 (ENNReal.ofReal p), RepresentsOn u w

/-- The domain and exponent are fixed before the constant and the data.
Neither boundary regularity nor connectedness nor nonemptiness is imposed. -/
def InteriorEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      simpa using ENNReal.ofReal_le_ofReal hp.le⟩
    ∀ (Ω V U : Domain n), RelativelyCompactIn V U → RelativelyCompactIn U Ω →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u f : Space n → ℝ),
        LocallyMemLp Ω (ENNReal.ofReal p) u →
        LocallyMemLp Ω (ENNReal.ofReal p) f →
        -distributionLaplacian (regularDistribution Ω u) = regularDistribution Ω f →
        ∃ w : W ℝ V 2 (ENNReal.ofReal p), RepresentsOn u w ∧
          ‖w‖ ≤ C * ((eLpNorm f (ENNReal.ofReal p) (domainMeasure U)).toReal +
            (eLpNorm u (ENNReal.ofReal p) (domainMeasure U)).toReal)

/-- The whole-space clause uses the usual Euclidean (Frobenius) Hessian. -/
def WholeSpaceEstimateStatement : Prop :=
  WholeSpaceW2p.FrobeniusEstimateStatement

end P201Specs.Elliptic.LocalW2p
