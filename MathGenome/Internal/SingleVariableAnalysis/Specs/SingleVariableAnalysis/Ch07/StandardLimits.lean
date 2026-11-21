import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SinCos
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers

/-!
K03.07.standard_limits, paper.tex:1846–1870. All increments and limits
are real. The logarithm and power limits are restricted to positive bases.
The variable-power assertion permits arbitrary approaches and zeros of u;
the shared positive-base power at base 1 has its ordinary value 1.
No convergence or boundedness of v itself is required.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.StandardLimits
open Filter Set
open scoped Topology

def sineQuotient : Prop :=
  Tendsto (fun h : ℝ => SinCos.realSeriesSinValue h / h) (𝓝[≠] 0) (𝓝 1)

def exponentialQuotient : Prop :=
  Tendsto (fun h : ℝ => (ExpConstruction.realSeriesExpValue h - 1) / h)
    (𝓝[≠] 0) (𝓝 1)

def logarithmQuotient : Prop :=
  Tendsto (fun h : ℝ => LogConstruction.seriesLogValue (1 + h) / h)
    (𝓝[{h : ℝ | h ≠ 0 ∧ 0 < 1 + h}] 0) (𝓝 1)

def variablePowerLimit : Prop :=
  ∀ {α : Type} (l : Filter α) (u v : α → ℝ) (L : ℝ),
    Tendsto u l (𝓝 0) → (∀ᶠ t in l, 0 < 1 + u t) →
    Tendsto (fun t => v t * u t) l (𝓝 L) →
    Tendsto (fun t => RealPowers.realPowerValue (1 + u t) (v t)) l
      (𝓝 (ExpConstruction.realSeriesExpValue L))

def powerAtZero : Prop :=
  ∀ v : ℝ, RealPowers.realPowerValue (1 + 0) v = 1

def reciprocalPowerLimit : Prop :=
  Tendsto (fun h : ℝ => RealPowers.realPowerValue (1 + h) (1 / h))
    (𝓝[{h : ℝ | h ≠ 0 ∧ 0 < 1 + h}] 0)
    (𝓝 (ExpConstruction.realSeriesExpValue 1))

end Specs.SingleVariableAnalysis.Ch07.StandardLimits
