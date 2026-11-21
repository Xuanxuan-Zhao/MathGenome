import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpProperties

/-!
# Properties of the real factorial-series exponential

K03.07.exp_properties, paper.tex:1578–1593. All statements concern the
shared series construction. Its proved equality with `Real.exp` transfers
Mathlib's positivity, strict increase, range, and limits at infinity.
The derivative reuses the upstream real termwise differentiation theorem.

Provenance: `Analysis/Complex/Exponential.lean` proves positivity and strict
increase from the factorial-series bounds and the addition/reciprocal laws.
`Analysis/SpecialFunctions/Exp.lean` obtains the positive-infinity limit
from the linear lower bound, the negative-infinity limit from reciprocals,
and the range from continuity and these limits. No logarithm is used to
establish surjectivity here.
-/

noncomputable section
namespace SingleVariableAnalysis

open Filter Set
open scoped Topology

theorem real_expSeries_pos : Specs.SingleVariableAnalysis.Ch07.ExpProperties.positivity := by
  intro x
  change 0 < realSeriesExp x
  have he : realSeriesExp = Real.exp := funext expSeries_eq_realExp
  rw [he]
  exact Real.exp_pos x

theorem real_expSeries_derivative :
    Specs.SingleVariableAnalysis.Ch07.ExpProperties.derivative :=
  real_expSeries_hasDerivAt

theorem real_expSeries_strictMono :
    Specs.SingleVariableAnalysis.Ch07.ExpProperties.strictIncrease := by
  change StrictMono realSeriesExp
  have he : realSeriesExp = Real.exp := funext expSeries_eq_realExp
  rw [he]
  exact Real.exp_strictMono

theorem real_expSeries_bijOn_positive :
    Specs.SingleVariableAnalysis.Ch07.ExpProperties.positiveBijection := by
  change BijOn realSeriesExp univ (Ioi 0)
  refine ⟨fun x _ => real_expSeries_pos x, real_expSeries_strictMono.injective.injOn, ?_⟩
  intro y hy
  have hmem : y ∈ range Real.exp := by
    rw [Real.range_exp]
    exact hy
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, mem_univ _, (expSeries_eq_realExp x).trans hx⟩

theorem real_expSeries_tendsto_atBot :
    Specs.SingleVariableAnalysis.Ch07.ExpProperties.limitAtNegInfinity := by
  change Tendsto realSeriesExp atBot (𝓝 0)
  have he : realSeriesExp = Real.exp := funext expSeries_eq_realExp
  rw [he]
  exact Real.tendsto_exp_atBot

theorem real_expSeries_tendsto_atTop :
    Specs.SingleVariableAnalysis.Ch07.ExpProperties.limitAtPosInfinity := by
  change Tendsto realSeriesExp atTop atTop
  have he : realSeriesExp = Real.exp := funext expSeries_eq_realExp
  rw [he]
  exact Real.tendsto_exp_atTop

theorem real_expSeries_one_add_le :
    Specs.SingleVariableAnalysis.Ch07.ExpProperties.linearLowerBound := by
  intro x _hx
  change 1 + x ≤ realSeriesExp x
  have he : realSeriesExp = Real.exp := funext expSeries_eq_realExp
  rw [he, add_comm]
  exact Real.add_one_le_exp x

end SingleVariableAnalysis
