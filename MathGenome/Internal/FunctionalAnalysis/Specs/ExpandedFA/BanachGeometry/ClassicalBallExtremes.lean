import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.SequenceBallExtremes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent specification of `fa2:p2:classical-ball-extremes`,
paper.tex 8752–8789. Convexity uses real scalars for both real and complex
function spaces; `Lp` is the quotient by Lebesgue almost-everywhere equality.
The sequence spaces and their coordinate convention are the shared upstream ones. -/
noncomputable section
open MeasureTheory
universe u
namespace ExpandedFA.BanachGeometry.ClassicalBallExtremes.Spec

/-- All sequence conclusions, including the explicit real signs and the
complex modulus-one phases. The interior p range means every norm-one vector. -/
def SequenceExtremes : Prop :=
  SequenceBallExtremes.Spec.InfinityExtremes.{u} ∧
  SequenceBallExtremes.Spec.ConvergentExtremes.{u} ∧
  SequenceBallExtremes.Spec.C0Extremes.{u} ∧
  SequenceBallExtremes.Spec.L1Extremes.{u} ∧
  SequenceBallExtremes.Spec.LpExtremes.{u} ∧
  SequenceBallExtremes.Spec.RealInfinityExtremes ∧
  SequenceBallExtremes.Spec.RealConvergentExtremes ∧
  SequenceBallExtremes.Spec.RealL1Extremes

/-- The actual L¹ space on the real line with Lebesgue measure, over either
scalar field. In particular this is not the counting-measure sequence space. -/
def LebesgueL1NoExtremes : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Set.extremePoints ℝ (Metric.closedBall (0 : Lp 𝕜 1 (volume : Measure ℝ)) 1) = ∅

end ExpandedFA.BanachGeometry.ClassicalBallExtremes.Spec
