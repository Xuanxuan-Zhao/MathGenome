import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.DunfordPettisContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Independent statements for `fa2:p2:dp-classical-examples`, including the
arbitrary-measure amendment in parts/part2-dp-examples.tex. The endpoint
statement uses the full continuous scalar-linear dual, with no measure-size
or separability assumption. -/
namespace ExpandedFA.Compactness.DunfordPettisL1.Spec
open MeasureTheory
universe u w

/-- The diagonal weak-null test and the operator Dunford--Pettis property
for ordinary L¹ over an arbitrary positive measure. -/
def L1Theorem (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (α : Type u) [MeasurableSpace α] (μ : Measure α),
    DunfordPettisCriterion.Spec.WeakNullTestingPropertyValue 𝕜 (Lp 𝕜 1 μ) ∧
      DunfordPettisCriterion.Spec.DunfordPettisPropertyValue.{0,u,w} 𝕜 (Lp 𝕜 1 μ)

/-- The L¹ statement uniformly over the real or complex scalar field. -/
def AllScalarL1Theorem : Prop := ∀ (𝕜 : Type) [RCLike 𝕜], L1Theorem.{u,w} 𝕜

/-- Both classical examples over the real field, including empty compact
spaces and arbitrary positive measures. -/
def RealClassicalExamples : Prop :=
  DunfordPettisContinuousFunctions.Spec.ContinuousFunctionsTheorem.{u,w} ℝ ∧
    L1Theorem.{u,w} ℝ

/-- Both classical examples over the complex field. -/
def ComplexClassicalExamples : Prop :=
  DunfordPettisContinuousFunctions.Spec.ContinuousFunctionsTheorem.{u,w} ℂ ∧
    L1Theorem.{u,w} ℂ

end ExpandedFA.Compactness.DunfordPettisL1.Spec
