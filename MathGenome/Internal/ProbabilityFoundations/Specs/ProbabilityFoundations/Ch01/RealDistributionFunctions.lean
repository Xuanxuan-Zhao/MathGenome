import Mathlib.MeasureTheory.Measure.Stieltjes

/-! Independent statements for the real part of paper.tex, Theorem 1.7
(lines 234–264). All measures are on the usual Borel measurable space of ℝ.
Right continuity is the only continuity hypothesis; atoms are permitted. -/

open MeasureTheory Set Filter
open scoped Topology

namespace Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions

def distributionFunctionType := Measure ℝ → ℝ → ℝ

/-- The real mass of a closed lower half-line. -/
noncomputable def distributionFunctionValue : distributionFunctionType :=
  fun μ x => (μ (Iic x)).toReal

def isDistributionFunctionType := (ℝ → ℝ) → Prop

/-- Exactly the four conditions in the source's characterization. -/
def isDistributionFunctionValue : isDistributionFunctionType := fun F =>
  Monotone F ∧ (∀ x, ContinuousWithinAt F (Ici x) x) ∧
    Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1)

def propertiesType : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    isDistributionFunctionValue (distributionFunctionValue μ)

def existenceUniquenessType : Prop :=
  ∀ F : ℝ → ℝ, isDistributionFunctionValue F →
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧ distributionFunctionValue μ = F

/-- The weak inequality includes the empty interval when a = b. -/
def intervalMassType : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ), a ≤ b →
    (μ (Ioc a b)).toReal = distributionFunctionValue μ b - distributionFunctionValue μ a

/-- The value used in the atom formula really is the limit from below. -/
def leftLimitType : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ),
    Tendsto (distributionFunctionValue μ) (𝓝[<] a)
      (𝓝 (Function.leftLim (distributionFunctionValue μ) a)) ∧
    (μ (Iio a)).toReal = Function.leftLim (distributionFunctionValue μ) a

def atomMassType : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ),
    (μ {a}).toReal = distributionFunctionValue μ a -
      Function.leftLim (distributionFunctionValue μ) a

end Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions
