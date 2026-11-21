import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Dirichlet
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The exact rational indicator on `[0,1]` from the calculus foundation,
extended by zero outside. Borel measurability is distinguished from integration
on completed Lebesgue measure. Discontinuity is relative, including endpoints. -/
noncomputable section
open Set MeasureTheory
namespace Specs.D11.Ch16.LebesgueNotRiemann

abbrev dirichlet_type := ℝ → ℝ
abbrev dirichlet_value : dirichlet_type :=
  Specs.SingleVariableAnalysis.Ch08.Dirichlet.dirichletValue

/-- The chosen representative is one precisely at rational points of the interval. -/
def exact_values : Prop := by
  classical
  exact ∀ x : ℝ, dirichlet_value x = if x ∈ Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x then 1 else 0

def borel_measurable : Prop :=
  Measurable dirichlet_value ∧ Measurable (fun x : Icc (0 : ℝ) 1 => dirichlet_value x)

/-- The measure is the completed Borel volume on the real line. Restriction
expresses the integral on the source interval. Actual measurability and absolute
integrability are asserted explicitly, so the integral is within the source convention. -/
def lebesgue_properties : Prop :=
  let μ := Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)
  @Measurable ℝ ℝ
      (Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ))
      (borel ℝ) dirichlet_value ∧
    dirichlet_value =ᵐ[μ.restrict (Icc (0 : ℝ) 1)] (fun _ => 0) ∧
    Integrable dirichlet_value (μ.restrict (Icc (0 : ℝ) 1)) ∧
    (∫ x, dirichlet_value x ∂(μ.restrict (Icc (0 : ℝ) 1))) = 0

def discontinuous_everywhere : Prop := ∀ x ∈ Icc (0 : ℝ) 1,
  ¬ ContinuousWithinAt dirichlet_value (Icc (0 : ℝ) 1) x

def not_riemann_integrable : Prop :=
  ¬ Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue dirichlet_value 0 1

/-- Two representatives equal a.e. on the interval have different Riemann
integrability status. The zero representative is continuous and integrable. -/
def representative_failure : Prop :=
  dirichlet_value =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun _ => 0) ∧
  Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue (fun _ => 0) 0 1 ∧
  ¬ Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue dirichlet_value 0 1

end Specs.D11.Ch16.LebesgueNotRiemann
