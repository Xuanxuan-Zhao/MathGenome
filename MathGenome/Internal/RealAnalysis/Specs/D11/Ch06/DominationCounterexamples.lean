import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Independent statements for paper.tex:2060–2070. The natural index `n`
represents the paper's positive index `n+1`. We use completed Lebesgue measure,
and its restriction to `(0,1)` for the second example. Restriction is the usual
set-integral realization of that domain; functions are extended by zero.
All scalar evaluations have separate absolute-integrability obligations. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace Specs.D11.Ch06.DominationCounterexamples
open Specs.D11.Ch06.ScalarIntegral

abbrev lebesgue := (volume : Measure ℝ).completion
def openUnitInterval : Set ℝ := Ioo 0 1
abbrev intervalMeasure := lebesgue.restrict openUnitInterval

/-- The actual domain `(0,1)` with the trace of the completed sigma-algebra. -/
abbrev Interval := {x : NullMeasurableSpace ℝ volume // x ∈ openUnitInterval}
abbrev intervalDomainMeasure : Measure Interval := lebesgue.comap Subtype.val

def spreading_type := ℕ → ℝ → ℝ
def spreading_value : spreading_type := fun n =>
  (Ioo 0 ((n : ℝ) + 1)).indicator (fun _ => ((n : ℝ) + 1)⁻¹)

def concentrating_type := ℕ → ℝ → ℝ
def concentrating_value : concentrating_type := fun n =>
  (Ioo 0 ((n : ℝ) + 1)⁻¹).indicator (fun _ => (n : ℝ) + 1)

def domain_masses : Prop :=
  lebesgue univ = ∞ ∧ intervalMeasure univ = 1

def spreading_integrable : Prop :=
  ∀ n, scalarIntegrable_value lebesgue (spreading_value n)

def spreading_sup : Prop :=
  ∀ n, (⨆ x : ℝ, |spreading_value n x|) = ((n : ℝ) + 1)⁻¹

def spreading_uniform : Prop :=
  TendstoUniformly spreading_value (fun _ => 0) atTop

def spreading_integral : Prop :=
  ∀ n (h : scalarIntegrable_value lebesgue (spreading_value n)),
    scalarIntegral_value lebesgue (spreading_value n) h = 1

def spreading_integrals_not_tendsto_zero : Prop :=
  ∀ h : ∀ n, scalarIntegrable_value lebesgue (spreading_value n),
    ¬Tendsto (fun n => scalarIntegral_value lebesgue (spreading_value n) (h n))
      atTop (𝓝 0)

def spreading_no_integrable_dominator : Prop :=
  ¬∃ g : ℝ → ℝ, scalarIntegrable_value lebesgue g ∧
    (∀ x, 0 ≤ g x) ∧ (∀ n, ∀ᵐ x ∂lebesgue, |spreading_value n x| ≤ g x)

def concentrating_integrable : Prop :=
  ∀ n, scalarIntegrable_value intervalMeasure (concentrating_value n)

def concentrating_pointwise : Prop :=
  ∀ x ∈ Ioo (0 : ℝ) 1,
    Tendsto (fun n => concentrating_value n x) atTop (𝓝 0)

def concentrating_integral : Prop :=
  ∀ n (h : scalarIntegrable_value intervalMeasure (concentrating_value n)),
    scalarIntegral_value intervalMeasure (concentrating_value n) h = 1

def concentrating_integrals_not_tendsto_zero : Prop :=
  ∀ h : ∀ n, scalarIntegrable_value intervalMeasure (concentrating_value n),
    ¬Tendsto (fun n => scalarIntegral_value intervalMeasure (concentrating_value n) (h n))
      atTop (𝓝 0)

def concentrating_no_integrable_dominator : Prop :=
  ¬∃ g : ℝ → ℝ, scalarIntegrable_value intervalMeasure g ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ g x) ∧
    (∀ n, ∀ᵐ x ∂intervalMeasure, |concentrating_value n x| ≤ g x)

/-- The second counterexample on the interval as an actual measurable subtype.
This also makes applicability to dominators defined only on `(0,1)` explicit. -/
def concentrating_on_interval : Prop :=
  intervalDomainMeasure univ = 1 ∧
  (∀ x : Interval, Tendsto (fun n => concentrating_value n x.val) atTop (𝓝 0)) ∧
  ∃ h : ∀ n, scalarIntegrable_value intervalDomainMeasure
      (fun x : Interval => concentrating_value n x.val),
    (∀ n, scalarIntegral_value intervalDomainMeasure
      (fun x : Interval => concentrating_value n x.val) (h n) = 1) ∧
    (¬Tendsto (fun n => scalarIntegral_value intervalDomainMeasure
      (fun x : Interval => concentrating_value n x.val) (h n)) atTop (𝓝 0)) ∧
    (¬∃ g : Interval → ℝ, scalarIntegrable_value intervalDomainMeasure g ∧
      (∀ x, 0 ≤ g x) ∧
      (∀ n, ∀ᵐ x ∂intervalDomainMeasure, |concentrating_value n x.val| ≤ g x))

end Specs.D11.Ch06.DominationCounterexamples
