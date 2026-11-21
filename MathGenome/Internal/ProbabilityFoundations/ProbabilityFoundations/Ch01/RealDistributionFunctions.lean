import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions
import Mathlib.Probability.CDF

/-! Real distribution functions: their characterization, unique probability
laws, half-open interval increments, and jumps at atoms. -/

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace ProbabilityFoundations.Ch01

/-- The distribution function is the real mass of (-∞, x]. -/
noncomputable def realDistributionFunction (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ (Iic x)).toReal

/-- The four necessary and sufficient conditions for a real CDF. -/
def IsRealDistributionFunction (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ (∀ x, ContinuousWithinAt F (Ici x) x) ∧
    Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1)

/-- Identify the explicit half-line definition with Mathlib's bundled CDF. -/
private theorem realDistributionFunction_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    realDistributionFunction μ = ⇑(cdf μ) := by
  funext x
  exact (cdf_eq_real μ x).symm

theorem realDistributionFunction_properties (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsRealDistributionFunction (realDistributionFunction μ) := by
  rw [realDistributionFunction_eq_cdf]
  exact ⟨monotone_cdf μ, (cdf μ).right_continuous,
    tendsto_cdf_atBot μ, tendsto_cdf_atTop μ⟩

/-- Stieltjes measure gives existence, and equality of CDFs gives uniqueness. -/
theorem existsUnique_probabilityMeasure_of_distributionFunction (F : ℝ → ℝ)
    (hF : IsRealDistributionFunction F) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧ realDistributionFunction μ = F := by
  let f : StieltjesFunction ℝ := ⟨F, hF.1, hF.2.1⟩
  have : IsProbabilityMeasure f.measure := f.isProbabilityMeasure hF.2.2.1 hF.2.2.2
  have hcdf : cdf f.measure = f :=
    cdf_measure_stieltjesFunction f hF.2.2.1 hF.2.2.2
  have hμ : realDistributionFunction f.measure = F := by
    rw [realDistributionFunction_eq_cdf, hcdf]
  refine ⟨f.measure, ⟨inferInstance, hμ⟩, ?_⟩
  rintro ν ⟨hν, hνF⟩
  let : IsProbabilityMeasure ν := hν
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  have hfun : ⇑(cdf ν) = ⇑(cdf f.measure) := by
    rw [← realDistributionFunction_eq_cdf, ← realDistributionFunction_eq_cdf, hνF, hμ]
  exact congrFun hfun x

/-- Includes a = b and permits arbitrary atomic probability laws. -/
theorem realDistributionFunction_interval_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a ≤ b) :
    (μ (Ioc a b)).toReal = realDistributionFunction μ b - realDistributionFunction μ a := by
  rw [realDistributionFunction_eq_cdf]
  conv_lhs => rw [← measure_cdf μ, StieltjesFunction.measure_Ioc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr ((cdf μ).mono hab))

/-- The left limit exists at every real a and equals the mass of (-∞, a). -/
theorem realDistributionFunction_leftLimit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) :
    Tendsto (realDistributionFunction μ) (𝓝[<] a)
      (𝓝 (Function.leftLim (realDistributionFunction μ) a)) ∧
    (μ (Iio a)).toReal = Function.leftLim (realDistributionFunction μ) a := by
  rw [realDistributionFunction_eq_cdf]
  refine ⟨(cdf μ).mono.tendsto_leftLim a, ?_⟩
  have hn : 0 ≤ Function.leftLim (cdf μ) a :=
    (cdf_nonneg μ (a - 1)).trans ((cdf μ).mono.le_leftLim (sub_lt_self a zero_lt_one))
  conv_lhs => rw [← measure_cdf μ, StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot μ), sub_zero]
  exact ENNReal.toReal_ofReal hn

/-- Each atom has mass equal to the jump of the CDF. -/
theorem realDistributionFunction_atom_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) :
    (μ {a}).toReal = realDistributionFunction μ a -
      Function.leftLim (realDistributionFunction μ) a := by
  rw [realDistributionFunction_eq_cdf]
  conv_lhs => rw [← measure_cdf μ, StieltjesFunction.measure_singleton]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr ((cdf μ).mono.leftLim_le le_rfl))

end ProbabilityFoundations.Ch01
