import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.SingularContinuousCounterexample
import MathGenome.Internal.RealAnalysis.D11.Ch03.CantorFunction
import MathGenome.Internal.RealAnalysis.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcFtc
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace D11.Ch12.SingularContinuousCounterexample
open D11.Ch03
local notation "Γ" => Specs.D11.Ch03.CantorFunction.Gamma_value
local notation "C" => Specs.D11.Ch03.CantorSet.C_value

theorem function_properties : Specs.D11.Ch12.SingularContinuousCounterexample.function_properties :=
  ⟨CantorFunction.continuous, CantorFunction.monotone, CantorFunction.maps_unit_interval,
    CantorFunction.endpoints⟩

theorem variation_one : Specs.D11.Ch12.SingularContinuousCounterexample.variation_one := by
  change variation Γ 0 1 = 1
  rw [variation_eq_eVariationOn]
  have h := (CantorFunction.monotone.monotoneOn univ).eVariationOn_eq
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  simpa [CantorFunction.endpoints.1, CantorFunction.endpoints.2] using h

lemma Gamma_zero_of_le_zero {x : ℝ} (hx : x ≤ 0) : Γ x = 0 := by
  apply le_antisymm
  · exact (CantorFunction.monotone hx).trans_eq CantorFunction.endpoints.1
  · exact (CantorFunction.Gamma_bounds x).1

lemma Gamma_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : Γ x = 1 := by
  apply le_antisymm
  · exact (CantorFunction.Gamma_bounds x).2
  · exact CantorFunction.endpoints.2.symm.trans_le (CantorFunction.monotone hx)

lemma extension_eq_Gamma : extension = Γ := by
  funext x
  change Γ (max 0 (min 1 x)) - Γ 0 = Γ x
  rw [CantorFunction.endpoints.1, sub_zero]
  rcases le_or_gt x 0 with hx | hx
  · rw [max_eq_left ((min_le_right 1 x).trans hx), CantorFunction.endpoints.1,
      Gamma_zero_of_le_zero hx]
  · rcases le_or_gt 1 x with h1 | h1
    · rw [min_eq_left h1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        CantorFunction.endpoints.2, Gamma_one_of_one_le h1]
    · rw [min_eq_right h1.le, max_eq_right hx.le]

lemma Gamma_bv : BV Γ 0 1 := by
  change variation Γ 0 1 < ⊤
  rw [show variation Γ 0 1 = 1 from variation_one]
  exact ENNReal.one_lt_top

lemma extension_nbv_continuous :
    ScalarStieltjesCorrespondence.NBV extension ∧ Continuous extension := by
  exact (NormalizedStieltjes.compact_continuous Γ (by norm_num : (0 : ℝ) < 1)
    Gamma_bv CantorFunction.continuous).imp_right fun h => h.1

lemma Gamma_continuous : Continuous Γ := by
  rw [← extension_eq_Gamma]
  exact extension_nbv_continuous.2

theorem extension_properties :
    Specs.D11.Ch12.SingularContinuousCounterexample.extension_properties := by
  refine ⟨extension_nbv_continuous.1, extension_nbv_continuous.2, ?_, ?_, ?_⟩
  · intro x hx
    rw [extension_eq_Gamma]
    exact Gamma_zero_of_le_zero hx
  · intro x _
    exact congrFun extension_eq_Gamma x
  · intro x hx
    rw [extension_eq_Gamma]
    exact Gamma_one_of_one_le hx

/-- Every point off the closed Cantor set has an interval neighborhood with no
Cantor points. Surjectivity of the upstream digit map then forces constancy. -/
lemma Gamma_locally_constant {x : ℝ} (hx : x ∉ C) :
    ∃ a b : ℝ, x ∈ Ioo a b ∧ EqOn Γ (fun _ => Γ x) (Ioo a b) := by
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (isClosed_cantorSet.isOpen_compl.mem_nhds hx)
  refine ⟨a, b, ⟨hax, hxb⟩, ?_⟩
  intro y hy
  rcases le_total y x with hyx | hxy
  · apply CantorFunction.Gamma_eq_of_no_C_between hyx
    apply disjoint_left.mpr
    intro z hz hzc
    exact hab ⟨hy.1.trans hz.1, hz.2.trans hxb⟩ hzc
  · symm
    apply CantorFunction.Gamma_eq_of_no_C_between hxy
    apply disjoint_left.mpr
    intro z hz hzc
    exact hab ⟨hax.trans hz.1, hz.2.trans hy.2⟩ hzc

lemma hasDerivAt_zero_off_C {x : ℝ} (hx : x ∉ C) : HasDerivAt Γ 0 x := by
  obtain ⟨a, b, hx, hconst⟩ := Gamma_locally_constant hx
  apply (hasDerivAt_const x (Γ x)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact hconst hy

theorem derivative_zero : Specs.D11.Ch12.SingularContinuousCounterexample.derivative_zero := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp CantorSet.C_volume_zero] with x hx
  exact hasDerivAt_zero_off_C hx

lemma deriv_ae_zero : deriv Γ =ᵐ[volume] (fun _ => (0 : ℝ)) := by
  filter_upwards [derivative_zero] with x hx
  exact hx.deriv

lemma integral_deriv_zero (a b : ℝ) : (∫ x in a..b, deriv Γ x) = 0 := by
  calc
    (∫ x in a..b, deriv Γ x) = ∫ x in a..b, (0 : ℝ) :=
      intervalIntegral.integral_congr_ae (deriv_ae_zero.mono fun _ hx _ => hx)
    _ = 0 := by simp

theorem strict_derivative_inequality :
    Specs.D11.Ch12.SingularContinuousCounterexample.strict_derivative_inequality := by
  refine ⟨?_, integral_deriv_zero 0 1, ?_⟩
  · have heq : (fun _ : ℝ => (0 : ℝ)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] deriv Γ :=
      ae_restrict_of_ae deriv_ae_zero.symm
    exact IntegrableOn.congr_fun_ae (g := deriv Γ) integrableOn_zero heq
  · rw [integral_deriv_zero, CantorFunction.endpoints.1, CantorFunction.endpoints.2]
    norm_num

theorem not_absolutely_continuous :
    Specs.D11.Ch12.SingularContinuousCounterexample.not_absolutely_continuous := by
  intro hAC
  have h := ((AcFtc.ftc_real Γ (by norm_num : (0 : ℝ) < 1)).2.1.mp hAC).2.2
    1 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  change Γ 1 = Γ 0 + ∫ x in (0 : ℝ)..1, deriv Γ x at h
  rw [CantorFunction.endpoints.1, CantorFunction.endpoints.2, integral_deriv_zero] at h
  norm_num at h

/-- The positive Borel Stieltjes measure of the same normalized extension. -/
def cantorStieltjes : StieltjesFunction ℝ :=
  ⟨extension, by
      rw [extension_eq_Gamma]
      exact CantorFunction.monotone,
    fun x => extension_nbv_continuous.2.continuousAt.continuousWithinAt⟩

lemma extension_tendsto_atBot : Tendsto extension atBot (𝓝 0) :=
  extension_nbv_continuous.1.2.2

lemma extension_tendsto_atTop : Tendsto extension atTop (𝓝 1) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact ((extension_properties.2.2.2.2) x hx).symm

lemma measure_probability : IsProbabilityMeasure cantorStieltjes.measure :=
  cantorStieltjes.isProbabilityMeasure extension_tendsto_atBot extension_tendsto_atTop

lemma measure_noAtoms : NullSingletonClass cantorStieltjes.measure := by
  constructor
  intro x
  rw [cantorStieltjes.measure_singleton]
  have hleft : Function.leftLim cantorStieltjes x = extension x :=
    extension_nbv_continuous.2.continuousAt.continuousWithinAt.leftLim_eq
  simp only [hleft]
  simp [cantorStieltjes]

lemma measure_off_C : cantorStieltjes.measure Cᶜ = 0 := by
  have hs : cantorStieltjes.measure.support ⊆ C := by
    intro x hx
    by_contra hxc
    obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (isClosed_cantorSet.isOpen_compl.mem_nhds hxc)
    have hxI : x ∈ Ioo a b := ⟨hax, hxb⟩
    have hz : cantorStieltjes.measure (Ioo a b) = 0 := by
      have heq : Γ a = Γ b := by
        apply CantorFunction.Gamma_eq_of_no_C_between (hxI.1.trans hxI.2).le
        apply disjoint_left.mpr
        intro z hz hzc
        exact hab hz hzc
      rw [cantorStieltjes.measure_Ioo]
      have hleft : Function.leftLim cantorStieltjes b = extension b :=
        extension_nbv_continuous.2.continuousAt.continuousWithinAt.leftLim_eq
      rw [hleft]
      change ENNReal.ofReal (extension b - extension a) = 0
      rw [extension_eq_Gamma, ← heq, sub_self, ENNReal.ofReal_zero]
    exact (Measure.notMem_support_iff_exists.mpr
      ⟨Ioo a b, Ioo_mem_nhds hxI.1 hxI.2, hz⟩) hx
  exact measure_mono_null (compl_subset_compl.mpr hs) Measure.measure_compl_support

theorem stieltjes_probability :
    Specs.D11.Ch12.SingularContinuousCounterexample.stieltjes_probability := by
  have := measure_probability
  refine ⟨cantorStieltjes.measure, measure_probability, ?_, measure_noAtoms,
    measure_off_C, CantorSet.C_volume_zero, ?_, ?_, ?_⟩
  · exact MeasureTheory.IsProbabilityMeasure.ne_zero _
  · refine ⟨Cᶜ, CantorSet.C_borel.compl, measure_off_C, ?_⟩
    rw [compl_compl]
    exact CantorSet.C_volume_zero
  · exact cantorStieltjes.measure_Ioc
  · intro x
    simpa only [cantorStieltjes, sub_zero] using
      cantorStieltjes.measure_Iic extension_tendsto_atBot x

end D11.Ch12.SingularContinuousCounterexample
