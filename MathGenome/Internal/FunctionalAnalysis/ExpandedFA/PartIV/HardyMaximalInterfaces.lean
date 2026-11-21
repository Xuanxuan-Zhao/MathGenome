import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyMaximalInterfaces
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace ExpandedFA.PartIV.HardyMaximal
open ExpandedFA.Fourier HardyMaximalSpec

abbrev L1 : Spec.L1Type := @HardyMaximalSpec.L1
abbrev Hardy : Spec.HardyType := @HardyMaximalSpec.Hardy
abbrev coordinatePartial : Spec.coordinatePartialType := @HardyMaximalSpec.coordinatePartial
abbrev IsFixedKernel : Spec.IsFixedKernelType := @HardyMaximalSpec.IsFixedKernel
abbrev dilate : Spec.dilateType := @HardyMaximalSpec.dilate
abbrev convolve : Spec.convolveType := @HardyMaximalSpec.convolve
abbrev radial : Spec.radialType := @HardyMaximalSpec.radial
abbrev weightedNorm : Spec.weightedNormType := @HardyMaximalSpec.weightedNorm
abbrev peetreExponent : Spec.peetreExponentType := @HardyMaximalSpec.peetreExponent
abbrev averagingExponent : Spec.averagingExponentType := @HardyMaximalSpec.averagingExponent
abbrev AdmissibleOrder : Spec.AdmissibleOrderType := @HardyMaximalSpec.AdmissibleOrder
abbrev IsTest : Spec.IsTestType := @HardyMaximalSpec.IsTest
abbrev Tests : Spec.TestsType := @HardyMaximalSpec.Tests
abbrev grand : Spec.grandType := @HardyMaximalSpec.grand
abbrev peetre : Spec.peetreType := @HardyMaximalSpec.peetre

theorem kernel_bounded : Spec.KernelBounded := by
  intro 𝕜 _ d φ hφ
  obtain ⟨C, hC, hb⟩ := hφ.2.2 0 (Fin.elim0)
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := hb x
  simp only [HardyMaximalSpec.coordinatePartial, iteratedFDeriv_zero_apply] at h
  have hpow : 1 ≤ (1 + ‖x‖) ^ (d + 1 + 0) := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg x))
  exact h.trans (div_le_self hC hpow)

theorem test_bounded : Spec.TestBounded := by
  intro 𝕜 _ d N ψ x
  simpa only [HardyMaximalSpec.coordinatePartial, iteratedFDeriv_zero_apply] using
    ψ.property.2.2 0 (Nat.zero_le N) Fin.elim0 x

theorem parameters : Spec.Parameters := by
  intro d
  have h : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  dsimp [HardyMaximalSpec.averagingExponent, HardyMaximalSpec.peetreExponent,
    HardyMaximalSpec.AdmissibleOrder]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ⟨2 * (d + 1) + d + 5, by omega⟩⟩ <;>
    (first | positivity | (field_simp; nlinarith))

theorem scaled_convolution_continuous : Spec.ScaledConvolutionContinuous := by
  intro 𝕜 _ d u f hu hb hf t
  have hd : Continuous (dilate t u) := by
    unfold dilate HardyMaximalSpec.dilate
    fun_prop
  have hbd : BddAbove (Set.range fun x => ‖dilate t u x‖) := by
    obtain ⟨C, hC⟩ := hb
    refine ⟨‖(t ^ d)⁻¹‖ * C, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [dilate, HardyMaximalSpec.dilate, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (Set.mem_range_self _)) (norm_nonneg _)
  exact hbd.continuous_convolution_left_of_integrable _ hd hf

theorem radial_regularity : Spec.RadialRegularity := by
  intro 𝕜 _ d φ f hφ hf
  have h : LowerSemicontinuous (radial φ f) := by
    apply lowerSemicontinuous_iSup
    intro t
    exact (ENNReal.continuous_ofReal.comp
      (scaled_convolution_continuous φ f hφ.1.continuous (kernel_bounded φ hφ) hf t).norm).lowerSemicontinuous
  exact ⟨h, h.measurable⟩

theorem grand_regularity : Spec.GrandRegularity := by
  intro 𝕜 _ d N f hf
  have h : LowerSemicontinuous (grand N f) := by
    apply lowerSemicontinuous_iSup
    intro t
    apply lowerSemicontinuous_iSup
    intro ψ
    have hb : BddAbove (Set.range fun x => ‖ψ.val x‖) :=
      ⟨1, by rintro _ ⟨x, rfl⟩; exact test_bounded ψ x⟩
    exact (ENNReal.continuous_ofReal.comp
      (scaled_convolution_continuous ψ.val f ψ.property.1.continuous hb hf t).norm).lowerSemicontinuous
  exact ⟨h, h.measurable⟩

theorem peetre_regularity : Spec.PeetreRegularity := by
  intro 𝕜 _ d η f
  have h : LowerSemicontinuous (peetre η f) := by
    apply lowerSemicontinuous_iSup
    intro j
    apply lowerSemicontinuous_iSup
    intro y
    apply Continuous.lowerSemicontinuous
    apply ENNReal.continuous_ofReal.comp
    apply Continuous.div continuous_const
    · fun_prop
    · intro x
      have hz : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
      positivity
  exact ⟨h, h.measurable⟩

end ExpandedFA.PartIV.HardyMaximal
