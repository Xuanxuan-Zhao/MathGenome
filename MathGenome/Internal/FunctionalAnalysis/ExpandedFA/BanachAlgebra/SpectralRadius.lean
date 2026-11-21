import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.SpectralRadius
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NonemptySpectrum
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Analytic.Uniqueness

/-!
Gelfand's formula for the manuscript's real spectral radius.

The hard inequality is proved using Cauchy coefficients of (1-z•a)⁻¹ on
all disks of radius smaller than the inverse spectral radius. Uniqueness
identifies these with the geometric-series coefficients a^n; Cauchy-Hadamard
then bounds the limsup of the roots. This is the disk-at-zero version of the
manuscript's exterior-resolvent argument. The remaining inequality is the
native spectral-mapping/norm bound, which also bounds every positive root.

Compactness identifies the real spectral maximum with the native extended-real
radius. No division by a power norm or by the real spectral radius is used.
-/

namespace ExpandedFA.BanachAlgebra

open Filter Set
open scoped Topology NNReal ENNReal
open Specs.ExpandedFA.BanachAlgebra.SpectralRadius

universe u

theorem algebraSpectralRadius_maximum : RadiusMaximum.{u} := by
  intro A _ _ hA a
  obtain ⟨hne, hc, hdisk⟩ := algebra_spectrum_properties A hA a
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn hne continuous_norm.continuousOn
  have hb : BddAbove ((fun z : ℂ => ‖z‖) '' algebraSpectrum ℂ A a) :=
    hc.bddAbove_image continuous_norm.continuousOn
  have heq : algebraSpectralRadius ℂ A a = ‖z‖ := by
    apply le_antisymm
    · exact csSup_le (hne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact hmax hw)
    · exact le_csSup hb ⟨z, hz, rfl⟩
  refine ⟨⟨z, hz, heq.symm⟩, ?_, ?_, ?_⟩
  · intro w hw
    exact le_csSup hb ⟨w, hw, rfl⟩
  · change 0 ≤ algebraSpectralRadius ℂ A a
    rw [heq]
    exact norm_nonneg z
  · change algebraSpectralRadius ℂ A a ≤ ‖a‖
    rw [heq]
    exact hdisk hz

/-- The manuscript's real supremum and Mathlib's extended-real radius agree. -/
theorem algebraSpectralRadius_eq_native : RadiusNativeIdentification.{u} := by
  intro A _ _ hA a
  obtain ⟨⟨z, hz, hzr⟩, hbound, _, _⟩ := algebraSpectralRadius_maximum A hA a
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · rw [← hzr]
    exact le_iSup₂_of_le z hz (by simp)
  · apply iSup₂_le
    intro w hw
    simpa only [ofReal_norm, enorm] using ENNReal.ofReal_le_ofReal (hbound w hw)

/-- Cauchy coefficients of the inverse function give the difficult root estimate.
This proof follows the analytic argument in Mathlib's Gelfand formula, retaining
its Cauchy power-series construction and coefficient uniqueness explicitly. -/
lemma limsup_roots_le_spectralRadius (A : Type u) [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    limsup (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop ≤
      spectralRadius ℂ a := by
  refine ENNReal.inv_le_inv.mp (ENNReal.le_of_forall_pos_nnreal_lt fun r r_pos r_lt => ?_)
  simp_rw [ENNReal.inv_limsup, ← one_div]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius by
    convert h
    simp only [p, p.radius_eq_liminf, ← norm_toNNReal,
      ContinuousMultilinearMap.norm_mkPiRing]
    congr
    ext n
    rw [norm_toNNReal, ENNReal.coe_rpow_def ‖a ^ n‖₊ (1 / n : ℝ), ite_eq_right]
    exact fun ha => (lt_self_iff_false _).mp
      (ha.2.trans_le (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ)))
  -- Holomorphy is proved from invertibility at each point in the disk.
  have hcauchy := (spectrum.differentiableOn_inverse_one_sub_smul r_lt).hasFPowerSeriesOnBall r_pos
  -- Cauchy's series has radius at least r. Its coefficients coincide with the
  -- known local geometric series, so the latter also has radius at least r.
  exact ((spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).exchange_radius hcauchy).r_le

theorem algebraSpectralRadius_root_limit : RootLimit.{u} := by
  intro A _ _ hA a
  let : CompleteSpace A := hA.1
  have hr := algebraSpectralRadius_eq_native A hA a
  have hr0 := (algebraSpectralRadius_maximum A hA a).2.2.1
  have hfin : spectralRadius ℂ a ≠ ⊤ := by rw [← hr]; exact ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop
      (𝓝 (spectralRadius ℂ a)) :=
    tendsto_of_le_liminf_of_limsup_le
      (spectrum.spectralRadius_le_liminf_pow_nnnorm_pow_one_div ℂ a)
      (limsup_roots_le_spectralRadius A a)
  have ht := (ENNReal.tendsto_toReal hfin).comp hlim
  have ht' : Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (algebraSpectralRadius ℂ A a)) := by
    simpa only [← hr, ENNReal.toReal_ofReal hr0, Function.comp_def,
      ← ENNReal.toReal_rpow, toReal_coe_nnnorm] using ht
  exact ht'.comp (tendsto_add_atTop_nat 1)

/-- Every positive root bounds the radius, including when the power is zero. -/
lemma algebraSpectralRadius_le_root (A : Type u) [NormedRing A]
    [NormedAlgebra ℂ A] (hA : IsUnitalBanachAlgebra A) (a : A) (n : ℕ) :
    algebraSpectralRadius ℂ A a ≤ ‖a ^ (n + 1)‖ ^ (1 / ((n + 1 : ℕ) : ℝ)) := by
  let : CompleteSpace A := hA.1
  let : NormOneClass A := hA.2.2
  have hn := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ a n
  simp only [nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow, mul_one] at hn
  have hr := algebraSpectralRadius_eq_native A hA a
  have hr0 := (algebraSpectralRadius_maximum A hA a).2.2.1
  have hfin : ((‖a ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / ((n + 1 : ℕ) : ℝ))) ≠ ⊤ := by
    rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity)]
    exact ENNReal.coe_ne_top
  simp only [Nat.cast_add, Nat.cast_one] at hfin ⊢
  have hreal := ENNReal.toReal_mono hfin hn
  simpa only [← hr, ENNReal.toReal_ofReal hr0, ← ENNReal.toReal_rpow,
    toReal_coe_nnnorm] using hreal

theorem algebraSpectralRadius_root_infimum : RootInfimum.{u} := by
  intro A _ _ hA a
  let f : ℕ → ℝ := fun n => ‖a ^ (n + 1)‖ ^ (1 / ((n + 1 : ℕ) : ℝ))
  have hb : BddBelow (range f) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact Real.rpow_nonneg (norm_nonneg _) _⟩
  apply le_antisymm
  · exact ge_of_tendsto (algebraSpectralRadius_root_limit A hA a)
      (Filter.Eventually.of_forall fun n => csInf_le hb (mem_range_self n))
  · exact le_csInf (range_nonempty f) (by
      rintro _ ⟨n, rfl⟩
      exact algebraSpectralRadius_le_root A hA a n)

end ExpandedFA.BanachAlgebra

/- Mathlib proof attribution
Adapted portion near line 62:
The Cauchy estimate and power-series radius argument in the Gelfand
spectral-radius formula.

Upstream: Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean (around line 101)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
