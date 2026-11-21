import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.ReciprocalFourth
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.QuadraticFourier
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Parseval
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
namespace SingleVariableAnalysis
open Set Riemann
open scoped BigOperators
open Specs.SingleVariableAnalysis.Ch19.QuadraticFourier
open Specs.SingleVariableAnalysis.Ch19.ReciprocalFourth

namespace ReciprocalFourth

lemma norm_integral_value
    (h : RealIntegrable (fun x => |quadraticValue x| ^ 2) (-Real.pi) Real.pi) :
    realIntegral _ h = 2 * Real.pi ^ 5 / 5 := by
  have hv := real_ftc_second (fun t : ℝ => t^5/5)
    (fun x => |quadraticValue x| ^ 2) (-Real.pi) Real.pi
    (by linarith [Real.pi_pos]) ((continuous_id.pow 5).div_const 5).continuousOn
    (fun x hx => by
      rw [quadratic_fourier_extension.2.2 (Ioo_subset_Icc_self hx), sq_abs]
      convert (ElementaryPrimitives.natural_power_primitive 4).1 x (mem_univ x) using 1 <;>
        norm_num <;> ring) h
  calc
    realIntegral _ h = Real.pi^5/5 - (-Real.pi)^5/5 := hv
    _ = _ := by ring

lemma norm_integrable :
    RealIntegrable (fun x => |quadraticValue x| ^ 2) (-Real.pi) Real.pi :=
  Fourier.realIntegrable_of_continuousOn (by linarith [Real.pi_pos])
    (quadratic_fourier_extension.1.abs.pow 2).continuousOn

lemma normalized_norm_value
    (h : RealIntegrable (fun x => |quadraticValue x| ^ 2) (-Real.pi) Real.pi) :
    (1 / (2 * Real.pi)) * realIntegral _ h = Real.pi ^ 4 / 5 := by
  rw [norm_integral_value h]
  field_simp

lemma signed_coefficient_square (n : ℕ) (a : ℝ) :
    ‖((4 * (-1 : ℝ)^n / a^2 : ℝ) : ℂ) / 2‖^2 = 4 / a^4 := by
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Complex.norm_ofNat, div_pow, sq_abs, mul_pow]
  rw [hs]
  ring

lemma zero_square
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights
      (fun x => (quadraticValue x : ℂ))) :
    ‖fourierCoeff (fun x => (quadraticValue x : ℂ)) 0 (h 0)‖^2 = Real.pi^4/9 := by
  obtain ⟨hf, ha, hb⟩ := quadratic_fourier_integrability
  have hc := (quadratic_fourier_coefficients hf.2 ha hb).1
  have hz : fourierCoeff (fun x => (quadraticValue x : ℂ)) 0 (h 0) =
      (Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.aZeroValue quadraticValue hf.2 : ℂ) / 2 :=
    fourierCoeff_zero_real quadraticValue hf h
  rw [hz]
  have he : (Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.aZeroValue quadraticValue hf.2 : ℂ) / 2 =
      ((Real.pi^2/3 : ℝ) : ℂ) := by
    exact_mod_cast hc
  rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

lemma positive_square
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights
      (fun x => (quadraticValue x : ℂ))) (k : ℕ) :
    ‖fourierCoeff (fun x => (quadraticValue x : ℂ)) ((k : ℤ)+1) (h _)‖^2 =
      4 * (1 / (((k+1 : ℕ) : ℝ)^4)) := by
  obtain ⟨hf, ha, hb⟩ := quadratic_fourier_integrability
  let n : ℕ+ := ⟨k+1, Nat.succ_pos k⟩
  have he := (quadratic_fourier_coefficients hf.2 ha hb).2 n
  have hc := fourierCoeff_positive_real quadraticValue hf h ha hb n
  change fourierCoeff (fun x => (quadraticValue x : ℂ)) ((k : ℤ)+1) (h _) = _ at hc
  rw [hc, he.1, he.2]
  simp only [Complex.ofReal_zero, mul_zero, sub_zero]
  rw [signed_coefficient_square]
  change 4 / (((k+1 : ℕ) : ℝ)^4) = _
  ring

lemma negative_square
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights
      (fun x => (quadraticValue x : ℂ))) (k : ℕ) :
    ‖fourierCoeff (fun x => (quadraticValue x : ℂ)) (-((k : ℤ)+1)) (h _)‖^2 =
      4 * (1 / (((k+1 : ℕ) : ℝ)^4)) := by
  obtain ⟨hf, ha, hb⟩ := quadratic_fourier_integrability
  let n : ℕ+ := ⟨k+1, Nat.succ_pos k⟩
  have he := (quadratic_fourier_coefficients hf.2 ha hb).2 n
  have hc := fourierCoeff_negative_real quadraticValue hf h ha hb n
  change fourierCoeff (fun x => (quadraticValue x : ℂ)) (-((k : ℤ)+1)) (h _) = _ at hc
  rw [hc, he.1, he.2]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [signed_coefficient_square]
  change 4 / (((k+1 : ℕ) : ℝ)^4) = _
  ring

lemma series_summable : Summable (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ)^4)) :=
  (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 4))

end ReciprocalFourth

/-- Evaluate the squared norm by the primitive x⁵/5 on the entire closed period. -/
theorem quadratic_fourier_norm_integral : normIntegral :=
  ⟨ReciprocalFourth.norm_integrable,
    ReciprocalFourth.norm_integral_value _, ReciprocalFourth.normalized_norm_value _⟩

/-- Continuous Parseval for the periodic quadratic, with both frequency halves combined. -/
theorem quadratic_fourier_parseval_fourth : parsevalIdentity := by
  obtain ⟨h, hs, hr, hsum, heq, hlim, hnorm⟩ := fourierParseval_real quadraticValue
    quadratic_fourier_extension.1 quadratic_fourier_extension.2.1
  let c : ℤ → ℝ := fun n => ‖fourierCoeff (fun x => (quadraticValue x : ℂ)) n (h n)‖^2
  have hpos : (fun k : ℕ => c ((k : ℤ)+1)) =
      (fun k : ℕ => 4 * (1 / (((k+1 : ℕ) : ℝ)^4))) :=
    funext (ReciprocalFourth.positive_square h)
  have hneg : (fun k : ℕ => c (-((k : ℤ)+1))) =
      (fun k : ℕ => 4 * (1 / (((k+1 : ℕ) : ℝ)^4))) :=
    funext (ReciprocalFourth.negative_square h)
  have hp : Summable (fun k : ℕ => c ((k : ℤ)+1)) := by
    rw [hpos]
    exact ReciprocalFourth.series_summable.mul_left 4
  have hn : Summable (fun k : ℕ => c (-((k : ℤ)+1))) := by
    rw [hneg]
    exact ReciprocalFourth.series_summable.mul_left 4
  have ht := tsum_of_add_one_of_neg_add_one hp hn
  have hz : c 0 = Real.pi^4/9 := ReciprocalFourth.zero_square h
  rw [hpos, hneg, tsum_mul_left, hz] at ht
  change (∑' n : ℤ, c n) = (1 / (2 * Real.pi)) * realIntegral _ hs at heq
  rw [ReciprocalFourth.normalized_norm_value hs] at heq
  dsimp [parsevalIdentity]
  linarith only [ht, heq]

/-- The ordinary positive fourth-power reciprocal series has sum π⁴/90. -/
theorem reciprocal_fourth_hasSum : reciprocalFourthSum := by
  have he := quadratic_fourier_parseval_fourth
  have hs := ReciprocalFourth.series_summable.hasSum
  have hv : (∑' k : ℕ, 1 / (((k+1 : ℕ) : ℝ)^4)) = Real.pi^4/90 := by
    dsimp [parsevalIdentity] at he
    linarith
  rw [hv] at hs
  exact hs

theorem reciprocal_fourth_tsum : reciprocalFourthTsum :=
  reciprocal_fourth_hasSum.tsum_eq

end SingleVariableAnalysis
