import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.Typewriter
import MathGenome.Internal.RealAnalysis.D11.Ch07.NormToMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology ENNReal
/-! Exact dyadic indexing, finite-p convergence, and failure at every point.
The completed subtype measure and the representative convergence predicates
are the independent canonical objects in the Specs. -/

noncomputable section
namespace D11.Ch07.Typewriter
open Specs.D11.Ch07.Typewriter
open D11.Ch07.ConvergenceDefinitions

def sequence : Specs.D11.Ch07.Typewriter.sequence_type :=
  Specs.D11.Ch07.Typewriter.sequence_value

theorem indexing : Specs.D11.Ch07.Typewriter.indexing := by
  intro k j hj
  have hpos : 0 < 2^k := pow_pos (by decide) _
  have hlog : Nat.log 2 (2^k+j) = k :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
  simp [Specs.D11.Ch07.Typewriter.sequence_value, hlog]

private theorem measurable_cell (k j : ℕ) : MeasurableSet (cell k j) := by
  exact (measurableSet_Ico.preimage measurable_subtype_coe).nullMeasurableSet

theorem measurable_sequence : Specs.D11.Ch07.Typewriter.measurable_sequence := by
  intro n
  by_cases hn : n = 0
  · simp only [Specs.D11.Ch07.Typewriter.sequence_value, ite_eq_left hn]
    exact measurable_const
  · simpa [Specs.D11.Ch07.Typewriter.sequence_value, hn] using
      measurable_const.indicator (measurable_cell (Nat.log 2 n) (n-2^(Nat.log 2 n)))

private theorem measure_cell (k j : ℕ) (hj : j < 2^k) :
    μ (cell k j) = ENNReal.ofReal ((2 : ℝ)^k)⁻¹ := by
  have hd : 0 < (2 : ℝ)^k := pow_pos (by norm_num) _
  have ha : 0 ≤ (j : ℝ) / (2 : ℝ)^k := div_nonneg (Nat.cast_nonneg _) hd.le
  have hb : ((j : ℝ)+1) / (2 : ℝ)^k ≤ 1 := by
    apply (div_le_one hd).mpr
    exact_mod_cast (Nat.succ_le_of_lt hj)
  change intervalMeasure {x : Interval | x.val ∈
    Ico ((j : ℝ)/(2 : ℝ)^k) (((j : ℝ)+1)/(2 : ℝ)^k)} = _
  rw [intervalMeasure, comap_subtype_coe_apply measurableSet_Ico]
  have himage : Subtype.val '' {x : Interval | x.val ∈
      Ico ((j : ℝ)/(2 : ℝ)^k) (((j : ℝ)+1)/(2 : ℝ)^k)} =
      Ico ((j : ℝ)/(2 : ℝ)^k) (((j : ℝ)+1)/(2 : ℝ)^k) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, ha.trans hx.1, hx.2.trans_le hb⟩, hx, rfl⟩
  rw [himage, Real.volume_Ico]
  have hlen : ((j : ℝ)+1)/(2 : ℝ)^k - (j : ℝ)/(2 : ℝ)^k = ((2 : ℝ)^k)⁻¹ := by
    field_simp
    ring
  rw [hlen, ENNReal.ofReal_inv_of_pos hd]

theorem block_power_integral : Specs.D11.Ch07.Typewriter.block_power_integral := by
  intro p hp k j hj
  change powerIntegral μ p (Specs.D11.Ch07.Typewriter.sequence_value (2^k+j)) = _
  rw [indexing k j hj, powerIntegral_eq_lintegral]
  have hpow : (fun x : Domain => ENNReal.ofReal
      (‖(cell k j).indicator (fun _ => (1 : ℝ)) x‖ ^ p)) =
      (cell k j).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ cell k j
    · simp [hx]
    · simp [hx, Real.zero_rpow (show p ≠ 0 by linarith)]
  rw [hpow]
  exact (lintegral_indicator_const (μ := μ) (measurable_cell k j) 1).trans
    (by simpa using measure_cell k j hj)

private theorem decoded_power_integral (p : ℝ) (hp : 1 ≤ p) (n : ℕ) (hn : n ≠ 0) :
    powerIntegral μ p (Specs.D11.Ch07.Typewriter.sequence_value n) =
      ((2 : ℝ≥0∞)⁻¹)^(Nat.log 2 n) := by
  have hlo := Nat.pow_log_le_self 2 hn
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hj : n-2^(Nat.log 2 n) < 2^(Nat.log 2 n) := by
    rw [pow_succ] at hhi
    omega
  have hb := block_power_integral p hp (Nat.log 2 n) (n-2^(Nat.log 2 n)) hj
  rw [Nat.add_sub_of_le hlo] at hb
  change powerIntegral μ p (Specs.D11.Ch07.Typewriter.sequence_value n) = _ at hb
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)] at hb
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] at hb
  simpa only [ENNReal.ofReal_ofNat, ENNReal.inv_pow] using hb

private theorem zero_power_integral (p : ℝ) (hp : 1 ≤ p) :
    powerIntegral μ p (fun _ : Domain => (0 : ℝ)) = 0 := by
  rw [powerIntegral_eq_lintegral]
  simp [Real.zero_rpow (show p ≠ 0 by linarith)]

theorem lp_convergence : Specs.D11.Ch07.Typewriter.lp_convergence := by
  intro p hp
  change lpConverges μ p Specs.D11.Ch07.Typewriter.sequence_value (fun _ => (0 : ℝ))
  refine ⟨hp, ⟨measurable_const, ?_⟩, ?_, ?_⟩
  · rw [zero_power_integral p hp]
    exact ENNReal.zero_lt_top
  · intro n
    refine ⟨measurable_sequence n, ?_⟩
    by_cases hn : n = 0
    · subst n
      change powerIntegral μ p (fun _ : Domain => (0 : ℝ)) < ∞
      rw [zero_power_integral p hp]
      exact ENNReal.zero_lt_top
    · rw [decoded_power_integral p hp n hn]
      finiteness
  · simp only [sub_zero]
    have hlog : Tendsto (Nat.log 2) atTop atTop := by
      apply tendsto_atTop_atTop.mpr
      intro K
      exact ⟨2^K, fun n hn => Nat.le_log_of_pow_le (by decide) hn⟩
    have ht := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (2 : ℝ≥0∞)⁻¹ < 1 by norm_num)).comp hlog
    apply ht.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (decoded_power_integral p hp n hn).symm

theorem measure_convergence : Specs.D11.Ch07.Typewriter.measure_convergence := by
  exact D11.Ch07.NormToMeasure.lp_to_measure μ
    Specs.D11.Ch07.Typewriter.sequence_value (fun _ => (0 : ℝ)) 1 (lp_convergence 1 le_rfl)

private theorem coordinate_bounds (x : Domain) :
    0 ≤ coordinate x ∧ coordinate x < 1 :=
  (show Interval from x).property

private theorem cell_iff_floor (k j : ℕ) (x : Domain) :
    x ∈ cell k j ↔ ⌊coordinate x * (2 : ℝ)^k⌋₊ = j := by
  have hd : 0 < (2 : ℝ)^k := pow_pos (by norm_num) _
  rw [Nat.floor_eq_iff (mul_nonneg (coordinate_bounds x).1 hd.le)]
  exact ⟨fun h => ⟨(div_le_iff₀ hd).mp h.1, (lt_div_iff₀ hd).mp h.2⟩,
    fun h => ⟨(div_le_iff₀ hd).mpr h.1, (lt_div_iff₀ hd).mpr h.2⟩⟩

private theorem floor_lt_block (k : ℕ) (x : Domain) :
    ⌊coordinate x * (2 : ℝ)^k⌋₊ < 2^k := by
  have hd : 0 < (2 : ℝ)^k := pow_pos (by norm_num) _
  apply (Nat.floor_lt (mul_nonneg (coordinate_bounds x).1 hd.le)).mpr
  push_cast
  nlinarith [(coordinate_bounds x).2]

theorem infinitely_one : Specs.D11.Ch07.Typewriter.infinitely_one := by
  intro x N
  let j := ⌊coordinate x * (2 : ℝ)^N⌋₊
  refine ⟨2^N+j, ?_, ?_⟩
  · have h := Nat.lt_pow_self (n := N) (by decide : 1 < 2)
    omega
  · rw [indexing N j (floor_lt_block N x)]
    exact Set.indicator_of_mem ((cell_iff_floor N j x).mpr rfl) _

theorem infinitely_zero : Specs.D11.Ch07.Typewriter.infinitely_zero := by
  intro x N
  let k := N+1
  let j := ⌊coordinate x * (2 : ℝ)^k⌋₊
  have htwo : 2 ≤ 2^k := by
    have h : 2^1 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
    simpa using h
  obtain ⟨i, hi, hne⟩ : ∃ i : ℕ, i < 2^k ∧ i ≠ j := by
    by_cases hj : j = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, Ne.symm hj⟩
  refine ⟨2^k+i, ?_, ?_⟩
  · have h := Nat.lt_pow_self (n := k) (by decide : 1 < 2)
    dsimp [k] at h ⊢
    omega
  · rw [indexing k i hi]
    apply Set.indicator_of_notMem
    intro hx
    exact hne ((cell_iff_floor k i x).mp hx).symm

theorem nowhere_convergent : Specs.D11.Ch07.Typewriter.nowhere_convergent := by
  intro x ⟨c, hc⟩
  have h1 : c = 1 := tendsto_nhds_unique_of_frequently_eq hc
    tendsto_const_nhds (frequently_atTop.mpr (infinitely_one x))
  have h0 : c = 0 := tendsto_nhds_unique_of_frequently_eq hc
    tendsto_const_nhds (frequently_atTop.mpr (infinitely_zero x))
  linarith

end D11.Ch07.Typewriter
