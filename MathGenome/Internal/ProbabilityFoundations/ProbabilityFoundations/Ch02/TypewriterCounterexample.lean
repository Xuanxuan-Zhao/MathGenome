import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.TypewriterCounterexample
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.ConvergenceComparisons
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ProbabilityFoundations.Ch02.TypewriterCounterexample
open Specs.ProbabilityFoundations.Ch02.TypewriterCounterexample

lemma level_lower (n : ℕ) : 2 ^ level n ≤ n + 1 :=
  Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)

lemma level_upper (n : ℕ) : n + 1 < 2 ^ (level n + 1) :=
  Nat.lt_pow_succ_log_self (by decide) (n + 1)

lemma decode_index (m j : ℕ) (hj : j < 2 ^ m) :
    level (index m j) = m ∧ slot (index m j) = j := by
  have hp : 0 < 2 ^ m := pow_pos (by decide) _
  have hn : index m j + 1 = 2 ^ m + j := by unfold index; omega
  have hl : level (index m j) = m := by
    unfold level
    rw [hn]
    apply Nat.log_eq_of_pow_le_of_lt_pow (by omega)
    rw [pow_succ]
    omega
  exact ⟨hl, by simp [slot, hl, hn]⟩

lemma level_tendsto : Tendsto level atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (2 ^ m)] with n hn
  exact Nat.le_log_of_pow_le (by decide) (by omega)

theorem enumeration : enumerationType := by
  refine ⟨?_, decode_index, level_tendsto⟩
  intro n
  have hl := level_lower n
  have hu := level_upper n
  rw [pow_succ] at hu
  constructor
  · unfold slot; omega
  · unfold index slot; omega

lemma dyadic_measurable (m j : ℕ) : MeasurableSet (dyadic m j) :=
  measurableSet_Ico.preimage measurable_subtype_coe

lemma typewriter_measurable (n : ℕ) : Measurable (typewriter n) :=
  measurable_const.indicator (dyadic_measurable _ _)

lemma dyadic_subset (m j : ℕ) (hj : j < 2 ^ m) :
    Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m) ⊆ Ico (0 : ℝ) 1 := by
  have hp : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  have hj' : (j : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast (Nat.succ_le_iff.mpr hj)
  intro x hx
  exact ⟨(div_nonneg (Nat.cast_nonneg j) hp.le).trans hx.1,
    hx.2.trans_le ((div_le_one hp).2 hj')⟩

lemma dyadic_measure (m j : ℕ) (hj : j < 2 ^ m) :
    probability (dyadic m j) = ENNReal.ofReal ((2 : ℝ) ^ m)⁻¹ := by
  rw [probability, comap_subtype_coe_apply measurableSet_Ico]
  have himage : Subtype.val '' dyadic m j =
      Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, dyadic_subset m j hj hx⟩, hx, rfl⟩
  rw [himage, Real.volume_Ico]
  congr 1
  ring

lemma dyadic_mem_iff (m j : ℕ) (x : Sample) :
    x ∈ dyadic m j ↔ (j : ℝ) ≤ (x : ℝ) * 2 ^ m ∧
      (x : ℝ) * 2 ^ m < (j : ℝ) + 1 := by
  have hp : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  exact and_congr (div_le_iff₀ hp) (lt_div_iff₀ hp)

theorem partition : partitionType := by
  intro m x
  have hp : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  have hx : 0 ≤ (x : ℝ) * 2 ^ m := mul_nonneg x.property.1 hp.le
  let j := ⌊(x : ℝ) * 2 ^ m⌋₊
  have hj : j < 2 ^ m := by
    apply (Nat.floor_lt hx).2
    push_cast
    nlinarith [x.property.2]
  refine ⟨⟨j, hj⟩, (dyadic_mem_iff m j x).2 ⟨Nat.floor_le hx,
    Nat.lt_floor_add_one _⟩, ?_⟩
  intro k hk
  apply Fin.ext
  exact ((Nat.floor_eq_iff hx).2 ((dyadic_mem_iff m k x).1 hk)).symm

lemma typewriter_memLp (n : ℕ) (p : ℝ≥0∞) : MemLp (typewriter n) p probability := by
  exact memLp_indicator_const p (dyadic_measurable _ _).nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

lemma indicator_rpow (n : ℕ) (p : ℝ) (hp : 0 < p) :
    (fun x => |typewriter n x| ^ p) = typewriter n := by
  funext x
  by_cases hx : x ∈ dyadic (level n) (slot n)
  · simp [typewriter, indicator_of_mem hx]
  · simp [typewriter, indicator_of_notMem hx, Real.zero_rpow hp.ne']

theorem moment : momentType := by
  intro p hp n
  rw [indicator_rpow n p hp]
  unfold typewriter
  rw [integral_indicator_const 1 (dyadic_measurable _ _)]
  simp only [Measure.real, dyadic_measure _ _ (enumeration.1 n).1,
    smul_eq_mul, mul_one]
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma width_tendsto :
    Tendsto (fun n => ((2 : ℝ) ^ level n)⁻¹) atTop (𝓝 0) := by
  exact (tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).comp level_tendsto

theorem lp_convergence : lpConvergenceType := by
  intro p hp
  refine ⟨fun n => ⟨typewriter_measurable n, typewriter_memLp n _⟩, MemLp.zero, ?_⟩
  simpa only [sub_zero, moment p hp] using width_tendsto

theorem probability_convergence : probabilityConvergenceType := by
  exact ProbabilityFoundations.Ch02.lp_implies_probability probability typewriter (fun _ => 0) 1
    typewriter_measurable measurable_const (by norm_num)
    (fun n => typewriter_memLp n _) MemLp.zero (lp_convergence 1 (by norm_num)).2.2

lemma typewriter_index (m j : ℕ) (hj : j < 2 ^ m) :
    typewriter (index m j) = (dyadic m j).indicator (fun _ => 1) := by
  simp only [typewriter, (decode_index m j hj).1, (decode_index m j hj).2]

lemma index_ge (m j : ℕ) : m ≤ index m j := by
  have := m.lt_two_pow_self
  unfold index
  omega

theorem oscillation : oscillationType := by
  intro x
  constructor
  · intro N
    obtain ⟨j, hj, _⟩ := partition N x
    refine ⟨index N j, index_ge N j, ?_⟩
    rw [typewriter_index N j j.isLt, indicator_of_mem hj]
  · intro N
    let m := N + 1
    obtain ⟨j, hj, huniq⟩ := partition m x
    have htwo : 1 < 2 ^ m := Nat.one_lt_pow (by dsimp [m]; omega) (by decide)
    obtain ⟨k, hk⟩ : ∃ k : Fin (2 ^ m), k ≠ j := by
      by_cases hj0 : j.val = 0
      · refine ⟨⟨1, htwo⟩, ?_⟩
        intro heq
        have := congrArg Fin.val heq
        simp only at this
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro heq
        exact hj0 (congrArg Fin.val heq).symm
    have hmiss : x ∉ dyadic m k := fun h => hk (huniq k h)
    refine ⟨index m k, (Nat.le_succ N).trans (index_ge m k), ?_⟩
    rw [typewriter_index m k k.isLt, indicator_of_notMem hmiss]

theorem nowhere_convergent : nowhereConvergentType := by
  intro x a hconv
  have h1 : ∃ᶠ n in atTop, typewriter n x = 1 :=
    frequently_atTop.2 (oscillation x).1
  have h0 : ∃ᶠ n in atTop, typewriter n x = 0 :=
    frequently_atTop.2 (oscillation x).2
  have ha1 : a = 1 := tendsto_nhds_unique_of_frequently_eq hconv tendsto_const_nhds h1
  have ha0 : a = 0 := tendsto_nhds_unique_of_frequently_eq hconv tendsto_const_nhds h0
  linarith

theorem not_almost_sure : notAlmostSureType := by
  have hnot (Y : Sample → ℝ) :
      ¬ ∀ᵐ x ∂probability, Tendsto (fun n => typewriter n x) atTop (𝓝 (Y x)) := by
    intro h
    have hf : ∀ᵐ x ∂probability, False := h.mono (fun x hx => nowhere_convergent x (Y x) hx)
    exact (IsProbabilityMeasure.ne_zero probability) (by simpa using hf)
  refine ⟨hnot (fun _ => 0), hnot, ?_⟩
  have he : {x : Sample | ∃ a : ℝ, Tendsto (fun n => typewriter n x) atTop (𝓝 a)} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
    exact nowhere_convergent x
  rw [he, measure_empty]

end ProbabilityFoundations.Ch02.TypewriterCounterexample
