import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TotalVariation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter
open scoped Topology ENNReal Classical

universe u
namespace P207.Markov
noncomputable section

namespace TotalVariation
abbrev distance : TotalVariationSpec.totalVariationType.{u} := @totalVariation.{u}
end TotalVariation

lemma summable_mass {S : Type u} (μ : ProbabilityLaw S) :
    Summable (fun i => (μ i).toReal) :=
  ENNReal.summable_toReal (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)

lemma tsum_mass {S : Type u} (μ : ProbabilityLaw S) :
    ∑' i, (μ i).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun i => μ.apply_ne_top i), μ.tsum_coe]
  rfl

lemma lawEvent_real {S : Type u} (μ : ProbabilityLaw S) (A : Set S) :
    (lawEvent μ A).toReal = ∑' i, A.indicator (fun j => (μ j).toReal) i := by
  rw [lawEvent, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro i
    by_cases hi : i ∈ A <;> simp [hi]
  · intro i
    by_cases hi : i ∈ A <;> simp [hi, μ.apply_ne_top]

private lemma summable_abs_diff {S : Type u} (μ ν : ProbabilityLaw S) :
    Summable (fun i => |(μ i).toReal - (ν i).toReal|) := by
  simpa only [Real.norm_eq_abs] using ((summable_mass μ).sub (summable_mass ν)).norm

private lemma summable_pos_diff {S : Type u} (μ ν : ProbabilityLaw S) :
    Summable (fun i => max ((μ i).toReal - (ν i).toReal) 0) := by
  apply (summable_abs_diff μ ν).of_nonneg_of_le
  · intro i; exact le_max_right _ _
  · intro i; exact max_le (le_abs_self _) (abs_nonneg _)

private lemma tsum_pos_diff {S : Type u} (μ ν : ProbabilityLaw S) :
    (∑' i, max ((μ i).toReal - (ν i).toReal) 0) =
      (1 / 2 : ℝ) * ∑' i, |(μ i).toReal - (ν i).toReal| := by
  have hd := (summable_mass μ).sub (summable_mass ν)
  have hz : ∑' i, ((μ i).toReal - (ν i).toReal) = 0 := by
    rw [(summable_mass μ).tsum_sub (summable_mass ν), tsum_mass, tsum_mass, sub_self]
  calc
    _ = ∑' i, (|(μ i).toReal - (ν i).toReal| + ((μ i).toReal - (ν i).toReal)) / 2 := by
      apply tsum_congr
      intro i
      by_cases hi : 0 ≤ (μ i).toReal - (ν i).toReal
      · rw [max_eq_left hi, abs_of_nonneg hi]; ring
      · rw [max_eq_right (le_of_not_ge hi), abs_of_nonpos (le_of_not_ge hi)]; ring
    _ = _ := by
      rw [tsum_div_const, (summable_abs_diff μ ν).tsum_add hd, hz]
      ring

private lemma event_diff_le_pos {S : Type u} (μ ν : ProbabilityLaw S) (A : Set S) :
    (lawEvent μ A).toReal - (lawEvent ν A).toReal ≤
      ∑' i, max ((μ i).toReal - (ν i).toReal) 0 := by
  rw [lawEvent_real, lawEvent_real,
    ← ((summable_mass μ).indicator A).tsum_sub ((summable_mass ν).indicator A)]
  apply Summable.tsum_le_tsum _
    (((summable_mass μ).indicator A).sub ((summable_mass ν).indicator A))
    (summable_pos_diff μ ν)
  intro i
  by_cases hi : i ∈ A
  · simpa only [Set.indicator_of_mem hi] using
      (le_max_left ((μ i).toReal - (ν i).toReal) 0)
  · simpa only [Set.indicator_of_notMem hi, sub_self] using
      (le_max_right ((μ i).toReal - (ν i).toReal) 0)

private lemma event_abs_le_half {S : Type u} (μ ν : ProbabilityLaw S) (A : Set S) :
    |(lawEvent μ A).toReal - (lawEvent ν A).toReal| ≤
      (1 / 2 : ℝ) * ∑' i, |(μ i).toReal - (ν i).toReal| := by
  apply abs_le.mpr
  constructor
  · have h := event_diff_le_pos ν μ A
    rw [tsum_pos_diff] at h
    simp_rw [abs_sub_comm (ν _).toReal (μ _).toReal] at h
    linarith
  · rw [← tsum_pos_diff]
    exact event_diff_le_pos μ ν A

private lemma positive_event {S : Type u} (μ ν : ProbabilityLaw S) :
    (lawEvent μ {i | (ν i).toReal ≤ (μ i).toReal}).toReal -
      (lawEvent ν {i | (ν i).toReal ≤ (μ i).toReal}).toReal =
      (1 / 2 : ℝ) * ∑' i, |(μ i).toReal - (ν i).toReal| := by
  rw [lawEvent_real, lawEvent_real,
    ← ((summable_mass μ).indicator _).tsum_sub ((summable_mass ν).indicator _),
    ← tsum_pos_diff]
  apply tsum_congr
  intro i
  by_cases hi : (ν i).toReal ≤ (μ i).toReal
  · simp [hi]
  · simp [hi, max_eq_right (sub_nonpos.mpr (le_of_not_ge hi))]

/-- The event supremum is half the real ℓ¹ distance. -/
theorem totalVariation_eq_half_tsum {S : Type u} [Countable S] (μ ν : ProbabilityLaw S) :
    totalVariation μ ν = (1 / 2 : ℝ) * ∑' i, |(μ i).toReal - (ν i).toReal| := by
  let b := (1 / 2 : ℝ) * ∑' i, |(μ i).toReal - (ν i).toReal|
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (tsum_nonneg (fun _ => abs_nonneg _))
  have hbound : BddAbove (Set.range (fun A : Set S =>
      |(lawEvent μ A).toReal - (lawEvent ν A).toReal|)) :=
    ⟨b, by rintro _ ⟨A, rfl⟩; exact event_abs_le_half μ ν A⟩
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨A, rfl⟩; exact event_abs_le_half μ ν A)
  · have h := le_csSup hbound (Set.mem_range_self {i | (ν i).toReal ≤ (μ i).toReal})
    rw [positive_event μ ν, abs_of_nonneg hb] at h
    exact h

lemma summable_overlap {S : Type u} (μ ν : ProbabilityLaw S) :
    Summable (fun i => min (μ i).toReal (ν i).toReal) := by
  apply (summable_mass μ).of_nonneg_of_le
  · intro i; exact le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · intro i; exact min_le_left _ _

/-- The distance is the mass left after removing the common part. -/
theorem totalVariation_eq_one_sub_overlap {S : Type u} [Countable S]
    (μ ν : ProbabilityLaw S) :
    totalVariation μ ν = 1 - ∑' i, min (μ i).toReal (ν i).toReal := by
  rw [totalVariation_eq_half_tsum]
  have hid : (fun i => |(μ i).toReal - (ν i).toReal|) =
      (fun i => (μ i).toReal + (ν i).toReal - 2 * min (μ i).toReal (ν i).toReal) := by
    funext i
    by_cases hi : (μ i).toReal ≤ (ν i).toReal
    · rw [min_eq_left hi, abs_of_nonpos (sub_nonpos.mpr hi)]; ring
    · rw [min_eq_right (le_of_not_ge hi), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hi))]
      ring
  rw [hid, ((summable_mass μ).add (summable_mass ν)).tsum_sub
    ((summable_overlap μ ν).mul_left 2),
    (summable_mass μ).tsum_add (summable_mass ν), tsum_mass, tsum_mass, tsum_mul_left]
  ring

lemma overlap_le_one {S : Type u} (μ ν : ProbabilityLaw S) :
    (∑' i, min (μ i) (ν i)) ≤ 1 := by
  calc
    _ ≤ ∑' i, μ i := ENNReal.tsum_le_tsum (fun _ => min_le_left _ _)
    _ = 1 := μ.tsum_coe

lemma overlap_toReal {S : Type u} (μ ν : ProbabilityLaw S) :
    (∑' i, min (μ i) (ν i)).toReal = ∑' i, min (μ i).toReal (ν i).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun i => ne_top_of_le_ne_top (μ.apply_ne_top i) (min_le_left _ _))]
  apply tsum_congr
  intro i
  exact ENNReal.toReal_min (μ.apply_ne_top i) (ν.apply_ne_top i)

lemma overlap_bind_le {S : Type u} (μ ν : ProbabilityLaw S) (P : StochasticMatrix S) :
    (∑' i, min (μ i) (ν i)) ≤ ∑' j, min (μ.bind P j) (ν.bind P j) := by
  calc
    _ = ∑' i, ∑' j, min (μ i) (ν i) * P i j := by
      simp only [ENNReal.tsum_mul_left, (P _).tsum_coe, mul_one]
    _ = ∑' j, ∑' i, min (μ i) (ν i) * P i j := ENNReal.tsum_comm
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply le_min
      · exact ENNReal.tsum_le_tsum (fun i => mul_le_mul_left (min_le_left _ _) _)
      · exact ENNReal.tsum_le_tsum (fun i => mul_le_mul_left (min_le_right _ _) _)

/-- A stochastic transition increases overlap and therefore contracts the distance. -/
theorem totalVariation_bind_le {S : Type u} [Countable S] (μ ν : ProbabilityLaw S)
    (P : StochasticMatrix S) :
    totalVariation (μ.bind P) (ν.bind P) ≤ totalVariation μ ν := by
  rw [totalVariation_eq_one_sub_overlap, totalVariation_eq_one_sub_overlap,
    ← overlap_toReal, ← overlap_toReal]
  exact sub_le_sub_left (ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (overlap_le_one _ _))
    (overlap_bind_le μ ν P)) 1

/-- Pointwise convergence to a probability law implies total variation convergence.
The common masses are dominated by the summable limiting masses. -/
theorem tendsto_totalVariation_of_pointwise {S : Type u} [Countable S]
    (μn : ℕ → ProbabilityLaw S) (μ : ProbabilityLaw S)
    (h : ∀ i, Tendsto (fun n => (μn n i).toReal) atTop (𝓝 (μ i).toReal)) :
    Tendsto (fun n => totalVariation (μn n) μ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ∑' i, min (μn n i).toReal (μ i).toReal)
      atTop (𝓝 (∑' i, (μ i).toReal)) := by
    apply tendsto_tsum_of_dominated_convergence (summable_mass μ)
    · intro i
      simpa only [min_self] using (h i).min (tendsto_const_nhds (x := (μ i).toReal))
    · apply Filter.Eventually.of_forall
      intro n i
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
      exact min_le_right _ _
  have hfinal := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  simpa only [totalVariation_eq_one_sub_overlap, tsum_mass, sub_self] using hfinal

end
end P207.Markov
