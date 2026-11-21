import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Variation
import Mathlib.Tactic.Linarith

/-! The isolated-spike obstruction from K03.15.rs_jump. For every a < c < b,
the actual point value at c gives opposite adjacent increments, even though
both one-sided limits are zero. All arguments use refinement sums and the
upstream strict endpoint partitions; no mesh or measure integral is substituted. -/
namespace SingleVariableAnalysis.Stieltjes
open Riemann
open scoped BigOperators
open Filter Topology
namespace SpikeSpec
export Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction (spikeValue)
end SpikeSpec

noncomputable abbrev unitSpike := SpikeSpec.spikeValue

@[simp] theorem unitSpike_self (c : ℝ) : unitSpike c c = 1 := by
  simp [unitSpike, SpikeSpec.spikeValue]

@[simp] theorem unitSpike_of_ne {c x : ℝ} (hx : x ≠ c) : unitSpike c x = 0 := by
  simp [unitSpike, SpikeSpec.spikeValue, hx]

theorem spike_variation_and_bounds :
    Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction.variationAndBounds := by
  intro a c b hac hcb
  have hv : BV.totalVariation (unitSpike c) a b = 2 := BV.real_unit_spike hac hcb
  refine ⟨hv, ?_, 1, ?_⟩
  · change BV.totalVariation (unitSpike c) a b < ⊤
    rw [hv]
    norm_num
  · intro x _
    simp only [SpikeSpec.spikeValue]
    split_ifs <;> norm_num

theorem spike_zero_net_jump :
    Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction.zeroNetJump := by
  intro c
  refine ⟨0, 0, rfl, rfl, ?_, ?_, by norm_num, by simp, by simp⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (unitSpike_of_ne (ne_of_lt hx)).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (unitSpike_of_ne (ne_of_gt hx)).symm

/-- The left and right endpoint tags are permitted by the closed-cell convention. -/
def leftTags {a b : ℝ} (P : Partition a b) : Tagging P :=
  fun i => ⟨P.point i.castSucc, le_rfl, (P.strictMono (Fin.castSucc_lt_succ (i := i))).le⟩

def rightTags {a b : ℝ} (P : Partition a b) : Tagging P :=
  fun i => ⟨P.point i.succ, (P.strictMono (Fin.castSucc_lt_succ (i := i))).le, le_rfl⟩

/-- In each cell select an endpoint different from c. -/
noncomputable def avoidingTags {a b : ℝ} (P : Partition a b) (c : ℝ) : Tagging P :=
  fun i => if P.point i.castSucc = c then rightTags P i else leftTags P i

theorem avoidingTags_ne {a b : ℝ} (P : Partition a b) (c : ℝ) (i : Fin P.n) :
    (avoidingTags P c i : ℝ) ≠ c := by
  classical
  have hi := P.strictMono (Fin.castSucc_lt_succ (i := i))
  dsimp [avoidingTags, leftTags, rightTags]
  split_ifs with h
  · dsimp
    exact ne_of_gt (h ▸ hi)
  · exact h

theorem spike_avoiding_sum {a b : ℝ} (P : Partition a b) (c : ℝ) :
    taggedSum P (avoidingTags P c) (unitSpike c) (unitSpike c) = 0 := by
  unfold taggedSum S.sumValue
  apply Finset.sum_eq_zero
  intro i _
  rw [unitSpike_of_ne (avoidingTags_ne P c i), smul_zero]

/-- Only the cell whose left endpoint is c contributes to the left-tag sum. -/
theorem spike_left_sum {a b c : ℝ} (P : Partition a b) (k : Fin P.n)
    (hk : P.point k.castSucc = c) :
    taggedSum P (leftTags P) (unitSpike c) (unitSpike c) = -1 := by
  classical
  change (∑ i : Fin P.n, (unitSpike c (P.point i.succ) -
    unitSpike c (P.point i.castSucc)) * unitSpike c (P.point i.castSucc)) = -1
  rw [Finset.sum_eq_single k]
  · have hne : P.point k.succ ≠ c := by
      rw [← hk]
      exact ne_of_gt (P.strictMono (Fin.castSucc_lt_succ (i := k)))
    simp [hk, hne]
  · intro i _ hik
    have hne : P.point i.castSucc ≠ c := by
      intro hi
      have he := P.strictMono.injective (hi.trans hk.symm)
      exact hik (Fin.ext (congrArg (fun l : Fin (P.n + 1) => l.val) he))
    simp [hne]
  · simp

/-- Only the cell whose right endpoint is c contributes to the right-tag sum. -/
theorem spike_right_sum {a b c : ℝ} (P : Partition a b) (k : Fin P.n)
    (hk : P.point k.succ = c) :
    taggedSum P (rightTags P) (unitSpike c) (unitSpike c) = 1 := by
  classical
  change (∑ i : Fin P.n, (unitSpike c (P.point i.succ) -
    unitSpike c (P.point i.castSucc)) * unitSpike c (P.point i.succ)) = 1
  rw [Finset.sum_eq_single k]
  · have hne : P.point k.castSucc ≠ c := by
      rw [← hk]
      exact ne_of_lt (P.strictMono (Fin.castSucc_lt_succ (i := k)))
    simp [hk, hne]
  · intro i _ hik
    have hne : P.point i.succ ≠ c := by
      intro hi
      have he := P.strictMono.injective (hi.trans hk.symm)
      exact hik (Fin.ext (by have hv := congrArg Fin.val he; simpa using hv))
    simp [hne]
  · simp

theorem spike_sums_on_partition :
    Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction.sumsOnPartition := by
  intro a c b hac hcb P hc
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
  have hjpos : 0 < j.val := by
    by_contra h
    have he : j = 0 := Fin.ext (by change j.val = 0; omega)
    rw [he, P.first] at hj
    exact (ne_of_lt hac) hj
  have hjlt : j.val < P.n := by
    by_contra h
    have he : j = Fin.last P.n := Fin.ext (by dsimp; omega)
    rw [he, P.last] at hj
    exact (ne_of_gt hcb) hj
  let kr : Fin P.n := ⟨j.val, hjlt⟩
  let kl : Fin P.n := ⟨j.val - 1, by omega⟩
  have hr : P.point kr.castSucc = c := hj
  have hl : P.point kl.succ = c := by
    convert hj using 1
    apply congrArg P.point
    apply Fin.ext
    dsimp [kl]
    omega
  exact ⟨leftTags P, avoidingTags P c, rightTags P,
    spike_left_sum P kr hr, spike_avoiding_sum P c, spike_right_sum P kl hl⟩

/-- Insert c without removing any point of the proposed controlling partition. -/
theorem spike_sums_on_refinements :
    Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction.sumsOnRefinements := by
  classical
  intro a c b hac hcb P₀
  let s := insert c (points P₀)
  have ha : a ∈ s := Finset.mem_insert_of_mem (endpoints P₀).1
  have hb : b ∈ s := Finset.mem_insert_of_mem (endpoints P₀).2.1
  have hs : ∀ x ∈ s, x ∈ Set.Icc a b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hac.le, hcb.le⟩
    · exact (endpoints P₀).2.2 x hx
  obtain ⟨P, hP⟩ := finite_representation s ha hb hs
  change points P = s at hP
  have hPP₀ : Refines P P₀ := by
    change points P₀ ⊆ points P
    rw [hP]
    exact Finset.subset_insert _ _
  have hc : c ∈ points P := by
    rw [hP]
    exact Finset.mem_insert_self _ _
  exact ⟨P, hPP₀, hc, spike_sums_on_partition hac hcb P hc⟩

/-- The two fixed, separated sum values contradict every proposed limit. -/
theorem spike_no_refinement_limit :
    Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction.noRefinementLimit := by
  intro a c b hac hcb
  rintro ⟨I, hI⟩
  obtain ⟨P₀, hP₀⟩ := hI (1/2) (by norm_num)
  obtain ⟨P, hPP₀, _, tneg, tzero, tpos, hneg, _, hpos⟩ :=
    spike_sums_on_refinements hac hcb P₀
  have hn := hP₀ P hPP₀ tneg
  have hp := hP₀ P hPP₀ tpos
  rw [hneg, Real.norm_eq_abs] at hn
  rw [hpos, Real.norm_eq_abs] at hp
  have hn' := (abs_lt.mp hn).1
  have hp' := (abs_lt.mp hp).2
  linarith

theorem spike_no_integral :
    Specs.SingleVariableAnalysis.Ch15.RsSpikeObstruction.noIntegral := by
  intro a c b hac hcb
  rintro ⟨I, hI⟩
  apply spike_no_refinement_limit hac hcb
  exact ⟨I, by simpa only [ite_eq_left (hac.trans hcb).le] using hI.2.2⟩

end SingleVariableAnalysis.Stieltjes
