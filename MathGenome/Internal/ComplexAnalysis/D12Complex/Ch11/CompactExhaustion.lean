import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.CompactExhaustion
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Set

namespace D12Complex.Ch11.CompactExhaustion

/-- At positive indices the distance condition already forces membership in Ω.
This expresses each stage as a closed subset of a closed ball. -/
lemma stage_eq_closedBall_inter (Ω : Set ℂ) {j : ℕ} (hj : 1 ≤ j) :
    compactExhaustionStage Ω j = Metric.closedBall 0 (j : ℝ) ∩
      {z | ENNReal.ofReal (1 / (j : ℝ)) ≤ Metric.infEDist z Ωᶜ} := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  ext z
  constructor
  · rintro ⟨_, hn, hd⟩
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hn, hd⟩
  · rintro ⟨hn, hd⟩
    refine ⟨?_, by simpa only [Metric.mem_closedBall, dist_zero_right] using hn, hd⟩
    by_contra hz
    have hz0 := Metric.infEDist_zero_of_mem (show z ∈ Ωᶜ from hz)
    have hp : 0 < ENNReal.ofReal (1 / (j : ℝ)) :=
      ENNReal.ofReal_pos.mpr (one_div_pos.mpr hjR)
    change ENNReal.ofReal (1 / (j : ℝ)) ≤ Metric.infEDist z Ωᶜ at hd
    rw [hz0] at hd
    exact (not_le_of_gt hp) hd

theorem compact : Specs.D12Complex.Ch11.CompactExhaustion.compact_type := by
  intro Ω _ j hj
  rw [stage_eq_closedBall_inter Ω hj]
  exact (isCompact_closedBall (0 : ℂ) (j : ℝ)).inter_right
    (isClosed_le continuous_const Metric.continuous_infEDist)

/-- Monotonicity for positive indices, without any openness assumption. -/
lemma stage_mono (Ω : Set ℂ) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    compactExhaustionStage Ω j ⊆ compactExhaustionStage Ω k := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  rintro z ⟨hz, hn, hd⟩
  exact ⟨hz, hn.trans hjkR,
    (ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hjR hjkR)).trans hd⟩

theorem nesting : Specs.D12Complex.Ch11.CompactExhaustion.nesting_type := by
  intro Ω _ j hj
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hjnext : (j : ℝ) < (j + 1 : ℕ) := by simp
  have hrecip : ENNReal.ofReal (1 / ((j + 1 : ℕ) : ℝ)) <
      ENNReal.ofReal (1 / (j : ℝ)) :=
    (ENNReal.ofReal_lt_ofReal_iff (one_div_pos.mpr hjR)).mpr
      (one_div_lt_one_div_of_lt hjR hjnext)
  let U : Set ℂ := {z | ‖z‖ < ((j + 1 : ℕ) : ℝ) ∧
    ENNReal.ofReal (1 / ((j + 1 : ℕ) : ℝ)) < Metric.infEDist z Ωᶜ}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Metric.continuous_infEDist)
  have hUsub : U ⊆ compactExhaustionStage Ω (j + 1) := by
    rw [stage_eq_closedBall_inter Ω (by omega)]
    intro z hz
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1.le, hz.2.le⟩
  intro z hz
  apply interior_maximal hUsub hUopen
  exact ⟨hz.2.1.trans_lt hjnext, hrecip.trans_le hz.2.2⟩

/-- Every point of an open set belongs to a positive stage. The proof also
works when the complement is empty, since its extended distance is infinity. -/
lemma exists_stage_of_mem {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    ∃ j : ℕ, 1 ≤ j ∧ z ∈ compactExhaustionStage Ω j := by
  have hzcl : z ∉ closure Ωᶜ := by simpa only [hΩ.isClosed_compl.closure_eq, Set.mem_compl_iff, not_not] using hz
  obtain ⟨ε, hε, hεdist⟩ := Metric.exists_real_pos_lt_infEDist_of_notMem_closure hzcl
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
  let j := max (n + 1) m
  have hnj : n + 1 ≤ j := le_max_left _ _
  have hmj : m ≤ j := le_max_right _ _
  have hj : 1 ≤ j := le_trans (by omega) hnj
  have hnR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnjR : ((n + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hnj
  have hinv : 1 / (j : ℝ) < ε :=
    (one_div_le_one_div_of_le hnR hnjR).trans_lt (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
  refine ⟨j, hj, hz, ?_, ?_⟩
  · exact hm.le.trans (by exact_mod_cast hmj)
  · exact (ENNReal.ofReal_le_ofReal hinv.le).trans hεdist.le

theorem union : Specs.D12Complex.Ch11.CompactExhaustion.union_type := by
  intro Ω hΩ
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, _, hz⟩
    exact hz.1
  · intro hz
    obtain ⟨j, hj, hzj⟩ := exists_stage_of_mem hΩ hz
    exact ⟨j, hj, hzj⟩

theorem cofinal : Specs.D12Complex.Ch11.CompactExhaustion.cofinal_type := by
  intro Ω hΩ L hL hLΩ
  let U : ℕ → Set ℂ := fun n => interior (compactExhaustionStage Ω (n + 1))
  have hUmono : Monotone U := by
    intro m n hmn
    exact interior_mono (stage_mono Ω (by omega) (by omega))
  have hcover : L ⊆ ⋃ n, U n := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := exists_stage_of_mem hΩ (hLΩ hz)
    exact mem_iUnion.mpr ⟨j, nesting Ω hΩ j hj hzj⟩
  obtain ⟨n, hn⟩ := hL.elim_directed_cover U (fun _ => isOpen_interior) hcover hUmono.directed_le
  exact ⟨n + 1, by omega, hn.trans interior_subset⟩

theorem empty : Specs.D12Complex.Ch11.CompactExhaustion.empty_type := by
  intro j
  ext z
  simp [compactExhaustionStage]

theorem univ : Specs.D12Complex.Ch11.CompactExhaustion.univ_type := by
  intro j
  ext z
  simp [compactExhaustionStage, Metric.mem_closedBall, dist_zero_right]

end D12Complex.Ch11.CompactExhaustion
