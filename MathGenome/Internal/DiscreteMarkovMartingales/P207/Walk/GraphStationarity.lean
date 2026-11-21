import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.GraphStationarity
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.TimeReversal
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StationaryReturnTimes

open scoped ENNReal
universe u
namespace P207.Walk.GraphStationarity
open P207.Markov
noncomputable section

abbrev neighborKernel : GraphStationaritySpec.neighborKernelType.{u} :=
  @P207.Walk.neighborKernel
abbrev degreeLaw : GraphStationaritySpec.degreeLawType.{u} :=
  @P207.Walk.degreeLaw

theorem degree_pos : GraphStationaritySpec.degree_pos.{u} := by
  intro V _ _ G _ hG v
  exact hG.preconnected.degree_pos_of_nontrivial v

theorem edge_count_pos : GraphStationaritySpec.edge_count_pos.{u} := by
  intro V _ _ G _ hG
  exact lt_of_lt_of_le (degree_pos G hG (Classical.arbitrary V))
    (G.degree_le_card_edgeFinset (Classical.arbitrary V))

theorem neighborKernel_apply : GraphStationaritySpec.neighborKernel_apply.{u} := by
  intro V _ _ G _ hG v w
  simp [P207.Walk.neighborKernel]

theorem neighborKernel_row_sum : GraphStationaritySpec.neighborKernel_row_sum.{u} := by
  intro V _ _ G _ hG v
  exact (neighborKernel G hG v).tsum_coe

variable {V : Type u} [Fintype V] [Nontrivial V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)

/-- A graph edge is exactly a positive one-step transition. -/
theorem neighborKernel_pos_iff (v w : V) :
    0 < neighborKernel G hG v w ↔ G.Adj v w := by
  rw [neighborKernel_apply]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- A graph walk gives accessibility in the shared countable-chain interface. -/
theorem accessible_of_walk {v w : V} (p : G.Walk v w) :
    Accessible (neighborKernel G hG) v w := by
  induction p with
  | nil => exact accessible_refl _ _
  | @cons v w z h p ih =>
    apply accessible_trans (neighborKernel G hG) (j := w) _ ih
    refine ⟨1, ?_⟩
    rw [power_one]
    exact (neighborKernel_pos_iff G hG v w).mpr h

theorem neighborKernel_irreducible : GraphStationaritySpec.neighborKernel_irreducible.{u} := by
  intro V _ _ G _ hG v w
  obtain ⟨p⟩ := hG.preconnected v w
  exact ⟨accessible_of_walk G hG p, accessible_of_walk G hG p.reverse⟩

theorem degreeLaw_apply : GraphStationaritySpec.degreeLaw_apply.{u} := by
  intro V _ _ G _ hG v
  rfl

theorem degreeLaw_sum : GraphStationaritySpec.degreeLaw_sum.{u} := by
  intro V _ _ G _ hG
  exact (degreeLaw G hG).tsum_coe

/-- Every directed edge carries the same stationary probability flow. -/
theorem edge_flow (v w : V) :
    degreeLaw G hG v * neighborKernel G hG v w =
      if G.Adj v w then 1 / ((2 * G.edgeFinset.card : ℕ) : ℝ≥0∞) else 0 := by
  rw [degreeLaw_apply, neighborKernel_apply]
  split_ifs with h
  · have hd : (G.degree v : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (degree_pos G hG v).ne'
    simp only [div_eq_mul_inv, one_mul]
    calc
      ((G.degree v : ℝ≥0∞) * (((2 * G.edgeFinset.card : ℕ) : ℝ≥0∞))⁻¹) *
          (G.degree v : ℝ≥0∞)⁻¹ =
          ((G.degree v : ℝ≥0∞) * (G.degree v : ℝ≥0∞)⁻¹) *
            (((2 * G.edgeFinset.card : ℕ) : ℝ≥0∞))⁻¹ := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hd (by simp), one_mul]
  · exact mul_zero _

theorem detailed_balance : GraphStationaritySpec.detailed_balance.{u} := by
  intro V _ _ G _ hG v w
  simp only [edge_flow, G.adj_comm]

theorem stationary : GraphStationaritySpec.stationary.{u} := by
  intro V _ _ G _ hG
  exact detailedBalance_stationary _ _ (detailed_balance G hG)

theorem reversible : GraphStationaritySpec.reversible.{u} := by
  intro V _ _ _ _ G _ hG
  exact (reversible_iff_detailedBalance _ _).mpr (detailed_balance G hG)

theorem stationary_unique : GraphStationaritySpec.stationary_unique.{u} := by
  intro V _ _ _ _ G _ hG ρ hρ
  exact stationary_probability_unique _ _ _ (neighborKernel_irreducible G hG) hρ
    (stationary G hG)

end
end P207.Walk.GraphStationarity
