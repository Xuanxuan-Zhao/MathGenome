import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.HoffmanCirculation
import MathGenome.Internal.ExtremalOptimization.P205.Networks.HoffmanReduction
import MathGenome.Internal.ExtremalOptimization.P205.Networks.MaxFlowMinCut

/-! Hoffman circulation and fixed divergence (paper.tex, W38).
The auxiliary source has outgoing capacity exactly the positive demand.
Max-flow/min-cut therefore attains that demand when every cut bounds it below.
No division by the demand or positivity hypothesis on it is needed. -/

open scoped BigOperators Classical
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed FiniteCombinatorics.Graph.Flows
open HoffmanSpec

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Every feasible auxiliary flow has value at most the total positive demand,
including when that demand is zero. -/
theorem Hoffman.auxiliary_value_le_demand (G : Digraph V A) (c : A → ℝ)
    (β : V → ℝ) (hc : ∀ a, 0 ≤ c a) (F : AuxArc A β → ℝ)
    (hF : (HoffmanSpec.auxNetwork G c β hc).Feasible F) :
    (HoffmanSpec.auxNetwork G c β hc).value F ≤ HoffmanSpec.demand β := by
  change (auxGraph G β).divergence F source ≤ ∑ x : Positive β, β x.val
  rw [Hoffman.source_divergence]
  exact Finset.sum_le_sum (fun x _ => (hF.1 (.inr (.inl x))).2)

theorem hoffman_fixed_divergence :
    HoffmanCirculationSpec.hoffman_fixed_divergence.{u,v} := by
  intro V A _ _ G lo hi b hbounds hb
  rw [Hoffman.original_feasible_iff G lo hi b hbounds hb,
    Hoffman.original_cut_iff G lo hi b hbounds]
  let N := HoffmanSpec.shiftedNetwork G lo hi b hbounds
  let D := HoffmanSpec.demand (HoffmanSpec.shiftBalance G lo b)
  change (∃ F, N.Feasible F ∧ N.value F = D) ↔
    ∀ T, N.IsCut T → D ≤ N.cutCapacity T
  constructor
  · rintro ⟨F, hF, hv⟩ T hT
    have h := flow_cut_bound N F T hF hT
    change N.value F ≤ N.cutCapacity T at h
    rwa [hv] at h
  · intro hcut
    obtain ⟨F, T, hF, hT, _, _, heq⟩ := max_flow_min_cut N
    refine ⟨F, hF, le_antisymm ?_ ?_⟩
    · exact Hoffman.auxiliary_value_le_demand G _ _ _ F hF
    · exact (hcut T hT).trans_eq heq.symm

theorem integral_hoffman_fixed_divergence :
    HoffmanCirculationSpec.integral_hoffman_fixed_divergence.{u,v} := by
  intro V A _ _ G lo hi b hbounds hb hlo hhi hbint
  constructor
  · rintro ⟨f, hf, _⟩
    exact (hoffman_fixed_divergence G lo hi b hbounds hb).mp ⟨f, hf⟩
  · intro hcut
    apply (Hoffman.original_integral_iff G lo hi b hbounds hb hlo hhi hbint).mpr
    let N := HoffmanSpec.shiftedNetwork G lo hi b hbounds
    let D := HoffmanSpec.demand (HoffmanSpec.shiftBalance G lo b)
    have hdata := Hoffman.integral_shift G lo hi (fun _ => 0) b hlo hhi hbint
    have hcap : Integral N.capacity :=
      (Hoffman.integral_auxiliary _ _ hdata.1 hdata.2.1).1
    obtain ⟨F, T, hF, hT, _, _, heq, hFint⟩ := integral_max_flow_min_cut N hcap
    have hlower := (Hoffman.original_cut_iff G lo hi b hbounds).mp hcut T hT
    refine ⟨F, hF, le_antisymm ?_ (hlower.trans_eq heq.symm), hFint⟩
    exact Hoffman.auxiliary_value_le_demand G _ _ _ F hF

theorem hoffman_circulation : HoffmanCirculationSpec.hoffman_circulation.{u,v} := by
  intro V A _ _ G lo hi hbounds
  simpa [CutCondition, vertexSum, sub_nonneg] using
    hoffman_fixed_divergence G lo hi (fun _ => 0) hbounds (by simp)

theorem integral_hoffman_circulation :
    HoffmanCirculationSpec.integral_hoffman_circulation.{u,v} := by
  intro V A _ _ G lo hi hbounds hlo hhi
  simpa [CutCondition, vertexSum, sub_nonneg] using
    integral_hoffman_fixed_divergence G lo hi (fun _ => 0) hbounds (by simp)
      hlo hhi (fun _ => ⟨0, by simp⟩)

end P205.Networks
