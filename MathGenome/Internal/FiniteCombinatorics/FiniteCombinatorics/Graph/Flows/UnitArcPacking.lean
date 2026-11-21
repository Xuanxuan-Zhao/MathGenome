import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.PathCycleDecomposition
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.UnitArcPacking
import Mathlib.Algebra.Order.BigOperators.Group.List

universe u v
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed
namespace UnitArcPacking
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable {G : Digraph V A} {s t : V}

private theorem contribution_nonneg (ps : List (ℤ × Directed.Spec.path G s t))
    (hps : ∀ p ∈ ps, 0 < p.1) (a : A) :
    ∀ z ∈ ps.map (fun p => PathCycleSpec.pathContribution p.1 p.2 a), 0 ≤ z := by
  classical
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  unfold PathCycleSpec.pathContribution
  split_ifs
  · exact (hps p hp).le
  · exact le_refl 0

/-- A unit bound on each selected arc forces unit path weights and rules out
both repeated paths and shared selected arcs, even in a list with multiplicities. -/
private theorem extract (B : Finset A)
    (cover : ∀ p : Directed.Spec.path G s t, ∃ a ∈ B, a ∈ Directed.Spec.arcs p.val)
    (ps : List (ℤ × Directed.Spec.path G s t))
    (hps : ∀ p ∈ ps, 0 < p.1)
    (bound : ∀ a ∈ B,
      (ps.map (fun p => PathCycleSpec.pathContribution p.1 p.2 a)).sum ≤ 1) :
    (ps.map Prod.snd).Nodup ∧
    (ps.map Prod.snd).Pairwise (fun p q => ∀ a ∈ B,
      ¬ (a ∈ Directed.Spec.arcs p.val ∧ a ∈ Directed.Spec.arcs q.val)) ∧
    (ps.map Prod.fst).sum = (ps.length : ℤ) := by
  classical
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : 0 < p.1 := hps p (by simp)
    have ht : ∀ q ∈ ps, 0 < q.1 := fun q hq => hps q (by simp [hq])
    have hn (a : A) : 0 ≤
        (ps.map (fun q => PathCycleSpec.pathContribution q.1 q.2 a)).sum :=
      List.sum_nonneg (contribution_nonneg ps ht a)
    have hpc (a : A) : 0 ≤ PathCycleSpec.pathContribution p.1 p.2 a := by
      unfold PathCycleSpec.pathContribution
      split_ifs <;> omega
    have bt : ∀ a ∈ B,
        (ps.map (fun q => PathCycleSpec.pathContribution q.1 q.2 a)).sum ≤ 1 := by
      intro a ha
      have hb := bound a ha
      simp only [List.map_cons, List.sum_cons] at hb
      linarith [hpc a]
    obtain ⟨a₀, ha₀, hap⟩ := cover p.2
    have hw : p.1 = 1 := by
      have hb := bound a₀ ha₀
      simp only [List.map_cons, List.sum_cons,
        PathCycleSpec.pathContribution, ite_eq_left hap] at hb
      have hn₀ := hn a₀
      simp only [PathCycleSpec.pathContribution] at hn₀
      omega
    have hd : ∀ q ∈ ps.map Prod.snd, ∀ a ∈ B,
        ¬ (a ∈ Directed.Spec.arcs p.2.val ∧ a ∈ Directed.Spec.arcs q.val) := by
      intro q hq a ha ⟨hap, haq⟩
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hle := List.single_le_sum (contribution_nonneg ps ht a)
        (PathCycleSpec.pathContribution r.1 r.2 a) (List.mem_map.mpr ⟨r, hr, rfl⟩)
      have hb := bound a ha
      simp only [List.map_cons, List.sum_cons,
        PathCycleSpec.pathContribution, ite_eq_left hap, hw] at hb
      simp only [PathCycleSpec.pathContribution, ite_eq_left haq] at hle
      have := ht r hr
      omega
    obtain ⟨hnd, hpw, hsum⟩ := ih ht bt
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hm
      exact hd p.2 hm a₀ ha₀ ⟨hap, hap⟩
    · exact List.pairwise_cons.mpr ⟨hd, hpw⟩
    · simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, hw, hsum]
      omega

end UnitArcPacking
/-- Extract the unit-multiplicity packing required by the vertex-splitting
argument, using only integrality of the loads and the selected unit capacities. -/
theorem unit_arc_packing : UnitArcPackingSpec.unit_arc_packing.{u,v} := by
  classical
  intro V A _ _ N B hcap cover f hf hint hval
  by_cases hz : Spec.value N f = 0
  · exact ⟨∅, by simpa using hz.symm, by simp, by simp⟩
  have hpos : 0 < Spec.value N f := lt_of_le_of_ne hval (Ne.symm hz)
  obtain ⟨ps, cs, hps, hcs, hsum, hload⟩ :=
    (integer_flow_path_cycle_decomposition N f hf hint).1 hpos
  have bound : ∀ a ∈ B,
      (ps.map (fun p => PathCycleSpec.pathContribution p.1 p.2 a)).sum ≤ 1 := by
    intro a ha
    have hc : 0 ≤ (cs.map (fun c => CirculationSpec.contribution c.1 c.2 a)).sum := by
      apply List.sum_nonneg
      intro z hz
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
      unfold CirculationSpec.contribution
      split_ifs
      · exact (hcs c hc).le
      · exact le_refl 0
    have hb : f a ≤ 1 := (hf.1 a).2.trans_eq (hcap a ha)
    rw [hload a] at hb
    have hb' : (ps.map (fun p => PathCycleSpec.pathContribution p.1 p.2 a)).sum +
        (cs.map (fun c => CirculationSpec.contribution c.1 c.2 a)).sum ≤ (1 : ℤ) := by
      exact_mod_cast hb
    omega
  obtain ⟨hnd, hpw, hlen⟩ := UnitArcPacking.extract B cover ps hps bound
  let D := (ps.map Prod.snd).toFinset
  refine ⟨D, ?_, ?_, fun h => (hz h).elim⟩
  · have hdcard : D.card = ps.length := by
      simpa [D] using List.toFinset_card_of_nodup hnd
    rw [hdcard, ← hsum, hlen]
    simp only [Int.cast_natCast]
  · let : Std.Symm (fun p q : Directed.Spec.path N.graph N.source N.sink =>
        ∀ a ∈ B, ¬ (a ∈ Directed.Spec.arcs p.val ∧ a ∈ Directed.Spec.arcs q.val)) :=
      ⟨fun p q h a ha hh => h a ha hh.symm⟩
    intro p hp q hq hne
    exact hpw.forall (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq) hne

end FiniteCombinatorics.Graph.Flows
