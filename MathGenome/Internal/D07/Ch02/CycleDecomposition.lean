import MathGenome.Internal.D07.Ch02.PermutationConvention
import MathGenome.Internal.Specs.D07.Ch02.CycleDecomposition
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Disjoint-cycle decomposition

`K07.02.cycle_decomposition`. The output is a list of lists of entries,
not merely a collection of abstract permutations. Nontrivial cycles have
at least two distinct entries. The empty decomposition is permitted.
-/

namespace D07.Ch02.CycleDecomposition

open Equiv
open Specs.D07.Ch02.CycleDecomposition

universe u

private theorem rotation_iff {X : Type u} [DecidableEq X] {l m : List X}
    (hl : l.Nodup) (hm : m.Nodup) (hlen : 2 ≤ l.length) (_ : 2 ≤ m.length) :
    l.formPerm = m.formPerm ↔ l.IsRotated m := by
  rw [List.formPerm_eq_formPerm_iff hl hm]
  have h : ¬ l.length ≤ 1 := by omega
  simp [h]

theorem cycle_rotation : Specs.D07.Ch02.CycleDecomposition.CycleRotation.{u} := by
  classical
  intro X l m hl hm hlen hmen
  exact rotation_iff hl hm hlen hmen

theorem disjoint_commute : Specs.D07.Ch02.CycleDecomposition.DisjointCommute.{u} := by
  intro X σ τ h
  exact h.commute.eq

theorem disjoint_listed_cycles_commute :
    Specs.D07.Ch02.CycleDecomposition.DisjointListedCyclesCommute.{u} := by
  classical
  intro X l m hl hm hd
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : x ∈ l
  · exact Or.inr (List.formPerm_apply_of_notMem (fun hm => hd hx hm))
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

/-- Each abstract nontrivial cycle on a finite set has a faithful written cycle. -/
theorem cycle_has_listing {X : Type u} [Fintype X] [DecidableEq X]
    {g : Perm X} (hg : g.IsCycle) :
    ∃ l : List X, l.Nodup ∧ 2 ≤ l.length ∧ l.formPerm = g := by
  have hg' := hg
  obtain ⟨x, hx, _⟩ := hg
  refine ⟨g.toList x, Equiv.Perm.nodup_toList g x, ?_, ?_⟩
  · exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr
      (Equiv.Perm.mem_support.mpr hx)
  · rw [Equiv.Perm.formPerm_toList, hg'.cycleOf_eq hx]

/-- Convert a disjoint list of abstract cycles to disjoint lists of entries. -/
private theorem list_cycles_have_listings {X : Type u} [Fintype X] [DecidableEq X]
    (C : List (Perm X)) (hc : ∀ g ∈ C, g.IsCycle) (hd : C.Pairwise Perm.Disjoint) :
    ∃ L : List (List X), (∀ l ∈ L, l.Nodup ∧ 2 ≤ l.length) ∧
      L.Pairwise List.Disjoint ∧ L.map List.formPerm = C := by
  induction C with
  | nil => exact ⟨[], by simp⟩
  | cons g C ih =>
    obtain ⟨l, hl, hlen, hlg⟩ := cycle_has_listing (hc g List.mem_cons_self)
    obtain ⟨L, hL, hdL, hLC⟩ :=
      ih (fun g hg => hc g (List.mem_cons_of_mem _ hg)) hd.of_cons
    refine ⟨l :: L, ?_, ?_, ?_⟩
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨hl, hlen⟩
      · exact hL m hm
    · rw [List.pairwise_cons]
      refine ⟨?_, hdL⟩
      intro m hm
      apply (List.formPerm_disjoint_iff hl (hL m hm).1 hlen (hL m hm).2).mp
      rw [hlg]
      exact (List.pairwise_cons.mp hd).1 _
        (hLC ▸ List.mem_map.mpr ⟨m, hm, rfl⟩)
    · simp only [List.map_cons, hlg, hLC]

theorem cycle_decomposition :
    Specs.D07.Ch02.CycleDecomposition.ExistsDecomposition.{u} := by
  classical
  intro X _ σ
  let := Fintype.ofFinite X
  obtain ⟨C, hp, hc, hd⟩ := σ.truncCycleFactors.out
  obtain ⟨L, hL, hdL, hLC⟩ := list_cycles_have_listings C hc hd
  exact ⟨L, hL, hdL, by rw [hLC, hp]⟩

private theorem decomposition_cycles {X : Type u} [DecidableEq X]
    {σ : Perm X} {L : List (List X)} (hL : Decomposition σ L) :
    (∀ g ∈ L.map List.formPerm, g.IsCycle) ∧
      (L.map List.formPerm).Pairwise Perm.Disjoint := by
  constructor
  · intro g hg
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
    exact List.isCycle_formPerm (hL.1 l hl).1 (hL.1 l hl).2
  · apply List.pairwise_map.mpr
    apply hL.2.1.imp_of_mem
    intro l m hl hm hd
    exact (List.formPerm_disjoint_iff (hL.1 l hl).1 (hL.1 m hm).1
      (hL.1 l hl).2 (hL.1 m hm).2).mpr hd

/-- Lift equality of written-cycle permutations to rotation, retaining membership
information to exclude singleton and empty lists. -/
private theorem rotations_of_equal_cycles {X : Type u} [DecidableEq X]
    {L M : List (List X)}
    (hL : ∀ l ∈ L, l.Nodup ∧ 2 ≤ l.length)
    (hM : ∀ m ∈ M, m.Nodup ∧ 2 ≤ m.length)
    (h : List.Forall₂ (fun l m => l.formPerm = m.formPerm) L M) :
    List.Forall₂ List.IsRotated L M := by
  induction h with
  | nil => exact .nil
  | @cons l m L M heq h ih =>
    apply List.Forall₂.cons
    · exact (rotation_iff (hL l List.mem_cons_self).1 (hM m List.mem_cons_self).1
        (hL l List.mem_cons_self).2 (hM m List.mem_cons_self).2).mp heq
    · exact ih (fun l hl => hL l (List.mem_cons_of_mem _ hl))
        (fun m hm => hM m (List.mem_cons_of_mem _ hm))

theorem cycle_decomposition_unique :
    Specs.D07.Ch02.CycleDecomposition.UniqueDecomposition.{u} := by
  classical
  intro X _ σ τ L M hL hM
  obtain ⟨hcL, hdL⟩ := decomposition_cycles hL
  obtain ⟨hcM, hdM⟩ := decomposition_cycles hM
  constructor
  · intro heq
    have hp : (L.map List.formPerm).Perm (M.map List.formPerm) :=
      Equiv.Perm.list_cycles_perm_list_cycles (hL.2.2.trans (heq.trans hM.2.2.symm))
        hcL hcM hdL hdM
    have href : List.Forall₂ (fun g l => g = l.formPerm) (M.map List.formPerm) M := by
      simp
    obtain ⟨M', hrel, hperm⟩ := List.perm_comp_forall₂ hp href
    refine ⟨M', hperm, ?_⟩
    apply rotations_of_equal_cycles hL.1
      (fun m hm => hM.1 m (hperm.mem_iff.mp hm))
    exact List.forall₂_map_left_iff.mp hrel
  · rintro ⟨M', hperm, hrot⟩
    have hmap : L.map List.formPerm = M'.map List.formPerm := by
      have hv := (List.forall₂_and_left L M').mpr ⟨hL.1, hrot⟩
      have he := hv.imp (fun l m h => List.formPerm_eq_of_isRotated h.1.1 h.2)
      have hm : List.Forall₂ Eq (L.map List.formPerm) (M'.map List.formPerm) :=
        List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr he)
      simpa only [List.forall₂_eq_eq_eq] using hm
    have hp : (M'.map List.formPerm).prod = (M.map List.formPerm).prod := by
      exact ((hperm.map _).symm.prod_eq' (hdM.imp Perm.Disjoint.commute)).symm
    exact hL.2.2.symm.trans ((congrArg List.prod hmap).trans (hp.trans hM.2.2))

end D07.Ch02.CycleDecomposition
