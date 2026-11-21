import MathGenome.Internal.D07.Ch02.CycleDecomposition
import MathGenome.Internal.Specs.D07.Ch02.ConjugacyCycleType

/-!
Conjugacy and cycle type, `K07.02.conjugacy_cycle_type`.
The cycle-length multiset omits fixed points and is connected explicitly
to the written decompositions of the preceding entry.
-/

namespace D07.Ch02.ConjugacyCycleType

open Equiv
open Specs.D07.Ch02.ConjugacyCycleType

universe u

theorem decomposition_cycle_lengths : DecompositionCycleLengths.{u} := by
  classical
  intro X _ σ L hL
  let := Fintype.ofFinite X
  change σ.cycleType = _
  have hc : ∀ g ∈ L.map List.formPerm, g.IsCycle := by
    intro g hg
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
    exact List.isCycle_formPerm (hL.1 l hl).1 (hL.1 l hl).2
  have hd : (L.map List.formPerm).Pairwise Perm.Disjoint := by
    apply List.pairwise_map.mpr
    apply hL.2.1.imp_of_mem
    intro l m hl hm hdis
    exact (List.formPerm_disjoint_iff (hL.1 l hl).1 (hL.1 m hm).1
      (hL.1 l hl).2 (hL.1 m hm).2).mpr hdis
  rw [Perm.cycleType_eq (L.map List.formPerm) hL.2.2 hc hd, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  dsimp
  rw [List.support_formPerm_of_nodup l (hL.1 l hl).1]
  · exact List.toFinset_card_of_nodup (hL.1 l hl).1
  · intro x hx
    have := (hL.1 l hl).2
    simp [hx] at this

theorem conjugacy_iff_cycle_lengths : ConjugacyIffCycleLengths.{u} := by
  classical
  intro X _ σ τ
  let := Fintype.ofFinite X
  change (∃ b : Perm X, b * σ * b⁻¹ = τ) ↔ σ.cycleType = τ.cycleType
  exact isConj_iff.symm.trans Perm.isConj_iff_cycleType_eq

private theorem conjugate_formPerm {X : Type u} [DecidableEq X]
    (b : Perm X) (l : List X) : b * l.formPerm * b⁻¹ = (l.map b).formPerm := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil => simp
    | cons y l =>
      simp only [List.map_cons, List.formPerm_cons_cons] at ih ⊢
      rw [← conj_mul, ih, ← Equiv.swap_apply_apply]

theorem conjugate_listed_cycle : ConjugateListedCycle.{u} := by
  classical
  intro X b l hl
  exact conjugate_formPerm b l

end D07.Ch02.ConjugacyCycleType
