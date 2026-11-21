import MathGenome.Internal.Specs.D07.Ch18.NilpotenceExamplesSolvableNonnilpotent
import MathGenome.Internal.D07.Ch02.AlternatingGroups
import MathGenome.Internal.D07.Ch15.SolvableClosure
import MathGenome.Internal.D07.Ch18.MixedCommutators
import MathGenome.Internal.D07.Ch18.NilpotenceCriteria

namespace D07.Ch18.NilpotenceExamplesSolvableNonnilpotent

open scoped commutatorElement
open Specs.D07.Ch18.CentralSeries

private abbrev a : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private abbrev s : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private theorem a_even : a ∈ alternatingGroup (Fin 3) := by
  change Equiv.Perm.sign a = 1
  decide

private theorem even_cases : ∀ p : Equiv.Perm (Fin 3),
    p ∈ alternatingGroup (Fin 3) → p = 1 ∨ p = a ∨ p = a⁻¹ := by
  change ∀ p : Equiv.Perm (Fin 3), Equiv.Perm.sign p = 1 →
    p = 1 ∨ p = a ∨ p = a⁻¹
  decide

private theorem a_mem_mixed :
    a ∈ ⁅alternatingGroup (Fin 3), (⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆ := by
  have h := Subgroup.commutator_mem_commutator a_even
    (Subgroup.mem_top s)
  have heq : ⁅a, s⁆ = a⁻¹ := by decide
  rw [heq] at h
  simpa only [inv_inv] using
    (⁅alternatingGroup (Fin 3), (⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆).inv_mem h

theorem mixed_commutator :
    ⁅alternatingGroup (Fin 3), (⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆ =
      alternatingGroup (Fin 3) := by
  apply le_antisymm
  · exact Subgroup.commutator_le_left _ _
  · intro p hp
    rcases even_cases p hp with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact a_mem_mixed
    · exact Subgroup.inv_mem _ a_mem_mixed

theorem derived_subgroup :
    commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  apply le_antisymm
  · change commutator (Equiv.Perm (Fin 3)) ≤ (Equiv.Perm.sign).ker
    exact Abelianization.commutator_subset_ker Equiv.Perm.sign
  · change alternatingGroup (Fin 3) ≤ ⁅(⊤ : Subgroup (Equiv.Perm (Fin 3))), ⊤⁆
    rw [← mixed_commutator]
    exact Subgroup.commutator_mono le_top le_rfl

theorem first_derived_term :
    derivedSeries (Equiv.Perm (Fin 3)) 1 = alternatingGroup (Fin 3) :=
  derived_subgroup

theorem second_derived_term : derivedSeries (Equiv.Perm (Fin 3)) 2 = ⊥ := by
  rw [derivedSeries_succ, first_derived_term]
  exact Subgroup.commutator_self_eq_bot_iff.mpr
    (alternatingGroup.isMulCommutative_of_card_le_three (by simp))

theorem lower_central_terms (i : ℕ) (hi : 2 ≤ i) :
    lowerValue (Equiv.Perm (Fin 3)) i = alternatingGroup (Fin 3) := by
  induction i, hi using Nat.le_induction with
  | base => exact derived_subgroup
  | succ i hi ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    change ⁅lowerValue (Equiv.Perm (Fin 3)) (n + 1), ⊤⁆ = _
    rw [ih, mixed_commutator]

theorem solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
  ⟨⟨2, second_derived_term⟩⟩

private theorem alternating_ne_bot : alternatingGroup (Fin 3) ≠ ⊥ := by
  intro h
  have ha : a = 1 := Subgroup.mem_bot.mp (h ▸ a_even)
  have hne : a ≠ 1 := by decide
  exact hne ha

theorem no_class_bound (c : ℕ) :
    ¬ Specs.D07.Ch18.NilpotenceCriteria.classAtMostValue (Equiv.Perm (Fin 3)) c := by
  intro hc
  have hl := (NilpotenceCriteria.classAtMost_iff_lower (Equiv.Perm (Fin 3)) c).mp hc
  cases c with
  | zero =>
    change (⊤ : Subgroup (Equiv.Perm (Fin 3))) = ⊥ at hl
    exact alternating_ne_bot (le_bot_iff.mp (hl ▸ (le_top : alternatingGroup (Fin 3) ≤ ⊤)))
  | succ c =>
    rw [lower_central_terms (c + 1 + 1) (by omega)] at hl
    exact alternating_ne_bot hl

theorem not_nilpotent : ¬ Group.IsNilpotent (Equiv.Perm (Fin 3)) := by
  intro hn
  obtain ⟨c, hc⟩ :=
    (NilpotenceCriteria.nilpotent_iff_exists_bound (Equiv.Perm (Fin 3))).mp hn
  exact no_class_bound c hc

end D07.Ch18.NilpotenceExamplesSolvableNonnilpotent
