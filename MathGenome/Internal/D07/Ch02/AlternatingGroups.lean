import MathGenome.Internal.D07.Ch01.KernelImage
import MathGenome.Internal.D07.Ch02.SymmetricOrder
import MathGenome.Internal.D07.Ch02.TranspositionsParity
import MathGenome.Internal.Specs.D07.Ch02.AlternatingGroups

/-! Alternating groups: kernel, normality, index, order, generation and small cases. -/

namespace D07.Ch02.AlternatingGroups

universe u

open Specs.D07.Ch02.PermutationConvention

theorem even_permutations : Specs.D07.Ch02.AlternatingGroups.EvenPermutations.{u} := by
  classical
  intro X _ σ
  exact Equiv.Perm.mem_alternatingGroup

theorem kernel_identity : Specs.D07.Ch02.AlternatingGroups.KernelIdentity.{u} := by
  classical
  intro X _
  rfl

theorem normal_subgroup : Specs.D07.Ch02.AlternatingGroups.NormalSubgroup.{u} := by
  classical
  intro X _
  exact D07.Ch01.KernelImage.kernel_normal (Equiv.Perm X) ℤˣ
    (Specs.D07.Ch02.TranspositionsParity.signValue X)

theorem index_two : Specs.D07.Ch02.AlternatingGroups.IndexTwo.{u} := by
  classical
  intro X _ n hn htwo
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact alternatingGroup.index_eq_two

theorem alternating_order : Specs.D07.Ch02.AlternatingGroups.AlternatingOrder.{u} := by
  classical
  intro X _ n hn htwo
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  rw [nat_card_alternatingGroup, hn]

/-- The support of a nontrivial written cycle is exactly its distinct entries. -/
private theorem support_card_formPerm {X : Type u} [Fintype X] [DecidableEq X]
    (l : List X) (h : l.Nodup) (hlen : 2 ≤ l.length) :
    l.formPerm.support.card = l.length := by
  rw [List.support_formPerm_of_nodup l h, List.toFinset_card_of_nodup h]
  intro x hx
  simp [hx] at hlen

theorem three_cycle_listing : Specs.D07.Ch02.AlternatingGroups.ThreeCycleListing.{u} := by
  classical
  intro X _ σ
  constructor
  · intro hσ
    obtain ⟨l, hl, hlen, heq⟩ :=
      D07.Ch02.CycleDecomposition.cycle_has_listing hσ.isCycle
    refine ⟨l, hl, ?_, heq⟩
    rw [← support_card_formPerm l hl hlen, heq, hσ.card_support]
  · rintro ⟨l, hl, hlen, heq⟩
    change l.formPerm = σ at heq
    rw [← heq, ← card_support_eq_three_iff, support_card_formPerm l hl (by omega), hlen]

theorem three_cycles_even : Specs.D07.Ch02.AlternatingGroups.ThreeCyclesEven.{u} := by
  classical
  intro X _ l hl hlen
  exact ((three_cycle_listing X _).mpr ⟨l, hl, hlen, rfl⟩).mem_alternatingGroup

theorem three_cycle_generation :
    Specs.D07.Ch02.AlternatingGroups.ThreeCycleGeneration.{u} := by
  classical
  intro X _ n _ _
  have hset : {σ : Equiv.Perm X | ∃ (l : List X) (h : l.Nodup),
      l.length = 3 ∧ cycleConstructorValue X l h = σ} =
      {σ : Equiv.Perm X | σ.IsThreeCycle} := by
    ext σ
    exact (three_cycle_listing X σ).symm
  rw [hset]
  exact Equiv.Perm.closure_three_cycles_eq_alternating

theorem small_alternating_group :
    Specs.D07.Ch02.AlternatingGroups.SmallAlternatingGroup.{u} := by
  classical
  intro X _ hcard
  haveI : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact ⟨Subsingleton.elim _ _, Nat.card_unique⟩

end D07.Ch02.AlternatingGroups
