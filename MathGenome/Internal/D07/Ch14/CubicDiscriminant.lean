import MathGenome.Internal.Specs.D07.Ch14.CubicDiscriminant
import MathGenome.Internal.D07.Ch14.Discriminant
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Linarith

universe u v

namespace D07.Ch14.CubicDiscriminant

open Polynomial Specs.D07.Ch14.Discriminant Specs.D07.Ch14.CubicDiscriminant

/-- A transitive subgroup of S₃ has at least three elements. Its index is
therefore at most two, and the unique index-two subgroup is A₃. -/
theorem transitive_subgroup_three (H : Subgroup (Equiv.Perm (Fin 3)))
    (htrans : ∀ i j : Fin 3, ∃ g : H, g.val i = j) :
    H = alternatingGroup (Fin 3) ∨ H = ⊤ := by
  have hsurj : Function.Surjective (fun g : H => g.val (0 : Fin 3)) := by
    intro j
    exact htrans 0 j
  have hcard : 3 ≤ Nat.card H := by
    simpa using Nat.card_le_card_of_surjective _ hsurj
  have hmul : Nat.card H * H.index = 6 := by
    calc
      _ = Nat.card (Equiv.Perm (Fin 3)) := H.card_mul_index
      _ = 6 := by simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hindex : H.index ≤ 2 := by nlinarith
  by_cases htop : H = ⊤
  · exact Or.inr htop
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two
      (Nat.le_antisymm hindex (H.one_lt_index_of_ne_top htop)))

/-- The order-three alternating group is the cyclic group C₃. -/
theorem alternating_three_equiv_cyclic :
    Nonempty (alternatingGroup (Fin 3) ≃* Multiplicative (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨mulEquivOfPrimeCardEq (p := 3) ?_ ?_⟩
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    rfl
  · simp [Nat.card_eq_fintype_card]

theorem alternating_three_ne_top :
    alternatingGroup (Fin 3) ≠ (⊤ : Subgroup (Equiv.Perm (Fin 3))) := by
  intro h
  have hi := alternatingGroup.index_eq_two (α := Fin 3)
  rw [h, Subgroup.index_top] at hi
  contradiction

/-- The faithful transitive action comes from the actual field automorphisms. -/
theorem numbered_criterion : NumberedCriterion.{u, v} := by
  intro K L _ _ _ f hchar hirr hsep hsplit hdeg b Δ hΔ
  have hpos : 0 < f.natDegree := by rw [hdeg]; decide
  have hinj : Function.Injective (numberedAction b) :=
    b.symm.permCongrHom.injective.comp
      (PolynomialRootAction.rootActionFaithful K L f hpos hsep hsplit)
  have htrans : ∀ i j : Fin 3,
      ∃ g : (numberedAction b).range, g.val i = j := by
    intro i j
    obtain ⟨σ, hσ⟩ := PolynomialRootAction.rootActionTransitive K L f hpos hsep hsplit
      hirr (b i) (b j)
    refine ⟨⟨numberedAction b σ, ⟨σ, rfl⟩⟩, ?_⟩
    change b.symm (Specs.D07.Ch14.PolynomialRootAction.rootPermutationValue K L f σ
      (b i)) = j
    rw [hσ, b.symm_apply_apply]
  have hcases := transitive_subgroup_three (numberedAction b).range htrans
  have hAle : alternatingGroup (Fin 3) ≤ (numberedAction b).range := by
    rcases hcases with h | h
    · exact h.symm.le
    · rw [h]; exact le_top
  have hiff := Discriminant.alternating_iff_square K L f 3 hchar hsep hsplit hdeg b Δ hΔ
  have hA : (numberedAction b).range = alternatingGroup (Fin 3) ↔ IsSquare Δ := by
    constructor
    · intro h
      exact hiff.mp h.le
    · intro h
      exact le_antisymm (hiff.mpr h) hAle
  have hS : (numberedAction b).range = ⊤ ↔ ¬ IsSquare Δ := by
    constructor
    · intro h hsq
      exact alternating_three_ne_top ((hA.mpr hsq).symm.trans h)
    · intro hn
      exact hcases.resolve_left (fun h => hn (hA.mp h))
  refine ⟨hA, hS, ?_, ?_⟩
  · intro hsq
    let e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hA.mpr hsq))
    obtain ⟨eC⟩ := alternating_three_equiv_cyclic
    exact ⟨⟨e⟩, ⟨e.trans eC⟩⟩
  · intro hn
    exact ⟨((MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (hS.mpr hn))).trans Subgroup.topEquiv⟩

/-- The root count constructs the numbering and the accepted discriminant
theorem constructs the nonzero base element before applying the classification. -/
theorem cubic_criterion : CubicCriterion.{u, v} := by
  intro K L _ _ _ f hchar hirr hsep hsplit hdeg
  have hpos : 0 < f.natDegree := by rw [hdeg]; decide
  let b : Fin 3 ≃ f.rootSet L :=
    (Fintype.equivFinOfCardEq
      ((PolynomialRootAction.rootCount K L f hpos hsep hsplit).trans hdeg)).symm
  obtain ⟨Δ, hne, hΔ⟩ := Discriminant.discriminant_in_base K L f 3 hsep hsplit hdeg b
  exact ⟨b, Δ, hne, hΔ, numbered_criterion K L f hchar hirr hsep hsplit hdeg b Δ hΔ,
    Discriminant.leadingCoefficient_square_test K f Δ hsplit.1⟩

end D07.Ch14.CubicDiscriminant
