import MathGenome.Internal.D07.Ch01.ArithmeticExamples
import MathGenome.Internal.D07.Ch02.CyclicDefinition
import MathGenome.Internal.D07.Ch02.OrderDivisibility
import MathGenome.Internal.Specs.D07.Ch02.CyclicModelsIsomorphism
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The integer and residue models, with their generator formulas, and
classification of cyclic groups, including trivial and infinite groups. -/

namespace D07.Ch02.CyclicModelsIsomorphism

universe u v

theorem infinite_model (G : Type u) [Group G] (x : G)
    (hx : Subgroup.zpowers x = ⊤) (horder : orderOf x = 0) :
    Infinite G ∧ ∃ e : Multiplicative ℤ ≃* G,
      ∀ k : ℤ, e (Multiplicative.ofAdd k) = x ^ k := by
  have hbij : Function.Bijective (zpowersHom G x) := by
    constructor
    · intro a b hab
      apply Multiplicative.toAdd.injective
      exact (D07.Ch02.OrderDivisibility.infinite_powers_eq_iff G x horder _ _).mp hab
    · exact MonoidHom.range_eq_top.mp hx
  let e : Multiplicative ℤ ≃* G := MulEquiv.ofBijective (zpowersHom G x) hbij
  exact ⟨e.toEquiv.infinite_iff.mp inferInstance, e, fun _ => rfl⟩

theorem finite_model (G : Type u) [Group G] (x : G) (n : ℕ)
    (hx : Subgroup.zpowers x = ⊤) (hn : 0 < n) (horder : orderOf x = n) :
    Finite G ∧ Nat.card G = n ∧
      ∃ e : Multiplicative (ZMod n) ≃* G,
        ∀ k : ℤ, e (Multiplicative.ofAdd (k : ZMod n)) = x ^ k := by
  have hcard : Nat.card G = n :=
    (orderOf_eq_card_of_zpowers_eq_top hx).symm.trans horder
  have hfinite : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ hn.ne')
  have hgen : ∀ y : G, y ∈ Subgroup.zpowers x := fun y => hx ▸ Subgroup.mem_top y
  exact ⟨hfinite, hcard, zmodMulEquivOfGenerator hgen hcard,
    zmodMulEquivOfGenerator_apply_ofAdd_intCast hgen hcard⟩

theorem isomorphic_iff_same_order (G : Type u) (H : Type v)
    [Group G] [Group H] [IsCyclic G] [IsCyclic H] :
    Nonempty (G ≃* H) ↔
      (Finite G ∧ Finite H ∧ Nat.card G = Nat.card H) ∨
        (Infinite G ∧ Infinite H) := by
  constructor
  · rintro ⟨e⟩
    cases finite_or_infinite G with
    | inl h =>
      exact Or.inl ⟨h, e.toEquiv.finite_iff.mp h, Nat.card_congr e.toEquiv⟩
    | inr h =>
      exact Or.inr ⟨h, e.toEquiv.infinite_iff.mp h⟩
  · rintro (⟨hG, hH, hcard⟩ | ⟨hG, hH⟩)
    · exact ⟨mulEquivOfCyclicCardEq hcard⟩
    · let := hG
      let := hH
      exact ⟨intCyclicMulEquiv.symm.trans intCyclicMulEquiv⟩

theorem isomorphic_iff_same_cardinality (G : Type u) (H : Type v)
    [Group G] [Group H] [IsCyclic G] [IsCyclic H] :
    Nonempty (G ≃* H) ↔
      Cardinal.lift.{v} (Cardinal.mk G) = Cardinal.lift.{u} (Cardinal.mk H) := by
  constructor
  · rintro ⟨e⟩
    exact Cardinal.lift_mk_eq'.mpr ⟨e.toEquiv⟩
  · intro h
    obtain ⟨e⟩ := Cardinal.lift_mk_eq'.mp h
    exact ⟨mulEquivOfCyclicCardEq (Nat.card_congr e)⟩

end D07.Ch02.CyclicModelsIsomorphism
