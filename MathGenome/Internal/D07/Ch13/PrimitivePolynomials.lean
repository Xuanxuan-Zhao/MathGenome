import MathGenome.Internal.Specs.D07.Ch13.PrimitivePolynomials
import MathGenome.Internal.D07.Ch13.FrobeniusRoots
import MathGenome.Internal.D07.Ch13.PrimitiveDistinction

/-!
K07.13.primitive_polynomials. Frobenius is an injective field homomorphism,
so it preserves multiplicative orders. The upstream orbit theorem therefore
gives equality of the orders of all roots. In a finite unit group a unit
generates precisely when its order is the cardinality of that group.
-/

universe u v w
namespace D07.Ch13.PrimitivePolynomials

open Polynomial
open Specs.D07.Ch13.PrimitivePolynomials

/-- Finite-field multiplicative primitivity, with the base embedding explicit. -/
abbrev IsPrimitive : PrimitivePredicateType.{u,v} := primitivePredicateValue

theorem root_orders_equal : RootOrdersEqual.{u,v} := by
  intro K L _ _ _ _ f a b hf ha hb
  let := Fintype.ofFinite K
  obtain ⟨i, rfl⟩ := (FrobeniusRoots.roots_eq_orbit f a hf ha b).mp hb
  let Φ := FiniteField.frobeniusAlgHom K L ^ i.val
  have h := orderOf_injective Φ.toMonoidHom Φ.injective a
  change orderOf ((FiniteField.frobeniusAlgHom K L ^ i.val) a) = orderOf a at h
  rw [FrobeniusRoots.frobenius_pow_apply] at h
  exact h.symm

lemma root_generator_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [Finite K] [Finite L] (f : K[X]) (hf : Irreducible f)
    (b : L) (hb : aeval b f = 0) :
    (∃ a : Lˣ, aeval (a : L) f = 0 ∧ Subgroup.zpowers a = ⊤) ↔
      ∃ a : Lˣ, (a : L) = b ∧ Subgroup.zpowers a = ⊤ := by
  constructor
  · rintro ⟨a, ha, hag⟩
    obtain ⟨i, hi⟩ := (FrobeniusRoots.roots_eq_orbit f (a : L) hf ha b).mp hb
    have hb0 : b ≠ 0 := by rw [hi]; exact pow_ne_zero _ a.ne_zero
    let c : Lˣ := Units.mk0 b hb0
    have ho : orderOf c = orderOf a := by
      calc
        orderOf c = orderOf (c : L) := orderOf_units.symm
        _ = orderOf (a : L) := (root_orders_equal K L f (a : L) b hf ha hb).symm
        _ = orderOf a := orderOf_units
    refine ⟨c, rfl, ?_⟩
    apply (Subgroup.zpowers c).eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, orderOf_eq_card_of_zpowers_eq_top hag]
  · rintro ⟨a, hab, hag⟩
    exact ⟨a, hab.symm ▸ hb, hag⟩

theorem root_choice_independent : RootChoiceIndependent.{u,v} := by
  intro K L _ _ _ _ _ n f hn _hcard hm hd hf b hb
  change (0 < n ∧ f.Monic ∧ f.natDegree = n ∧ Irreducible f ∧ _) ↔ _
  simp only [hn, hm, hd, hf, true_and]
  exact root_generator_iff f hf b hb

/-- Transport of a cyclic generator through an isomorphism, including infinite
groups; no finiteness assumption is needed for this helper. -/
lemma generator_map {G : Type*} {H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a : G) (ha : Subgroup.zpowers a = ⊤) :
    Subgroup.zpowers (e a) = ⊤ := by
  calc
    Subgroup.zpowers (e a) = (Subgroup.zpowers a).map e.toMonoidHom :=
      (e.toMonoidHom.map_zpowers a).symm
    _ = ⊤ := by
      rw [ha, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr e.surjective

lemma primitive_transport {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (n : ℕ) (f : K[X])
    (h : IsPrimitive K L n f) : IsPrimitive K M n f := by
  obtain ⟨hn, hm, hd, hf, a, ha, hag⟩ := h
  let eU := Units.mapEquiv e.toMulEquiv
  refine ⟨hn, hm, hd, hf, eU a, ?_, generator_map eU a hag⟩
  change aeval (e (a : L)) f = 0
  rw [aeval_algHom_apply, ha, map_zero]

theorem base_preserving_invariance : BasePreservingInvariance.{u,v,w} := by
  intro K L M _ _ _ _ _ e n f
  exact ⟨primitive_transport e n f, primitive_transport e.symm n f⟩

theorem irreducible_not_primitive : IrreducibleNotPrimitive.{u} := by
  intro Ω _ _ _
  obtain ⟨E, i, hfin, hcard, hdim, hcardu, hi2, _hgen, hord, hing⟩ :=
    PrimitiveDistinction.embedded_counterexample Ω
  let := hfin
  have hf := PrimitiveDistinction.quadratic_over_three.2
  have hi : aeval (i : E) (X ^ 2 + 1 : (ZMod 3)[X]) = 0 := by
    simp only [aeval_add, map_pow, aeval_X, map_one, hi2, neg_add_cancel]
  refine ⟨E, hfin, hcard, hdim, hcardu, ?_, ?_, hf, ?_, ?_⟩
  · exact monic_X_pow_add_C (1 : ZMod 3) (by decide : 2 ≠ 0)
  · simp
  · intro b hb
    calc
      orderOf b = orderOf (i : E) :=
        (root_orders_equal (ZMod 3) E _ (i : E) b hf hi hb).symm
      _ = orderOf i := orderOf_units
      _ = 4 := hord
  · rintro ⟨_, _, _, _, h⟩
    obtain ⟨a, hai, hag⟩ := (root_generator_iff _ hf (i : E) hi).mp h
    have hai' : a = i := Units.ext hai
    exact hing (hai' ▸ hag)

end D07.Ch13.PrimitivePolynomials
