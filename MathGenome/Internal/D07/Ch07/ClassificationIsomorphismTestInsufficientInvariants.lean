import MathGenome.Internal.Specs.D07.Ch07.ClassificationIsomorphismTestInsufficientInvariants
import MathGenome.Internal.D07.Ch07.TorsionCountInvariants
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace D07.Ch07.ClassificationIsomorphismTestInsufficientInvariants

open Specs.D07.Ch07.ClassificationIsomorphismTestInsufficientInvariants
open Specs.D07.Ch07.TorsionCountInvariants
open Specs.D07.Ch06.CompositionSeriesDefinition

/-- An isomorphism restricts to the intrinsic annihilator subgroup. -/
def torsionCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A ≃+ B) (p k : ℕ) : torsionSubgroup A p k ≃+ torsionSubgroup B p k where
  toFun x := ⟨f x.val, by
    change (p ^ k) • f x.val = 0
    rw [← map_nsmul, show (p ^ k) • x.val = 0 from x.property, map_zero]⟩
  invFun x := ⟨f.symm x.val, by
    change (p ^ k) • f.symm x.val = 0
    rw [← map_nsmul, show (p ^ k) • x.val = 0 from x.property, map_zero]⟩
  left_inv x := by ext; exact f.symm_apply_apply x.val
  right_inv x := by ext; exact f.apply_symm_apply x.val
  map_add' _ _ := by ext; exact f.map_add _ _

/-- Annihilators in a product are products of annihilators. -/
def torsionProdEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] (p k : ℕ) :
    torsionSubgroup (A × B) p k ≃
      torsionSubgroup A p k × torsionSubgroup B p k where
  toFun x := (⟨x.val.1, congrArg Prod.fst x.property⟩,
    ⟨x.val.2, congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val, x.2.val), Prod.ext x.1.property x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem torsion_prod_card (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (p k : ℕ) : Nat.card (torsionSubgroup (A × B) p k) =
      Nat.card (torsionSubgroup A p k) * Nat.card (torsionSubgroup B p k) := by
  rw [Nat.card_congr (torsionProdEquiv A B p k), Nat.card_prod]

theorem zmod_exponent (n : ℕ) : AddMonoid.exponent (ZMod n) = n := by
  rw [← ringChar_eq_addMonoidExponent, ringChar.eq (ZMod n) n]

theorem order_four_cardinality : OrderFourCardinality := by
  norm_num [OrderFourCardinality, Klein, Nat.card_prod, Nat.card_zmod]

theorem order_four_not_isomorphic : OrderFourNotIsomorphic := by
  rintro ⟨f⟩
  have h := AddMonoid.exponent_eq_of_addEquiv f
  norm_num [zmod_exponent, AddMonoid.exponent_prod] at h

theorem order_four_element_orders : OrderFourElementOrders := by
  refine ⟨ZMod.addOrderOf_one 4, fun x hx => ?_⟩
  have h := AddMonoid.addOrder_dvd_exponent x
  have he : AddMonoid.exponent Klein = 2 := by
    norm_num [Klein, AddMonoid.exponent_prod, zmod_exponent]
  rw [he, hx] at h
  norm_num at h

theorem prime_example_cardinality : PrimeExampleCardinality := by
  intro p hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  simp only [SquarePair, MixedTriple, Nat.card_prod, Nat.card_zmod]
  constructor <;> ring

theorem prime_example_exponent : PrimeExampleExponent := by
  intro p _hp
  simp only [SquarePair, MixedTriple, AddMonoid.exponent_prod, zmod_exponent]
  change Nat.lcm (p ^ 2) (p ^ 2) = p ^ 2 ∧
    Nat.lcm (p ^ 2) (Nat.lcm p p) = p ^ 2
  simp only [Nat.lcm_self]
  exact ⟨trivial, Nat.lcm_eq_left (dvd_pow_self p (by decide : 2 ≠ 0))⟩

theorem prime_example_torsion_counts : PrimeExampleTorsionCounts := by
  intro p hp
  simp only [SquarePair, MixedTriple, torsion_prod_card]
  rw [D07.Ch07.TorsionCountInvariants.cyclic_torsion_card p hp 2 1]
  have h : Nat.card (torsionSubgroup (ZMod p) p 1) = p := by
    have hc := D07.Ch07.TorsionCountInvariants.cyclic_torsion_card p hp 1 1
    rw [pow_one] at hc
    simpa only [min_self, pow_one] using hc
  rw [h]
  norm_num
  constructor <;> ring

theorem prime_example_not_isomorphic : PrimeExampleNotIsomorphic := by
  intro p hp ⟨f⟩
  have h := Nat.card_congr (torsionCongr f p 1).toEquiv
  rw [(prime_example_torsion_counts p hp).1,
      (prime_example_torsion_counts p hp).2] at h
  have := Nat.pow_right_injective hp.two_le h
  norm_num at this

/-- A three-term chain through a subgroup of order two. -/
def threeTermChain {G : Type*} [Group G] (H : Subgroup G) : Fin 3 → Subgroup G :=
  ![⊥, H, ⊤]

theorem threeTermChain_strict {G : Type*} [Group G] (H : Subgroup G)
    (hG : Nat.card G = 4) (hH : Nat.card H = 2) : StrictMono (threeTermChain H) := by
  have hb : H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hH
    omega
  have ht : H ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hG] at hH
    omega
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact bot_lt_iff_ne_bot.mpr hb
  · exact lt_top_iff_ne_top.mpr ht

/-- Both actual adjacent quotients of this chain have order two. -/
theorem threeTermChain_factor_card {G : Type*} [CommGroup G] (H : Subgroup G)
    (hG : Nat.card G = 4) (hH : Nat.card H = 2) (i : Fin 2) :
    Nat.card ((threeTermChain H i.succ) ⧸
      (threeTermChain H i.castSucc).subgroupOf (threeTermChain H i.succ)) = 2 := by
  fin_cases i
  · change Nat.card (H ⧸ (⊥ : Subgroup G).subgroupOf H) = 2
    have hbot : Nat.card ((⊥ : Subgroup G).subgroupOf H) = 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (bot_le : (⊥ : Subgroup G) ≤ H)).toEquiv,
        Subgroup.card_bot]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((⊥ : Subgroup G).subgroupOf H)
    rw [hH, hbot, mul_one] at h
    exact h.symm
  · change Nat.card ((⊤ : Subgroup G) ⧸ H.subgroupOf ⊤) = 2
    have hsub : Nat.card (H.subgroupOf ⊤) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : H ≤ ⊤)).toEquiv, hH]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf ⊤)
    rw [Subgroup.card_top, hG, hsub] at h
    omega

/-- The two simple order-two quotients give a canonical shared series. -/
def orderFourSeries {G : Type*} [CommGroup G] (H : Subgroup G)
    (hG : Nat.card G = 4) (hH : Nat.card H = 2) : Series G where
  length := 2
  term := threeTermChain H
  first_eq_bot := rfl
  last_eq_top := rfl
  strictMono := threeTermChain_strict H hG hH
  normal _ := inferInstance
  simple i := isSimpleGroup_of_prime_card (threeTermChain_factor_card H hG hH i)

theorem order_four_has_two_factors (A : Type) [AddCommGroup A]
    (hA : Nat.card A = 4) : HasTwoC2Factors A := by
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hG : Nat.card (Multiplicative A) = 4 := hA
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Multiplicative A) 2 (by
    rw [hG]; decide)
  let H := Subgroup.zpowers g
  have hH : Nat.card H = 2 := (Nat.card_zpowers g).trans hg
  let s := orderFourSeries H hG hH
  refine ⟨s, rfl, fun i => ?_⟩
  exact ⟨mulEquivOfPrimeCardEq (p := 2) (threeTermChain_factor_card H hG hH i)
    (by change Nat.card (ZMod 2) = 2; exact Nat.card_zmod 2)⟩

theorem order_four_composition_factors : OrderFourCompositionFactors :=
  ⟨order_four_has_two_factors _ order_four_cardinality.1,
    order_four_has_two_factors _ order_four_cardinality.2⟩

end D07.Ch07.ClassificationIsomorphismTestInsufficientInvariants
