import MathGenome.Internal.Specs.D07.Ch20.CyclotomicFiniteFactors
import MathGenome.Internal.D07.Ch13.FrobeniusRoots
import MathGenome.Internal.D07.Ch15.RootsUnity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Algebra.Squarefree.Basic

/-! Cyclotomic factors over finite fields (paper.tex:6061–6080).

The normalized factors give an exact monic, squarefree product. The
Frobenius argument also proves the degree of a primitive root in any
overfield. That root generates the concrete cyclotomic splitting field.
-/

universe u v
namespace D07.Ch20.CyclotomicFiniteFactors
open Polynomial UniqueFactorizationMonoid
open Specs.D07.Ch20.CyclotomicFiniteFactors

/-- Prime-power cardinality converts the source's gcd hypothesis into the
characteristic condition required by separability. -/
lemma natCast_ne_zero (K : Type u) [Field K] [Finite K] (m : ℕ)
    (h : (Nat.card K).Coprime m) : (m : K) ≠ 0 := by
  let := Fintype.ofFinite K
  obtain ⟨p, hchar, r, hp, hcard⟩ := FiniteField.card' K
  let := hchar
  have hpm : p.Coprime m := h.of_dvd_left (by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p r.ne_zero)
  exact fun hz => hp.not_dvd_one (hpm.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl
    ((CharP.cast_eq_zero_iff K p m).mp hz))

lemma factor_degree (K : Type u) [Field K] [Finite K] (m : ℕ)
    (h : (Nat.card K).Coprime m) (P : K[X])
    (hdvd : P ∣ cyclotomic m K) (hirr : Irreducible P) :
    P.natDegree = orderOf (Nat.card K : ZMod m) := by
  let := Fintype.ofFinite K
  obtain ⟨p, hchar, r, hp, hcard⟩ := FiniteField.card' K
  let := hchar
  let : Fact p.Prime := ⟨hp⟩
  have hpm : p.Coprime m := h.of_dvd_left (by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p r.ne_zero)
  have hd := natDegree_of_dvd_cyclotomic_of_irreducible hcard hpm hdvd hirr
  simpa only [← orderOf_units, ZMod.coe_unitOfCoprime, ← hcard,
    ← Nat.card_eq_fintype_card] using hd

theorem modular_order : ModularOrder := by
  intro q m hm hqm
  have : NeZero m := ⟨by omega⟩
  have hu := (ZMod.isUnit_iff_coprime q m).mpr hqm
  have hf := hu.isOfFinOrder
  exact ⟨hf.orderOf_pos, pow_orderOf_eq_one _, fun j hj heq =>
    orderOf_le_of_pow_eq_one hj heq⟩

theorem factorization : Factorization.{u} := by
  classical
  intro K _ _ m hm hqm
  let : NeZero (m : K) := ⟨natCast_ne_zero K m hqm⟩
  let := Fintype.ofFinite K
  let t := normalizedFactors (cyclotomic m K)
  have hnd : t.Nodup :=
    (squarefree_iff_nodup_normalizedFactors (cyclotomic_ne_zero m K)).mp
      (squarefree_cyclotomic m K)
  refine ⟨map_cyclotomic_int m K, separable_cyclotomic m K,
    t.toFinset, ?_, ?_, ?_⟩
  · obtain ⟨p, hchar, r, hp, hcard⟩ := FiniteField.card' K
    let := hchar
    let : Fact p.Prime := ⟨hp⟩
    have hpm : p.Coprime m := hqm.of_dvd_left (by
      rw [Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self p r.ne_zero)
    have hc := normalizedFactors_cyclotomic_card hcard hpm
    simpa only [← orderOf_units, ZMod.coe_unitOfCoprime, ← hcard,
      ← Nat.card_eq_fintype_card] using hc
  · have heq := leadingCoeff_mul_prod_normalizedFactors (cyclotomic m K)
    simp only [(cyclotomic.monic m K).leadingCoeff, C_1, one_mul] at heq
    rw [← heq]
    change t.prod = t.toFinset.prod id
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd, Multiset.map_id]
  · intro P hP
    have hmem : P ∈ normalizedFactors (cyclotomic m K) := Multiset.mem_toFinset.mp hP
    obtain ⟨hirr, hmon, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff
      (cyclotomic_ne_zero m K)).mp hmem
    exact ⟨hmon, hirr, factor_degree K m hqm P hdvd hirr⟩

/-- Frobenius period and modular multiplicative order are the same least
positive integer. The ambient field need not itself be finite. -/
lemma degree_of_primitive_root (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Finite K]
    (m : ℕ) (hm : 0 < m) (ζ : L) (hζ : IsPrimitiveRoot ζ m) :
    (Nat.card K).Coprime m ∧
    (minpoly K ζ).natDegree = orderOf (Nat.card K : ZMod m) ∧
    Module.finrank K (IntermediateField.adjoin K {ζ}) =
      orderOf (Nat.card K : ZMod m) := by
  have hi : IsIntegral K ζ := IsIntegral.of_pow hm (by
    rw [hζ.pow_eq_one]
    exact isIntegral_one)
  have hf := minpoly.irreducible hi
  have hn := minpoly.natDegree_pos hi
  obtain ⟨hperiod, hleast⟩ := Ch13.FrobeniusRoots.least_period
    (minpoly K ζ) ζ hf (minpoly.aeval K ζ)
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hζ.pow_eq_one⟩
  have he (j : ℕ) : ζ ^ (Nat.card K ^ j) = ζ ↔ (Nat.card K : ZMod m) ^ j = 1 := by
    nth_rewrite 2 [← pow_one ζ]
    rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_pow, Nat.cast_one]
  have hqperiod := (he _).mp hperiod
  have hqfin : IsOfFinOrder (Nat.card K : ZMod m) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hn, hqperiod⟩
  have hdeg : (minpoly K ζ).natDegree = orderOf (Nat.card K : ZMod m) :=
    le_antisymm (hleast _ hqfin.orderOf_pos ((he _).mpr (pow_orderOf_eq_one _)))
      (orderOf_le_of_pow_eq_one hn hqperiod)
  exact ⟨(ZMod.isUnit_iff_coprime _ _).mp hqfin.isUnit, hdeg,
    (IntermediateField.adjoin.finrank hi).trans hdeg⟩

theorem element_degree : ElementDegree.{u, v} := by
  intro K L _ _ _ _ _ a ha
  have hroot : IsPrimitiveRoot (a : L) (orderOf a) := by
    rw [← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  exact degree_of_primitive_root K L (orderOf a) (by omega) (a : L) hroot

/-- A primitive root generates the field containing every cyclotomic root. -/
lemma adjoin_roots_eq (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    (m : ℕ) (hm : 0 < m) (ζ : L) (hζ : IsPrimitiveRoot ζ m) :
    IntermediateField.adjoin K ((cyclotomic m K).rootSet L) =
      IntermediateField.adjoin K {ζ} := by
  have : NeZero m := ⟨hm.ne'⟩
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hxroot : IsRoot (cyclotomic m L) x := by
      rw [← map_cyclotomic m (algebraMap K L), IsRoot, eval_map_algebraMap]
      exact (mem_rootSet.mp hx).2
    have hxpow := isRoot_of_unity_of_root_cyclotomic
      (Nat.mem_divisors_self m hm.ne') hxroot
    obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hxpow
    exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ) i
  · apply IntermediateField.adjoin.mono
    intro x hx
    obtain rfl : x = ζ := Set.mem_singleton_iff.mp hx
    apply mem_rootSet.mpr
    refine ⟨cyclotomic_ne_zero m K, ?_⟩
    have hr := hζ.isRoot_cyclotomic hm
    rwa [← map_cyclotomic m (algebraMap K L), IsRoot, eval_map_algebraMap] at hr

theorem splitting_field : Specs.D07.Ch20.CyclotomicFiniteFactors.SplittingField.{u, v} := by
  intro K Ω _ _ _ _ _ m hm hqm
  have hcast := natCast_ne_zero K m hqm
  obtain ⟨ζ, hζ⟩ := Ch15.RootsUnity.primitive_root_exists K Ω m (by omega) hcast
  have hi : IsIntegral K ζ := IsIntegral.of_pow (by omega : 0 < m) (by
    rw [hζ.pow_eq_one]
    exact isIntegral_one)
  have hd := degree_of_primitive_root K Ω m (by omega) ζ hζ
  have he := adjoin_roots_eq K Ω m (by omega) ζ hζ
  dsimp only
  rw [he]
  obtain ⟨hfinite, hdegree, hcard⟩ := Ch13.FrobeniusRoots.simple_field_data
    (minpoly K ζ) ζ (minpoly.irreducible hi) (minpoly.aeval K ζ)
  refine ⟨hfinite, ?_, hd.2.2, hcard.trans (congrArg _ hd.2.1), ?_⟩
  · rw [← he]
    exact IntermediateField.adjoin_rootSet_isSplittingField
      (IsAlgClosed.splits ((cyclotomic m K).map (algebraMap K Ω)))
  · intro S hS hScard
    apply Ch13.FrobeniusRoots.embedded_field_unique
      (minpoly K ζ) ζ (minpoly.irreducible hi) (minpoly.aeval K ζ) S hS
    simpa only [hd.2.1] using hScard

theorem first_cyclotomic : FirstCyclotomic.{u} := by
  intro R _
  exact cyclotomic_one R

theorem fifth_cyclotomic : FifthCyclotomic.{u} := by
  intro R _
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  ac_rfl

private lemma order_two_mod_five : orderOf (2 : ZMod 5) = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  refine ⟨by decide, ?_⟩
  intro j hj hjpos
  have : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl <;> decide

private lemma order_four_mod_five : orderOf (4 : ZMod 5) = 2 := by
  apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
  refine ⟨by decide, ?_⟩
  intro j hj hjpos
  have : j = 1 := by omega
  subst j
  decide

theorem mod_two_example : ModTwoExample := by
  refine ⟨order_two_mod_five, ?_⟩
  apply Polynomial.irreducible_of_dvd_cyclotomic_of_natDegree
    (p := 2) (f := 1) (by simp) (by decide) dvd_rfl
  rw [natDegree_cyclotomic, ← orderOf_units, ZMod.coe_unitOfCoprime]
  simpa only [pow_one, Nat.cast_ofNat, order_two_mod_five] using (show Nat.totient 5 = 4 by decide)

theorem mod_four_example : ModFourExample.{u} := by
  refine ⟨order_four_mod_five, ?_⟩
  intro K _ _ hK
  have hcop : (Nat.card K).Coprime 5 := by rw [hK]; decide
  have ho : orderOf (Nat.card K : ZMod 5) = 2 := by
    rw [hK]
    exact order_four_mod_five
  obtain ⟨_, _, s, hcard, heq, hfactor⟩ := factorization K 5 (by decide) hcop
  rw [ho] at hcard hfactor
  refine ⟨s, ?_, heq, hfactor⟩
  simpa only [show Nat.totient 5 = 4 by decide] using hcard

theorem characteristic_multiplicity : CharacteristicMultiplicity.{u} := by
  intro K _ p _ _ m
  rw [mul_comm p m, pow_mul]
  simpa only [one_pow] using (sub_pow_char (X ^ m : K[X]) 1).symm

theorem order_one : OrderOne.{u, v} := by
  intro K L _ _ _ a ha
  have heq : a = 1 := orderOf_eq_one_iff.mp ha
  subst a
  have hm : minpoly K (1 : L) = X - 1 := minpoly.one K L
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact hm
  · change (minpoly K (1 : L)).natDegree = 1
    rw [hm]
    simpa only [C_1] using (natDegree_X_sub_C (1 : K))
  · change Module.finrank K (IntermediateField.adjoin K {(1 : L)}) = 1
    rw [IntermediateField.adjoin.finrank (isIntegral_one : IsIntegral K (1 : L)), hm]
    simpa only [C_1] using (natDegree_X_sub_C (1 : K))

end D07.Ch20.CyclotomicFiniteFactors
