import MathGenome.Internal.Specs.D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible
import MathGenome.Internal.D07.Ch20.PolynomialOrder
import Mathlib.Tactic.Linarith

universe u v
namespace D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible
open Polynomial UniqueFactorizationMonoid
open Specs.D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible

/-- The strict inequality in the two-factor step, valid also for q=2. -/
lemma two_factor_bound {q a b : ℕ} (hq : 2 ≤ q) (ha : 0 < a) (hb : 0 < b) :
    (q ^ a - 1) * (q ^ b - 1) < q ^ (a + b) - 1 := by
  have hqa : 2 ≤ q ^ a := hq.trans (Nat.le_pow ha)
  have hqb : 2 ≤ q ^ b := hq.trans (Nat.le_pow hb)
  rw [pow_add]
  have hqa' : q ^ a - 1 + 1 = q ^ a := Nat.sub_add_cancel (by omega)
  have hqb' : q ^ b - 1 + 1 = q ^ b := Nat.sub_add_cancel (by omega)
  have hprod : 1 ≤ q ^ a * q ^ b := by nlinarith
  have hp' := Nat.sub_add_cancel hprod
  nlinarith

/-- A product over positive degrees is bounded by the corresponding field order;
the bound is strict as soon as there are at least two factors. -/
lemma product_degree_bound {ι : Type*} {q : ℕ} (hq : 2 ≤ q)
    (s : Finset ι) (d : ι → ℕ) (hs : s.Nonempty) (hd : ∀ i ∈ s, 0 < d i) :
    (∏ i ∈ s, (q ^ d i - 1)) ≤ q ^ (∑ i ∈ s, d i) - 1 ∧
    (2 ≤ s.card → (∏ i ∈ s, (q ^ d i - 1)) < q ^ (∑ i ∈ s, d i) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases hne : s.Nonempty
    · have ih' := ih hne (fun i hi => hd i (Finset.mem_insert_of_mem hi))
      have hsum : 0 < ∑ i ∈ s, d i :=
        Finset.sum_pos (fun i hi => hd i (Finset.mem_insert_of_mem hi)) hne
      have hstrict : (q ^ d a - 1) * (∏ i ∈ s, (q ^ d i - 1)) <
          q ^ (d a + ∑ i ∈ s, d i) - 1 :=
        lt_of_le_of_lt (Nat.mul_le_mul_left _ ih'.1)
          (two_factor_bound hq (hd a (Finset.mem_insert_self _ _)) hsum)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact ⟨hstrict.le, fun _ => hstrict⟩
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      simp

/-- In a finite field the characteristic prime divides q, hence not q^n-1.
This is the prime-to-characteristic part of the order test. -/
lemma maximal_exponent_not_dvd_char {F : Type u} [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (p : ℕ) [CharP F p] :
    ¬p ∣ Nat.card F ^ n - 1 := by
  let := Fintype.ofFinite F
  have hq : 2 ≤ Nat.card F := by
    have h : 1 < Fintype.card F := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  have hpow : 1 ≤ Nat.card F ^ n := by
    exact (by omega : 1 ≤ Nat.card F).trans (Nat.le_pow hn)
  have hc : (Nat.card F : F) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero F
  intro h
  have he := (CharP.cast_eq_zero_iff F p _).mpr h
  rw [Nat.cast_sub hpow, Nat.cast_pow, hc, zero_pow hn.ne', Nat.cast_one, zero_sub] at he
  exact neg_ne_zero.mpr one_ne_zero he

/-- The p-part formula forces every supplied factor multiplicity to be one.
No squarefreeness assumption is made. -/
lemma multiplicities_eq_one {F : Type u} [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (p : ℕ) [Fact p.Prime] [CharP F p]
    {ι : Type*} [Fintype ι] [Nonempty ι] (g : ι → F[X]) (b : ι → ℕ)
    (f : F[X]) (hm : ∀ i, (g i).Monic) (hg : ∀ i, Irreducible (g i))
    (hinj : Function.Injective g) (hb : ∀ i, 0 < b i)
    (hfdeg : 0 < f.natDegree) (hf0 : f.eval 0 ≠ 0)
    (hfac : f = C (1 : F) * ∏ i, g i ^ b i)
    (ho : PolynomialOrder.polynomialOrder F f = Nat.card F ^ n - 1) :
    ∀ i, b i = 1 := by
  have hrep := PolynomialOrder.repeated_factor_order F p ι g b 1 f hm hg hinj hb
    one_ne_zero hfdeg hf0 hfac
  obtain ⟨t, ht, htmin⟩ := hrep.2.1
  have htzero : t = 0 := by
    by_contra h
    have hd : p ∣ PolynomialOrder.polynomialOrder F f := by
      change p ∣ Specs.D07.Ch20.PolynomialOrder.orderValue F f
      rw [(hrep.2.2 t ht htmin).1]
      exact dvd_mul_of_dvd_right (dvd_pow_self p h) _
    rw [ho] at hd
    exact maximal_exponent_not_dvd_char hn p hd
  intro i
  have hi : b i ≤ p ^ t := ht i
  have hbi := hb i
  rw [htzero, pow_zero] at hi
  omega

/-- The irreducibility part, proved using the full irreducible factorization. -/
theorem irreducible_of_maximal_order {F : Type u} [Field F] [Finite F]
    {n : ℕ} (f : F[X]) (hn : 0 < n) (hm : f.Monic) (hd : f.natDegree = n)
    (hf0 : f.eval 0 ≠ 0)
    (ho : PolynomialOrder.polynomialOrder F f = Nat.card F ^ n - 1) :
    Irreducible f := by
  classical
  let s := (normalizedFactors f).toFinset
  have hfprod : (normalizedFactors f).prod = f := by
    simpa only [hm.leadingCoeff, C_1, one_mul] using leadingCoeff_mul_prod_normalizedFactors f
  have hs : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hem : normalizedFactors f = 0 := by
      simpa only [s, Multiset.toFinset_eq_empty] using he
    rw [hem, Multiset.prod_zero] at hfprod
    have hf1 : f = 1 := hfprod.symm
    simp [hf1] at hd
    omega
  let : Nonempty ↥s := hs.to_subtype
  let g : ↥s → F[X] := fun i => i.val
  let b : ↥s → ℕ := fun i => (normalizedFactors f).count i.val
  have hgdata (i : ↥s) : Irreducible (g i) ∧ (g i).Monic ∧ g i ∣ f :=
    (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp
      (Multiset.mem_toFinset.mp i.property)
  have hgm : ∀ i, (g i).Monic := fun i => (hgdata i).2.1
  have hgi : ∀ i, Irreducible (g i) := fun i => (hgdata i).1
  have hb : ∀ i, 0 < b i := by
    intro i
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp i.property)
  have hfac : f = C (1 : F) * ∏ i : ↥s, g i ^ b i := by
    rw [C_1, one_mul]
    change f = ∏ i : ↥s, i.val ^ (normalizedFactors f).count i.val
    rw [Finset.prod_coe_sort s (fun j => j ^ (normalizedFactors f).count j)]
    exact hfprod.symm.trans (Finset.prod_multiset_count (normalizedFactors f))
  let p := ringChar F
  let : Fact p.Prime := ⟨CharP.prime_ringChar F⟩
  let : CharP F p := ringChar.charP F
  have hb1 := multiplicities_eq_one hn p g b f hgm hgi Subtype.val_injective hb
    (hd ▸ hn) hf0 hfac ho
  have hfprod' : f = ∏ i : ↥s, g i := by
    simpa only [hb1, pow_one, C_1, one_mul] using hfac
  have hgsum : ∑ i : ↥s, (g i).natDegree = n := by
    rw [← hd, hfprod', natDegree_prod_of_monic _ _ (fun i _ => hgm i)]
  have hgpos : ∀ i : ↥s, 0 < (g i).natDegree := fun i => (hgi i).natDegree_pos
  have hgo (i : ↥s) : Specs.D07.Ch20.PolynomialOrder.orderValue F (g i) ∣
      Nat.card F ^ (g i).natDegree - 1 := by
    apply PolynomialOrder.irreducible_order_bound F (g i) (hgi i)
    intro hz
    exact hf0 (eval_eq_zero_of_dvd_of_eval_eq_zero (hgdata i).2.2 hz)
  have horep := PolynomialOrder.repeated_factor_order F p ↥s g (fun _ => 1) 1 f
    hgm hgi Subtype.val_injective (fun _ => Nat.one_pos) one_ne_zero (hd ▸ hn) hf0
    (by simpa only [pow_one, C_1, one_mul] using hfprod')
  have holcm := (horep.2.2 0 (by simp) (by simp)).1
  have hodvd : PolynomialOrder.polynomialOrder F f ∣
      ∏ i : ↥s, (Nat.card F ^ (g i).natDegree - 1) := by
    change Specs.D07.Ch20.PolynomialOrder.orderValue F f ∣ _
    rw [holcm, pow_zero, mul_one]
    apply Finset.lcm_dvd
    intro i _
    exact (hgo i).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hq : 2 ≤ Nat.card F := by
    let := Fintype.ofFinite F
    have h : 1 < Fintype.card F := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  have hprodpos : 0 < ∏ i : ↥s, (Nat.card F ^ (g i).natDegree - 1) := by
    apply Finset.prod_pos
    intro i _
    have hi : 2 ≤ Nat.card F ^ (g i).natDegree := hq.trans (Nat.le_pow (hgpos i))
    omega
  have hcard : Fintype.card ↥s < 2 := by
    by_contra h
    have hbound := (product_degree_bound hq Finset.univ (fun i : ↥s => (g i).natDegree)
      (Finset.univ_nonempty) (fun i _ => hgpos i)).2 (by simp only [Finset.card_univ]; omega)
    rw [hgsum] at hbound
    rw [ho] at hodvd
    exact (not_lt_of_ge (Nat.le_of_dvd hprodpos hodvd)) hbound
  obtain ⟨i⟩ := (inferInstance : Nonempty ↥s)
  have hall : ∀ j : ↥s, j = i := by
    intro j
    have hsub : Subsingleton ↥s := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact hsub.elim _ _
  have heq : f = g i := by
    rw [hfprod']
    have hu : (Finset.univ : Finset ↥s) = {i} := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact hall j
    rw [hu, Finset.prod_singleton]
  exact heq ▸ hgi i

/-- Full assigned conclusion, with every root in every q^n-element extension. -/
theorem maximal_order_forces_irreducible : MaximalOrderForcesIrreducible.{u,v} := by
  intro F _ _ n f hn hm hd hf0 ho
  have hf : Irreducible f := irreducible_of_maximal_order f hn hm hd hf0 ho
  refine ⟨hf, ?_⟩
  intro L _ _ _ hcard a ha
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    apply hf0
    apply (algebraMap F L).injective
    simpa [Polynomial.aeval_def, coeff_zero_eq_eval_zero] using ha
  let z : Lˣ := Units.mk0 a ha0
  refine ⟨z, rfl, ?_⟩
  apply (Subgroup.zpowers z).eq_top_of_card_eq
  rw [Nat.card_zpowers, Nat.card_units, hcard]
  have hroot := PolynomialOrder.root_order F f hf (hd ▸ hn) hf0 L a ha
  change Specs.D07.Ch20.PolynomialOrder.orderValue F f = orderOf a at hroot
  calc
    orderOf z = orderOf a := orderOf_units.symm
    _ = Nat.card F ^ n - 1 := hroot.symm.trans ho

end D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible
