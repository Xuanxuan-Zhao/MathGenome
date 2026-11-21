import MathGenome.Internal.Specs.D07.Ch09.CrtFiniteInteger
import MathGenome.Internal.D07.Ch09.ProductIntersection
import MathGenome.Internal.D07.Ch09.Comaximal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Coprime.Lemmas

/-! Finite CRT and its integer specialization, including the cofactor formula. -/

universe u v

namespace D07.Ch09.CrtFiniteInteger

open Specs.D07.Ch09.CrtFiniteInteger
open scoped BigOperators

theorem finiteCRT : FiniteCRT.{u, v} := by
  intro R _ ι _ I h
  have hc : Pairwise (fun i j => IsCoprime (I i) (I j)) :=
    fun i j hij => Ideal.isCoprime_iff_sup_eq.mpr (h i j hij)
  refine ⟨(D07.Ch09.ProductIntersection.indexedProductIntersection R ι I h).symm,
    Ideal.quotientInfRingEquivPiQuotient I hc, ?_⟩
  intro r i
  rfl

theorem integerIdealData : IntegerIdealData.{v} := by
  intro ι _ n _ hn
  have hc : ∀ i j, i ≠ j →
      Specs.D07.Ch09.Comaximal.comaximalPredicateValue
        (Ideal.span {n i}) (Ideal.span {n j}) := by
    intro i j hij
    exact (D07.Ch09.Comaximal.principalBezout ℤ (n i) (n j)).mpr
      (Int.isCoprime_iff_gcd_eq_one.mpr (hn i j hij))
  have hp : (∏ i, Ideal.span {n i}) = Ideal.span {∏ i, n i} :=
    Ideal.prod_span_singleton Finset.univ n
  exact ⟨hc, hp,
    (D07.Ch09.ProductIntersection.indexedProductIntersection ℤ ι _ hc).symm.trans hp⟩

theorem integerRingCRT : IntegerRingCRT.{v} := by
  intro ι _ n hn hc
  obtain ⟨hcomax, _, hinter⟩ := integerIdealData ι n hn hc
  obtain ⟨_, e, he⟩ := finiteCRT ℤ ι (fun i => Ideal.span {n i}) hcomax
  refine ⟨(Ideal.quotEquivOfEq hinter.symm).trans e, ?_⟩
  intro r i
  exact he r i

theorem integerExistence : IntegerExistence.{v} := by
  intro ι _ n hn hc a
  obtain ⟨e, he⟩ := integerRingCRT ι n hn hc
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (e.symm (fun i => Ideal.Quotient.mk (Ideal.span {n i}) (a i)))
  refine ⟨x, ?_⟩
  intro i
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [← he x i, hx, e.apply_symm_apply]

theorem integerUniqueness : IntegerUniqueness.{v} := by
  intro ι _ n hn hc x y
  obtain ⟨_, _, hinter⟩ := integerIdealData ι n hn hc
  have hm : (∀ i, n i ∣ x - y) ↔ x - y ∈ ⨅ i, Ideal.span {n i} := by
    simp only [Ideal.mem_iInf, Ideal.mem_span_singleton]
  rw [hm, hinter, Ideal.mem_span_singleton]

/-- Integer division by a nonzero factor gives the product of the remaining factors. -/
lemma cofactor_eq_prod_erase {ι : Type v} [Fintype ι] [DecidableEq ι]
    (n : ι → ℤ) (i : ι) (hi : n i ≠ 0) :
    (∏ j, n j) / n i = ∏ j ∈ Finset.univ.erase i, n j := by
  rw [← Finset.prod_erase_mul Finset.univ n (Finset.mem_univ i), Int.mul_ediv_cancel _ hi]

theorem cofactorData : CofactorData.{v} := by
  intro ι _ n hn hc i
  classical
  have heq := cofactor_eq_prod_erase n i (hn i).ne'
  have hcop : IsCoprime ((∏ j, n j) / n i) (n i) := by
    rw [heq]
    apply IsCoprime.prod_left
    intro j hj
    exact Int.isCoprime_iff_gcd_eq_one.mpr (hc j i (Finset.mem_erase.mp hj).1)
  refine ⟨Int.isCoprime_iff_gcd_eq_one.mp hcop, ?_, ?_⟩
  · intro j hji
    rw [heq]
    exact Finset.dvd_prod_of_mem n (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  · obtain ⟨t, s, hts⟩ := hcop
    refine ⟨t, ?_⟩
    have he : t * ((∏ j, n j) / n i) - 1 = -(s * n i) := by
      apply eq_neg_iff_add_eq_zero.mpr
      rw [sub_add_eq_add_sub, hts, sub_self]
    rw [he]
    exact dvd_neg.mpr (dvd_mul_left (n i) s)

theorem explicitSolution : ExplicitSolution.{v} := by
  intro ι _ n hn hc t ht a i
  classical
  let q := Ideal.Quotient.mk (Ideal.span {n i})
  have hinv : q (t i * ((∏ j, n j) / n i)) = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mem_span_singleton.mpr (ht i))
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  change q (∑ j, a j * t j * ((∏ k, n k) / n j)) = q (a i)
  rw [map_sum, Fintype.sum_eq_single i]
  · rw [mul_assoc, map_mul, hinv, mul_one]
  · intro j hji
    have hd : n i ∣ (∏ k, n k) / n j :=
      (cofactorData ι n hn hc j).2.1 i hji.symm
    have hz : q ((∏ k, n k) / n j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    rw [map_mul, hz, mul_zero]

end D07.Ch09.CrtFiniteInteger
