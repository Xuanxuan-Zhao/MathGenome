import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.HermiteAlgebra
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas

namespace NumAnalysis206.Approximation

open Polynomial
open scoped BigOperators

/-- A Bézout construction of simultaneous polynomial congruences. -/
theorem exists_polynomial_residues {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (q a : ι → K[X]) (hq : Pairwise (fun i j => IsCoprime (q i) (q j))) :
    ∃ b : K[X], ∀ i, q i ∣ b - a i := by
  classical
  let Q (i : ι) := ∏ j ∈ Finset.univ.erase i, q j
  have hc (i : ι) : IsCoprime (Q i) (q i) := by
    apply IsCoprime.prod_left
    intro j hj
    exact hq (Finset.mem_erase.mp hj).1
  choose u v huv using hc
  let b := ∑ i, a i * (u i * Q i)
  refine ⟨b, fun i => ?_⟩
  have hterm (j : ι) :
      q i ∣ a j * (u j * Q j) - (if j = i then a i else 0) := by
    by_cases hji : j = i
    · subst j
      simp only [ite_true]
      refine ⟨-(a i * v i), ?_⟩
      calc
        a i * (u i * Q i) - a i = a i * (u i * Q i - 1) := by ring
        _ = a i * (-(v i * q i)) := by
          congr 1
          rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, huv i, sub_self]
        _ = q i * -(a i * v i) := by ring
    · simp only [ite_eq_right hji, sub_zero]
      have hd : q i ∣ Q j := Finset.dvd_prod_of_mem q (Finset.mem_erase.mpr
        ⟨Ne.symm hji, Finset.mem_univ i⟩)
      simpa only [mul_assoc] using hd.mul_left (a j * u j)
  have hd := Finset.dvd_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hterm j)
  simpa [Finset.sum_sub_distrib, b] using hd

/-- The arbitrary-characteristic algebraic part of Hermite interpolation (W51). -/
theorem hermite_residue_interpolation : Specs.HermiteResidueInterpolation := by
  intro K _ s hs x hx m hm a
  classical
  let q : Fin s → K[X] := fun i => (X - C (x i)) ^ m i
  have hcop : Pairwise (fun i j => IsCoprime (q i) (q j)) := by
    intro i j hij
    exact (pairwise_coprime_X_sub_C hx hij).pow
  obtain ⟨b, hb⟩ := exists_polynomial_residues q a hcop
  let P := ∏ i, q i
  have hmon : P.Monic := by
    exact monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (x i)).pow (m i))
  have hdeg : P.natDegree = ∑ i, m i := by
    dsimp [P, q]
    rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (x i)).pow (m i))]
    simp
  have hdegree : P.degree = (↑(∑ i, m i) : WithBot ℕ) := by
    rw [degree_eq_natDegree hmon.ne_zero, hdeg]
  refine ⟨b %ₘ P, ⟨?_, ?_⟩, ?_⟩
  · rw [← hdegree]
    exact degree_modByMonic_lt b hmon
  · intro i
    change q i ∣ b %ₘ P - a i
    have hdiv : q i ∣ P := Finset.dvd_prod_of_mem q (Finset.mem_univ i)
    have hd := dvd_add (hdiv.trans (dvd_modByMonic_sub b P)) (hb i)
    simpa only [sub_add_sub_cancel] using hd
  · intro p hp
    apply sub_eq_zero.mp
    have hd : P ∣ p - b %ₘ P := by
      apply Fintype.prod_dvd_of_coprime hcop
      intro i
      have hdiv : q i ∣ P := Finset.dvd_prod_of_mem q (Finset.mem_univ i)
      have hr := dvd_add (hdiv.trans (dvd_modByMonic_sub b P)) (hb i)
      have hr' : q i ∣ b %ₘ P - a i := by simpa only [sub_add_sub_cancel] using hr
      simpa only [sub_sub_sub_cancel_right] using dvd_sub (hp.2 i) hr'
    apply eq_zero_of_dvd_of_degree_lt hd
    rw [hdegree]
    exact (degree_sub_le _ _).trans_lt (max_lt hp.1 (by
      rw [← hdegree]
      exact degree_modByMonic_lt b hmon))

end NumAnalysis206.Approximation
