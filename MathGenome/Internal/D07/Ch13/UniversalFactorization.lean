import MathGenome.Internal.Specs.D07.Ch13.UniversalFactorization
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Squarefree.Basic

/-! The universal splitting polynomial, K07.13.universal_factorization.
The finite-field degree criterion identifies the monic normalized factors.
The derivative -1 makes their multiset duplicate-free; its finite-set product
therefore retains the complete factorization, with no repeated factors.
-/

universe u
namespace D07.Ch13.UniversalFactorization

open Polynomial UniqueFactorizationMonoid
open Specs.D07.Ch13.UniversalFactorization

theorem irreducible_divisibility : IrreducibleDivisibility.{u} := by
  intro K _ _ q n hq _hn f hf
  subst q
  exact hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.symm

lemma defining_polynomial_separable (K : Type u) [Field K] [Finite K]
    (q n : ℕ) (hq : Nat.card K = q) (hn : 1 ≤ n) :
    (X ^ (q ^ n) - X : K[X]).Separable := by
  let := Fintype.ofFinite K
  have hqzero : (q : K) = 0 := by
    rw [← hq, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero K
  have hqnzero : ((q ^ n : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, hqzero, zero_pow (Nat.ne_zero_of_lt hn)]
  have hd : (X ^ (q ^ n) - X : K[X]).derivative = -1 := by
    simp [derivative_sub, derivative_X_pow, hqnzero]
  rw [Polynomial.separable_def, hd]
  exact isCoprime_one_right.neg_right

theorem universal_factorization : Factorization.{u} := by
  intro K _ _ q n hq hn
  classical
  let P : K[X] := X ^ (q ^ n) - X
  have hq1 : 1 < q := hq ▸ Finite.one_lt_card
  have hqn : 1 < q ^ n := Nat.one_lt_pow (Nat.ne_zero_of_lt hn) hq1
  have hm : P.Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hqn)
  have hP : P ≠ 0 := hm.ne_zero
  have hnodup : (normalizedFactors P).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hP).mp
      (defining_polynomial_separable K q n hq hn).squarefree
  refine ⟨(normalizedFactors P).toFinset, ?_, ?_⟩
  · intro f
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hP]
    have hd := irreducible_divisibility K q n hq hn f
    constructor
    · rintro ⟨hi, hmonic, hdvd⟩
      exact ⟨hmonic, hi, (hd hi).mp hdvd⟩
    · rintro ⟨hmonic, hi, hdvd⟩
      exact ⟨hi, hmonic, (hd hi).mpr hdvd⟩
  · change P = ∏ f ∈ (normalizedFactors P).toFinset, f
    rw [← Multiset.toFinset_eq hnodup, Finset.prod_mk]
    simpa using ((prod_normalizedFactors_eq hP).trans hm.normalize_eq_self).symm

end D07.Ch13.UniversalFactorization
