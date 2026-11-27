import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.CyclicBinomialGroup
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

namespace GaloisFormalization.IG.CyclicBinomial

open Polynomial

variable {k : Type*} [Field k]

theorem orderAtT_mul (u v : (RatFunc k)ˣ) :
    orderAtT k (u * v) = orderAtT k u + orderAtT k v := by
  let w := (Polynomial.idealX k).valuation (RatFunc k)
  change -WithZero.log (w ((u : RatFunc k) * (v : RatFunc k))) =
    -WithZero.log (w (u : RatFunc k)) + -WithZero.log (w (v : RatFunc k))
  rw [map_mul, WithZero.log_mul ((_root_.map_ne_zero w).2 u.ne_zero)
    ((_root_.map_ne_zero w).2 v.ne_zero), neg_add]

theorem orderAtT_t : orderAtT k (tUnit k) = 1 := by
  change -WithZero.log ((Polynomial.idealX k).valuation (RatFunc k) RatFunc.X) = 1
  simp

theorem dvd_of_t_zpow_eq_pow (n : ℕ) (_hn : 2 ≤ n) (i : ℤ) (x : RatFunc k)
    (hx : x ^ n = (RatFunc.X : RatFunc k) ^ i) : (n : ℤ) ∣ i := by
  let w := (Polynomial.idealX k).valuation (RatFunc k)
  have h := congrArg (fun y => -WithZero.log (w y)) hx
  change -WithZero.log (w (x ^ n)) = -WithZero.log (w ((RatFunc.X : RatFunc k) ^ i)) at h
  refine ⟨-WithZero.log (w x), ?_⟩
  simpa only [map_pow, map_zpow₀, WithZero.log_pow, WithZero.log_zpow, w,
    Polynomial.valuation_X_eq_neg_one, WithZero.log_exp, nsmul_eq_mul, zsmul_eq_mul,
    Int.cast_id, mul_neg, mul_one, neg_neg] using h.symm

theorem orderOf_tPowerClass (n : ℕ) (hn : 2 ≤ n) : orderOf (tPowerClass k n) = n := by
  let q := QuotientGroup.mk' (powMonoidHom (α := (RatFunc k)ˣ) n).range
  have pow_eq_one_iff (m : ℕ) : tPowerClass k n ^ m = 1 ↔
      ∃ u : (RatFunc k)ˣ, u ^ n = tUnit k ^ m := by
    change (q (tUnit k)) ^ m = 1 ↔ _
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_range]
    rfl
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((pow_eq_one_iff n).2 ⟨tUnit k, rfl⟩)
  · obtain ⟨u, hu⟩ := (pow_eq_one_iff _).1 (pow_orderOf_eq_one (tPowerClass k n))
    have hx := congrArg (fun a : (RatFunc k)ˣ => (a : RatFunc k)) hu
    have h := dvd_of_t_zpow_eq_pow n hn (orderOf (tPowerClass k n) : ℤ) (u : RatFunc k)
      (by simpa only [Units.val_pow_eq_pow_val, zpow_natCast, tUnit, Units.val_mk0] using hx)
    exact Int.natCast_dvd_natCast.mp h

theorem binomial_irreducible (n : ℕ) (hn : 2 ≤ n) : Irreducible (binomial k n) := by
  let f : Polynomial (Polynomial k) := X ^ n - C X
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hmonic : f.Monic := monic_X_pow_sub_C _ hnpos.ne'
  have hdeg : f.degree = n := degree_X_pow_sub_C hnpos _
  have hconst : f.coeff 0 = -(X : Polynomial k) := by simp [f, coeff_X_pow, hnpos.ne]
  have hirr : Irreducible f := by
    refine irreducible_of_eisenstein_criterion (Polynomial.idealX k).isPrime ?_ ?_ ?_ ?_
      hmonic.isPrimitive
    · rw [hmonic.leadingCoeff]
      intro h
      exact (Polynomial.idealX k).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
    · intro j hj
      rw [hdeg] at hj
      have hjn : j ≠ n := ne_of_lt (WithBot.coe_lt_coe.mp hj)
      by_cases hj0 : j = 0
      · subst j
        rw [hconst, Polynomial.idealX_span]
        exact neg_mem (Ideal.subset_span (Set.mem_singleton X))
      · simp [f, coeff_X_pow, coeff_C, hjn, hj0]
    · rw [hdeg]
      exact WithBot.coe_lt_coe.mpr hnpos
    · rw [Polynomial.idealX_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rw [hconst, dvd_neg, X_pow_dvd_iff]
      intro h
      simpa using h 1 (by decide)
  have hmap := (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc k)).mp hirr
  simpa only [f, binomial, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, RatFunc.algebraMap_X] using hmap

theorem binomial_separable (n : ℕ) (_hn : 2 ≤ n) (hunit : IsUnit (n : k)) :
    (binomial k n).Separable := by
  have hnonzero : (n : RatFunc k) ≠ 0 := by
    simpa using (hunit.map (algebraMap k (RatFunc k))).ne_zero
  exact separable_X_pow_sub_C _ hnonzero RatFunc.X_ne_zero

theorem cyclic_splitting_field (n : ℕ) (hn : 2 ≤ n) (hunit : IsUnit (n : k))
    (ζ : k) (hζ : IsPrimitiveRoot ζ n) (L : Type*) [Field L] [Algebra (RatFunc k) L]
    (hsplit : Polynomial.IsSplittingField (RatFunc k) L (binomial k n)) :
    FiniteDimensional (RatFunc k) L ∧ IsGalois (RatFunc k) L ∧
      Nonempty ((L ≃ₐ[RatFunc k] L) ≃* Multiplicative (ZMod n)) := by
  change Polynomial.IsSplittingField (RatFunc k) L (X ^ n - C RatFunc.X) at hsplit
  have : NeZero n := ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hn)⟩
  have hζ' := hζ.map_of_injective (algebraMap k (RatFunc k)).injective
  have hsep : (X ^ n - C (RatFunc.X : RatFunc k)).Separable := binomial_separable n hn hunit
  exact ⟨Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C RatFunc.X),
    IsGalois.of_separable_splitting_field hsep,
    ⟨autEquivZmod (binomial_irreducible n hn) L hζ'⟩⟩

theorem cyclic_splitting_field_extend_constants (n : ℕ) (hn : 2 ≤ n)
    (hunit : IsUnit (n : k)) (ζ : k) (hζ : IsPrimitiveRoot ζ n)
    (K : Type*) [Field K] [Algebra k K]
    (L : Type*) [Field L] [Algebra (RatFunc K) L]
    (hsplit : Polynomial.IsSplittingField (RatFunc K) L (binomial K n)) :
    FiniteDimensional (RatFunc K) L ∧ IsGalois (RatFunc K) L ∧
      Nonempty ((L ≃ₐ[RatFunc K] L) ≃* Multiplicative (ZMod n)) := by
  have hunit' : IsUnit (n : K) := by simpa using hunit.map (algebraMap k K)
  exact cyclic_splitting_field n hn hunit' (algebraMap k K ζ)
    (hζ.map_of_injective (algebraMap k K).injective) L hsplit

end GaloisFormalization.IG.CyclicBinomial
