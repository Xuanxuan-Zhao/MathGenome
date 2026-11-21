import MathGenome.Internal.Specs.D07.Ch11.PolynomialUfd
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
Unique factorization for polynomial rings. The forward direction and the
finite-variable consequence use Mathlib's polynomial UFD theorem. For the
converse, factor a nonzero constant into polynomial primes. Each factor
divides the constant, so degree additivity makes it constant too. Evaluating
the factorization at zero gives a factorization into primes of R, including
the possible empty factorization for units.
-/

universe u v

namespace D07.Ch11.PolynomialUfd

open Polynomial
open Specs.D07.Ch11.PolynomialUfd

theorem polynomialUfdIff : PolynomialUfdIff.{u} := by
  intro R _ _
  constructor
  · intro h
    let _ : UniqueFactorizationMonoid R := h
    exact Polynomial.uniqueFactorizationMonoid
  · intro h
    let _ : UniqueFactorizationMonoid R[X] := h
    apply UniqueFactorizationMonoid.of_exists_prime_factors
    intro a ha
    have hCa : C a ≠ (0 : R[X]) := C_ne_zero.mpr ha
    obtain ⟨s, hs, he⟩ := UniqueFactorizationMonoid.exists_prime_factors (C a) hCa
    refine ⟨s.map (evalRingHom (0 : R)), ?_, ?_⟩
    · intro b hb
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hb
      have hpd : p ∣ C a := (Multiset.dvd_prod hp).trans he.dvd
      have hd : p.natDegree = 0 :=
        Nat.eq_zero_of_le_zero (by simpa only [natDegree_C] using natDegree_le_of_dvd hpd hCa)
      have hc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd
      change Prime (p.eval 0)
      rw [hc, eval_C]
      exact prime_C_iff.mp (hc ▸ hs p hp)
    · have hm := he.map (evalRingHom (0 : R))
      rw [map_multiset_prod] at hm
      simpa only [coe_evalRingHom, eval_C] using hm

theorem finiteVariablePolynomialUfd : FiniteVariablePolynomialUfd.{u, v} := by
  intro R _ _ _ σ _
  exact MvPolynomial.uniqueFactorizationMonoid σ

end D07.Ch11.PolynomialUfd
