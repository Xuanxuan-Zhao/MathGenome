import MathGenome.Internal.Specs.D05.Foundations.Factorization
import MathGenome.Internal.D05.Foundations.IdealsGcd

/-! Factorization over any field, paper.tex:370–382. Primality is derived
from the accepted gcd/Bézout theorem. Existence uses Mathlib's normalized
factors; uniqueness uses prime-factor cancellation with that primality proof.
No splitting or characteristic assumption is imposed. -/

noncomputable section

namespace D05.Foundations.Factorization

open D05.Foundations

/-- A common divisor of an irreducible and a polynomial it does not divide
must be a unit. Monicity then makes their gcd exactly one. -/
theorem irreducibleBezout : D05.Specs.Factorization.irreducibleBezout := by
  intro K _ p a hp hpa
  obtain ⟨hg, _, hgp, hga, _, u, v, huv⟩ :=
    IdealsGcd.gcdProperties K p a (Or.inl hp.ne_zero)
  have hunit : IsUnit (monicGcd p a) :=
    (hp.isUnit_iff_not_associated_of_dvd hgp).mpr fun h => hpa (h.dvd.trans hga)
  have hg1 : monicGcd p a = 1 := hg.eq_one_of_isUnit hunit
  exact ⟨u, v, huv.symm.trans hg1⟩

/-- Multiply the Bézout identity by the other factor to obtain Euclid's lemma. -/
theorem irreduciblesPrime : D05.Specs.Factorization.irreduciblesPrime := by
  intro K _ p hp
  refine ⟨hp.ne_zero, hp.not_isUnit, ?_⟩
  intro a b hab
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · obtain ⟨u, v, huv⟩ := irreducibleBezout K p a hp hpa
    right
    have hdiv : p ∣ (u * p + v * a) * b := by
      rw [add_mul, mul_assoc v a b]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_left p u) b)
        (dvd_mul_of_dvd_right hab v)
    simpa [huv] using hdiv

theorem factorization : D05.Specs.Factorization.factorization := by
  intro K _ p hp
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors p
  have hs : ∀ q ∈ s, q.Monic ∧ Irreducible q := by
    intro q hq
    have h := (Polynomial.mem_normalizedFactors_iff hp).mp hq
    exact ⟨h.2.1, h.1⟩
  have hu : IsUnit (Polynomial.C p.leadingCoeff) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, s, hs, ?_⟩
  rw [hu]
  exact (Polynomial.leadingCoeff_mul_prod_normalizedFactors p).symm

theorem factorizationUnique : D05.Specs.Factorization.factorizationUnique := by
  intro K _ u v s t hs ht h
  have ha : Associated s.prod t.prod := by
    refine ⟨u * v⁻¹, ?_⟩
    calc
      s.prod * ((u * v⁻¹ : (Polynomial K)ˣ) : Polynomial K) =
          ((u : Polynomial K) * s.prod) * (v⁻¹ : (Polynomial K)ˣ) := by
            simp only [Units.val_mul]; ac_rfl
      _ = ((v : Polynomial K) * t.prod) * (v⁻¹ : (Polynomial K)ˣ) := by rw [h]
      _ = t.prod := by simp [mul_comm, mul_left_comm]
  have hr := prime_factors_unique
    (fun q hq => irreduciblesPrime K q (hs q hq).2)
    (fun q hq => irreduciblesPrime K q (ht q hq).2) ha
  have hst : s = t := Multiset.rel_eq.mp (hr.mono fun q hq r hr hqr =>
    Polynomial.eq_of_monic_of_associated (hs q hq).1 (ht r hr).1 hqr)
  have hn : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => (hs 0 h0).2.ne_zero rfl
  refine ⟨?_, hst⟩
  apply Units.ext
  exact mul_right_cancel₀ hn (by simpa only [← hst] using h)

theorem unitsAreConstants : D05.Specs.Factorization.unitsAreConstants := by
  intro K _ p
  constructor
  · intro hp
    obtain ⟨c, hc, hcp⟩ := Polynomial.isUnit_iff.mp hp
    exact ⟨c, hc.ne_zero, hcp.symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)

theorem emptyFactors : D05.Specs.Factorization.emptyFactors := by
  intro K _ p u s hs heq
  constructor
  · rintro rfl
    simp [heq]
  · intro hp
    apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    apply (hs q hq).2.not_isUnit
    apply isUnit_of_dvd_unit _ hp
    rw [heq]
    exact dvd_mul_of_dvd_right (Multiset.dvd_prod hq) u

theorem constantFactorization : D05.Specs.Factorization.constantFactorization := by
  intro K _ c hc
  obtain ⟨u, hu⟩ := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  exact ⟨u, hu, by simp [hu]⟩

end D05.Foundations.Factorization
