import MathGenome.Internal.Specs.D07.Ch11.Eisenstein
import MathGenome.Internal.D07.Ch11.GaussFractionIrreducible
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Int.Basic

/-! Eisenstein's criterion and its integer and fraction-field forms. -/

universe u v

namespace D07.Ch11.Eisenstein

open Polynomial
open Specs.D07.Ch11.Eisenstein

theorem monicCriterion : MonicCriterion.{u} := by
  intro R _ _ P f hP hf hd hc h0
  exact irreducible_of_eisenstein_criterion hP
    (by rw [hf.leadingCoeff]; exact hP.one_notMem)
    (fun i hi => hc i (coe_lt_degree.mp hi))
    (natDegree_pos_iff_degree_pos.mp hd) h0 hf.isPrimitive

theorem primitiveCriterion : PrimitiveCriterion.{u} := by
  intro R _ _ _ P f hP hf hd hl hc h0
  exact irreducible_of_eisenstein_criterion hP hl
    (fun i hi => hc i (coe_lt_degree.mp hi))
    (natDegree_pos_iff_degree_pos.mp hd) h0 hf

theorem monicFractionCriterion : MonicFractionCriterion.{u, v} := by
  intro R _ _ _ K _ _ _ P f hP hf hd hc h0
  have hi := monicCriterion R P f hP hf hd hc h0
  exact ⟨hi, (GaussFractionIrreducible.monicIrreducibleIff R K f hf).mp hi⟩

theorem primitiveFractionCriterion : PrimitiveFractionCriterion.{u, v} := by
  intro R _ _ _ K _ _ _ P f hP hf hd hl hc h0
  have hi := primitiveCriterion R P f hP hf hd hl hc h0
  exact ⟨hi, (GaussFractionIrreducible.primitiveIrreducibleIff R K f hf).mp hi⟩

theorem integerIdealConditions : IntegerIdealConditions := by
  intro p f
  dsimp
  simp only [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem integerCriterion : IntegerCriterion := by
  intro p f hp hf hd hl hc h0
  have hprim : f.IsPrimitive := hf.elim (fun h => h.isPrimitive) id
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨hl', hc', h0'⟩ := (integerIdealConditions p f).mpr ⟨hl, hc, h0⟩
  exact primitiveFractionCriterion ℤ ℚ _ f hP hprim hd hl' hc' h0'

theorem xPowSubPrime : XPowSubPrime := by
  intro p n hp hn
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let f : ℤ[X] := X ^ n - C (p : ℤ)
  have hf : f.Monic := monic_X_pow_sub_C _ hn0
  have hd : f.natDegree = n := natDegree_X_pow_sub_C
  have hl : ¬(p : ℤ) ∣ f.leadingCoeff := by
    rw [hf.leadingCoeff]
    exact hpz.not_dvd_one
  have hc (i : ℕ) (hi : i < f.natDegree) : (p : ℤ) ∣ f.coeff i := by
    have hin : i ≠ n := Nat.ne_of_lt (hd ▸ hi)
    simp only [f, coeff_sub, coeff_X_pow, ite_eq_right hin]
    by_cases hi0 : i = 0
    · subst i
      simp
    · simp [hi0]
  have h0 : ¬(p : ℤ) ^ 2 ∣ f.coeff 0 := by
    have he : f.coeff 0 = -(p : ℤ) := by
      simp [f, coeff_X_pow, Ne.symm hn0]
    rw [he, dvd_neg]
    intro h
    have h' : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ 1 := by simpa using h
    have := (pow_dvd_pow_iff hpz.ne_zero hpz.not_isUnit).mp h'
    exact (by decide : ¬(2 ≤ 1)) this
  obtain ⟨hi, hq⟩ := integerCriterion p f hp (Or.inl hf) (hd ▸ hn) hl hc h0
  refine ⟨hi, ?_⟩
  simpa [f] using hq

end D07.Ch11.Eisenstein
