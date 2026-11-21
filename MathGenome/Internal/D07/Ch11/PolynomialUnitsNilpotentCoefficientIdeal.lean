import MathGenome.Internal.Specs.D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal
import Mathlib.RingTheory.Nilpotent.Basic
import Lean.Elab.Tactic.Omega

/-! The explicit finite coefficient-ideal bound and polynomial inverses,
K07.11.polynomial_units, paper.tex:2299–2310. -/

universe u v

namespace D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal

open Polynomial
open Specs.D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal

theorem finiteFamilyIdealNilpotence : FiniteFamilyIdealNilpotence.{u, v} := by
  intro R _ ι s a e hpos hzero
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have he : 1 ≤ e i := hpos i (Finset.mem_insert_self i s)
    have hp : (Ideal.span {a i} : Ideal R) ^ e i = 0 := by
      rw [Ideal.span_singleton_pow, hzero i (Finset.mem_insert_self i s)]
      simp
    have hs : (Ideal.span (a '' (↑s : Set ι))) ^ (1 + ∑ j ∈ s, (e j - 1)) = 0 :=
      ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
        (fun j hj => hzero j (Finset.mem_insert_of_mem hj))
    have hsum := (Commute.all (Ideal.span {a i} : Ideal R)
      (Ideal.span (a '' (↑s : Set ι)))).add_pow_add_eq_zero_of_pow_eq_zero hp hs
    rw [Ideal.add_eq_sup] at hsum
    have hexp : e i + (1 + ∑ j ∈ s, (e j - 1)) - 1 =
        1 + ∑ j ∈ insert i s, (e j - 1) := by
      rw [Finset.sum_insert hi]
      omega
    rw [hexp] at hsum
    simpa only [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, Ideal.zero_eq_bot] using hsum

theorem coefficientsOfPowers : CoefficientsOfPowers.{u} := by
  intro R _ J f hf n
  induction n with
  | zero =>
    intro k
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro k
    rw [pow_succ, pow_succ, Polynomial.coeff_mul]
    exact (J ^ n * J).sum_mem fun ij _ => Ideal.mul_mem_mul (ih ij.1) (hf ij.2)

theorem polynomialPowerVanishes : PolynomialPowerVanishes.{u} := by
  intro R _ J f N hf hJ
  ext k
  have hk := coefficientsOfPowers R J f hf N k
  simpa only [hJ, Ideal.mem_bot, Polynomial.coeff_zero] using hk

/-- The nonconstant part is nilpotent because its finitely generated
coefficient ideal is nilpotent; adding the unit constant then gives a unit. -/
theorem polynomialInverse : PolynomialInverse.{u} := by
  intro R _ f hunit hnil
  classical
  let t : Polynomial R := f - C (f.coeff 0)
  have ht : ∀ k, IsNilpotent (t.coeff k) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [t]
    · simpa [t, Polynomial.coeff_sub, Polynomial.coeff_C, hk] using
        hnil k (Nat.pos_of_ne_zero hk)
  have hex : ∀ k, ∃ n : ℕ, 1 ≤ n ∧ t.coeff k ^ n = 0 := by
    intro k
    obtain ⟨n, hn⟩ := ht k
    exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), by rw [pow_succ, hn, zero_mul]⟩
  let e : ℕ → ℕ := fun k => (hex k).choose
  let J : Ideal R := Ideal.span (t.coeff '' (↑t.support : Set ℕ))
  have hJ : J ^ (1 + ∑ k ∈ t.support, (e k - 1)) = ⊥ :=
    finiteFamilyIdealNilpotence R ℕ t.support t.coeff e
      (fun k _ => (hex k).choose_spec.1) (fun k _ => (hex k).choose_spec.2)
  have hcoeff : ∀ k, t.coeff k ∈ J := by
    intro k
    by_cases hk : k ∈ t.support
    · exact Ideal.subset_span ⟨k, hk, rfl⟩
    · rw [Polynomial.notMem_support_iff.mp hk]
      exact J.zero_mem
  have htnil : IsNilpotent t :=
    ⟨_, polynomialPowerVanishes R J t _ hcoeff hJ⟩
  have hf : IsUnit f := by
    have hu := htnil.isUnit_add_left_of_commute (hunit.map C) (Commute.all _ _)
    simpa [t, add_comm, add_left_comm, sub_eq_add_neg] using hu
  obtain ⟨g, hg⟩ := hf.exists_right_inv
  exact ⟨g, hg, by rw [mul_comm]; exact hg⟩

end D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal
