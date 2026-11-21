import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.PartialFractionInterface
import MathGenome.Internal.D07.Ch19.PartialFractions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SingleVariableAnalysis.PartialFractionInterface

open Polynomial
open scoped BigOperators

/-- Classification of a monic irreducible real polynomial, with a strict
negative discriminant in the quadratic case. -/
lemma real_irreducible_classification (p : ℝ[X]) (hm : p.Monic)
    (hi : Irreducible p) :
    (p.natDegree = 1 ∧ p = X - C (-p.coeff 0)) ∨
    (p.natDegree = 2 ∧ p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) ∧
      p.coeff 1 ^ 2 - 4 * p.coeff 0 < 0) := by
  have hp := hi.natDegree_pos
  have hq := hi.natDegree_le_two
  have hd : p.natDegree = 1 ∨ p.natDegree = 2 := by omega
  rcases hd with hd | hd
  · left
    refine ⟨hd, ?_⟩
    simpa using hm.eq_X_add_C hd
  · right
    have heq : p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      conv_lhs => rw [p.as_sum_range_C_mul_X_pow, hd]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        pow_zero, mul_one, pow_one]
      rw [← hd, hm.coeff_natDegree, C_1]
      ring
    refine ⟨hd, heq, ?_⟩
    by_contra hneg
    have hnonneg : 0 ≤ p.coeff 1 ^ 2 - 4 * p.coeff 0 := le_of_not_gt hneg
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (a := (1 : ℝ)) (b := p.coeff 1)
      (c := p.coeff 0) one_ne_zero
      ⟨Real.sqrt (p.coeff 1 ^ 2 - 4 * p.coeff 0), by
        simpa [discrim, sq] using (Real.sq_sqrt hnonneg).symm⟩
    have hroot : p.IsRoot x := by
      rw [IsRoot, heq]
      simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C, one_mul, pow_two] using hx
    have hdvd : X - C x ∣ p := (dvd_iff_isRoot).mpr hroot
    have hassoc := (irreducible_X_sub_C x).associated_of_dvd hi hdvd
    have hequal := eq_of_monic_of_associated (monic_X_sub_C x) hm hassoc
    have hdeg := congrArg Polynomial.natDegree hequal
    simp [hd] at hdeg

/-- Enumerate normalized irreducible factors once each, retaining their
positive multiplicities and the original leading coefficient. -/
lemma normalized_real_factorization (Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ (n : ℕ) (p : Fin n → ℝ[X]) (e : Fin n → ℕ),
      (∀ i, (p i).Monic) ∧ (∀ i, Irreducible (p i)) ∧
      Function.Injective p ∧ (∀ i, 0 < e i) ∧
      Q = C Q.leadingCoeff * ∏ i, p i ^ e i := by
  classical
  let m := UniqueFactorizationMonoid.normalizedFactors Q
  let s := m.toFinset
  let t : Fin s.card ≃ s := s.equivFin.symm
  let p : Fin s.card → ℝ[X] := fun i => (t i).val
  let e : Fin s.card → ℕ := fun i => m.count (p i)
  have hmem (i : Fin s.card) : p i ∈ m := Multiset.mem_toFinset.mp (t i).property
  have hf (i : Fin s.card) := (Polynomial.mem_normalizedFactors_iff hQ).mp (hmem i)
  refine ⟨s.card, p, e, fun i => (hf i).2.1, fun i => (hf i).1,
    ?_, ?_, ?_⟩
  · intro i j hij
    exact t.injective (Subtype.ext hij)
  · intro i
    exact Multiset.count_pos.mpr (hmem i)
  · have hprod : (∏ i, p i ^ e i) = m.prod := by
      rw [Finset.prod_multiset_count]
      change (∏ i, (t i).val ^ m.count (t i).val) =
        ∏ q ∈ s, q ^ m.count q
      rw [← Finset.prod_coe_sort s]
      exact Equiv.prod_comp t (fun q : s => q.val ^ m.count q.val)
    rw [hprod]
    exact (Polynomial.leadingCoeff_mul_prod_normalizedFactors Q).symm

/-- Evaluate a normalized formal decomposition by first clearing its polynomial
denominators before substituting a real argument. -/
lemma decomposition_eval {n : ℕ} {p : Fin n → ℝ[X]} {e : Fin n → ℕ}
    {f : ℝ[X]} (hm : ∀ i, (p i).Monic)
    {ha : Specs.D07.Ch19.PartialFractions.Form ℝ n e}
    (hv : Specs.D07.Ch19.PartialFractions.IsDecomposition f p e ha)
    (x : ℝ) (hx : ∀ i, (p i).eval x ≠ 0) :
    f.eval x / (Specs.D07.Ch19.PartialFractions.denominator p e).eval x =
      ha.1.eval x + ∑ i, ∑ j : Fin (e i),
        (ha.2 i j).eval x / ((p i).eval x) ^ (j.val + 1) := by
  classical
  let D := Specs.D07.Ch19.PartialFractions.denominator p e
  have hD : D.eval x = ∏ i, (p i).eval x ^ e i := by
    simp only [D, Specs.D07.Ch19.PartialFractions.denominator, eval_prod, eval_pow]
  have hD0 : D.eval x ≠ 0 := by
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))
  have hc := congrArg (fun q : ℝ[X] => q.eval x)
    (D07.Ch19.PartialFractions.clear_decomposition hm hv)
  simp only [eval_add, eval_mul, eval_pow, eval_finsetSum, eval_prod] at hc
  rw [hc, add_div, mul_div_cancel_right₀ _ hD0, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hDi : D.eval x = (p i).eval x ^ e i *
      ∏ k ∈ Finset.univ.erase i, (p k).eval x ^ e k := by
    rw [hD]
    exact (Finset.mul_prod_erase Finset.univ
      (fun k => (p k).eval x ^ e k) (Finset.mem_univ i)).symm
  apply (div_eq_div_iff hD0 (pow_ne_zero _ (hx i))).mpr
  rw [hDi, pow_sub₀ _ (hx i) (Nat.succ_le_of_lt j.isLt)]
  field_simp [hx i]

/-- Degree bounds give the constant and affine numerators of the real form. -/
lemma numerator_eval {g p : ℝ[X]} (h : g.degree < p.degree) (x : ℝ) :
    (p.natDegree = 1 → g.eval x = g.coeff 0) ∧
    (p.natDegree = 2 → g.eval x = g.coeff 1 * x + g.coeff 0) := by
  constructor
  · intro hp
    have hd : g.degree ≤ 0 := by
      have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
      rw [degree_eq_natDegree hp0, hp] at h
      exact Nat.WithBot.lt_one_iff_le_zero.mp h
    calc
      g.eval x = (C (g.coeff 0)).eval x := congrArg (eval x) (eq_C_of_degree_le_zero hd)
      _ = g.coeff 0 := eval_C
  · intro hp
    have hd : g.degree ≤ 1 := by
      have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
      rw [degree_eq_natDegree hp0, hp] at h
      by_cases hz : g = 0
      · simp [hz]
      · rw [degree_eq_natDegree hz] at h ⊢
        have hh : g.natDegree < 2 := WithBot.coe_lt_coe.mp h
        exact_mod_cast (Nat.le_of_lt_succ hh)
    have hg := eq_X_add_C_of_degree_le_one hd
    calc
      g.eval x = (C (g.coeff 1) * X + C (g.coeff 0)).eval x := congrArg (eval x) hg
      _ = g.coeff 1 * x + g.coeff 0 := by simp

/-- Every real rational function admits the displayed finite real decomposition
on the whole set where its original denominator is nonzero. -/
theorem real_partial_fractions :
    Specs.SingleVariableAnalysis.Ch09.PartialFractionInterface.RealPartialFractions := by
  classical
  intro P Q hQ
  obtain ⟨n, p, e, hm, hi, hinj, he, hfac⟩ := normalized_real_factorization Q hQ
  let f : ℝ[X] := C Q.leadingCoeff⁻¹ * P
  obtain ⟨ha, hv, _⟩ := D07.Ch19.PartialFractions.normalized_partial_fractions
    ℝ n p e f hm hi hinj he
  refine ⟨n, p, e, ha.1, (fun i j => (ha.2 i j).coeff 0),
    (fun i j => (ha.2 i j).coeff 1), (fun i j => (ha.2 i j).coeff 0),
    hm, hi, hinj, he, hfac, (fun i => real_irreducible_classification (p i) (hm i) (hi i)), ?_⟩
  intro x hx
  let D := Specs.D07.Ch19.PartialFractions.denominator p e
  have hQx : Q.eval x = Q.leadingCoeff * D.eval x := by
    conv_lhs => rw [hfac]
    simp only [eval_mul, eval_C, D, Specs.D07.Ch19.PartialFractions.denominator]
  have hD0 : D.eval x ≠ 0 := by
    intro hz
    exact hx (by rw [hQx, hz, mul_zero])
  have hbase (i : Fin n) : (p i).eval x ≠ 0 := by
    have hprod : (∏ i, (p i).eval x ^ e i) ≠ 0 := by
      simpa only [D, Specs.D07.Ch19.PartialFractions.denominator,
        eval_prod, eval_pow] using hD0
    have hh := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
    intro hz
    exact hh (by rw [hz, zero_pow (Nat.ne_of_gt (he i))])
  calc
    P.eval x / Q.eval x = f.eval x / D.eval x := by
      rw [hQx]
      simp only [f, eval_mul, eval_C]
      field_simp
    _ = ha.1.eval x + ∑ i, ∑ j : Fin (e i),
        (ha.2 i j).eval x / ((p i).eval x) ^ (j.val + 1) :=
      decomposition_eval hm hv x hbase
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rcases real_irreducible_classification (p i) (hm i) (hi i) with
        ⟨hd, hp⟩ | ⟨hd, hp, _⟩
      · simp only [hd, ↓reduceIte, show (1 : ℕ) ≠ 2 by decide, add_zero]
        apply Finset.sum_congr rfl
        intro j _
        have hnum := (numerator_eval (hv.1 i j) x).1 hd
        rw [hnum]
        congr 2
        rw [hp]
        simp
      · simp only [hd, ↓reduceIte, show (2 : ℕ) ≠ 1 by decide, zero_add]
        apply Finset.sum_congr rfl
        intro j _
        have hnum := (numerator_eval (hv.1 i j) x).2 hd
        rw [hnum]
        congr 2
        rw [hp]
        simp

end SingleVariableAnalysis.PartialFractionInterface


