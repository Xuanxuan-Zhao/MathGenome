import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.PolynomialRoots
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.Rouche
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.PolynomialMultiplicity
import Mathlib.Tactic.Linarith

/-! Monic polynomial root counts and the coefficient radius, D12.09.04.
Rouché compares the polynomial with its leading monomial. The same direct
estimate excludes all exterior roots, giving a total count without assuming
algebraic closure. The previously proved local factorization identifies
every analytic multiplicity with its algebraic root multiplicity.
-/
noncomputable section
open Polynomial Set
open scoped BigOperators Topology

namespace D12Complex.PolynomialRoots

theorem lowerTerms_bound (P : Polynomial ℂ) (hP : P.Monic) (hn : 1 ≤ P.natDegree)
    (z : ℂ) (hz : 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < ‖z‖) :
    ‖P.eval z - z ^ P.natDegree‖ < ‖z ^ P.natDegree‖ := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ :=
    Finset.sum_nonneg (fun j hj => norm_nonneg _)
  have hz1 : 1 < ‖z‖ := lt_of_le_of_lt (by linarith) hz
  have hz0 : 0 < ‖z‖ := lt_trans zero_lt_one hz1
  have heval : P.eval z - z ^ P.natDegree =
      ∑ j ∈ Finset.range P.natDegree, P.coeff j * z ^ j := by
    rw [P.eval_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree,
      hP.leadingCoeff, one_mul, add_sub_cancel_right]
  rw [heval, norm_pow]
  calc
    ‖∑ j ∈ Finset.range P.natDegree, P.coeff j * z ^ j‖
        ≤ ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j * z ^ j‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ * ‖z‖ ^ j := by
      simp_rw [norm_mul, norm_pow]
    _ ≤ ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ * ‖z‖ ^ (P.natDegree - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply pow_le_pow_right₀ hz1.le
      exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
    _ = (∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖) * ‖z‖ ^ (P.natDegree - 1) :=
      (Finset.sum_mul _ _ _).symm
    _ < ‖z‖ * ‖z‖ ^ (P.natDegree - 1) := by
      apply mul_lt_mul_of_pos_right _ (pow_pos hz0 _)
      linarith
    _ = ‖z‖ ^ P.natDegree := by
      rw [← pow_succ', Nat.sub_add_cancel hn]

theorem root_norm_lt_radius (P : Polynomial ℂ) (hP : P.Monic) (hn : 1 ≤ P.natDegree)
    (R : ℝ) (hR : 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < R)
    (z : ℂ) (hz : P.IsRoot z) : ‖z‖ < R := by
  by_contra hnR
  have hest := lowerTerms_bound P hP hn z (hR.trans_le (not_lt.mp hnR))
  rw [Polynomial.IsRoot.def] at hz
  simp only [hz, zero_sub, norm_neg] at hest
  exact lt_irrefl _ hest


theorem multiplicity_agrees :
    Specs.D12Complex.Ch09.PolynomialRoots.multiplicity_agrees_type := by
  intro P hP a
  have ho := PolynomialMultiplicity.polynomial_order_eq_rootMultiplicity P hP.ne_zero a
  change analyticOrderAt (fun z => P.eval z) a = _ at ho
  exact ⟨PolynomialMultiplicity.polynomial_hasFiniteOrder P hP.ne_zero a,
    ho, by simp [analyticOrderNatAt, ho]⟩

lemma nat_order_eq (P : Polynomial ℂ) (hP : P.Monic) (a : ℂ) :
    analyticOrderNatAt (fun z => P.eval z) a = P.rootMultiplicity a :=
  (multiplicity_agrees P hP a).2.2

theorem roots_in_radius :
    Specs.D12Complex.Ch09.PolynomialRoots.roots_in_radius_type := by
  intro P hP hn R hR a ha
  exact root_norm_lt_radius P hP hn R hR a ha

lemma radius_pos (P : Polynomial ℂ) (R : ℝ)
    (hR : 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < R) : 0 < R := by
  have hs : 0 ≤ ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  linarith

lemma boundary_nonzero (P : Polynomial ℂ) (hP : P.Monic) (hn : 1 ≤ P.natDegree)
    (R : ℝ) (hR : 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < R) :
    ∀ a ∈ Metric.sphere (0 : ℂ) R, P.eval a ≠ 0 := by
  intro a ha hz
  have he : ‖a‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using ha
  have hl := roots_in_radius P hP hn R hR a hz
  rw [he] at hl
  exact lt_irrefl _ hl

lemma monomial_zero_count (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (s : Finset ℂ) (hs : ∀ a, a ∈ s ↔ a ∈ Metric.ball 0 R ∧ a ^ n = 0) :
    (∑ a ∈ s, analyticOrderNatAt (fun z : ℂ => z ^ n) a) = n := by
  have he : s = {0} := by
    ext a
    rw [hs, Finset.mem_singleton]
    constructor
    · intro ha
      exact (pow_eq_zero_iff (by omega)).mp ha.2
    · intro ha
      subst a
      exact ⟨by simpa using hR, zero_pow (by omega)⟩
  rw [he, Finset.sum_singleton]
  have hh := analyticOrderNatAt_pow (analyticAt_id : AnalyticAt ℂ id (0 : ℂ)) n
  simpa [Pi.pow_def, analyticOrderNatAt] using hh

lemma monomial_rouche_count (P : Polynomial ℂ) (n : ℕ) (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 < R)
    (hdom : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖P.eval z - z ^ n‖ < ‖z ^ n‖) :
    ∃ s : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ Metric.ball 0 R ∧ P.eval a = 0) ∧
      (∑ a ∈ s, analyticOrderNatAt (fun z : ℂ => P.eval z) a) = n := by
  have hmono : HolomorphicOn Set.univ (fun z : ℂ => z ^ n) :=
    ⟨isOpen_univ, fun _ _ => differentiableAt_id.pow n⟩
  obtain ⟨_, s, t, hs, ht, he⟩ := Rouche.circle Set.univ 0 R
    (fun z : ℂ => z ^ n) (fun z : ℂ => P.eval z) hR hmono
    (PolynomialMultiplicity.polynomial_holomorphic P) (subset_univ _) hdom
  refine ⟨t, ht, ?_⟩
  rw [← he]
  exact monomial_zero_count n hn R hR s hs

lemma circle_integral_of_finite_count (P : Polynomial ℂ) (R : ℝ) (hR : 0 < R)
    (havoid : ∀ z ∈ Metric.sphere (0 : ℂ) R, P.eval z ≠ 0)
    (s : Finset ℂ)
    (hs : ∀ a, a ∈ s ↔ a ∈ Metric.ball 0 R ∧ P.eval a = 0) :
    (Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_value 0 R).integral
        (fun z => deriv (fun w => P.eval w) z / P.eval z) /
        (2 * Real.pi * Complex.I : ℂ) =
      ((∑ a ∈ s, analyticOrderNatAt (fun z : ℂ => P.eval z) a : ℕ) : ℂ) := by
  let Γ := Rouche.positiveCircle 0 R
  have hidx := Rouche.circle_index_indicator (0 : ℂ) R hR
  have htrace : Γ.trace ⊆ Set.univ := subset_univ _
  have hindex : ∀ z, Γ.index z ≠ 0 → z ∈ Set.univ := fun _ _ => Set.mem_univ _
  have havoid' : ∀ z ∈ Γ.trace, P.eval z ≠ 0 := by
    intro z hz
    exact havoid z (by rwa [Rouche.positiveCircle_trace 0 R hR] at hz)
  obtain ⟨_, _, he⟩ := Rouche.holomorphic_argument_principle Set.univ Γ
    (fun z => P.eval z) (PolynomialMultiplicity.polynomial_holomorphic P)
    htrace hindex havoid'
  have hsum : (∑ᶠ a, Γ.index a *
      (analyticOrderNatAt (fun z : ℂ => P.eval z) a : ℂ)) =
      ((∑ a ∈ s, analyticOrderNatAt (fun z : ℂ => P.eval z) a : ℕ) : ℂ) := by
    rw [finsum_eq_sum_of_support_subset _ ?_]
    · simp only [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have hin := ((hs a).mp ha).1
      change (Rouche.positiveCircle 0 R).index a * _ = _
      simp [hidx a, hin]
    · intro a ha
      change Γ.index a * (analyticOrderNatAt (fun z : ℂ => P.eval z) a : ℂ) ≠ 0 at ha
      apply (hs a).mpr
      constructor
      · by_contra hn
        have hi : Γ.index a = 0 := by simpa [Γ, hn] using hidx a
        exact ha (by rw [hi, zero_mul])
      · apply apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := fun z : ℂ => P.eval z)
        intro hzero
        exact ha (by simp [hzero])
  have hout := he.trans hsum
  simpa [Γ, Rouche.positiveCircle, IntegralCycle.integral,
    IntegralChain.integral, IntegralCycle.chain, DiskCauchyFormula.circlePath, logDeriv, Pi.div_def] using hout


lemma circle_count_nat (P : Polynomial ℂ) (hP : P.Monic) (hn : 1 ≤ P.natDegree)
    (R : ℝ) (hR : 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < R) :
    ∃ s : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ Metric.ball 0 R ∧ P.eval a = 0) ∧
      (∑ a ∈ s, analyticOrderNatAt (fun z => P.eval z) a) = P.natDegree := by
  apply monomial_rouche_count P P.natDegree hn R (radius_pos P R hR)
  intro z hz
  have he : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
  apply lowerTerms_bound P hP hn z
  rwa [he]

theorem circle_count :
    Specs.D12Complex.Ch09.PolynomialRoots.circle_count_type := by
  intro P hP hn R hR
  have havoid := boundary_nonzero P hP hn R hR
  obtain ⟨s, hs, hcount⟩ := circle_count_nat P hP hn R hR
  refine ⟨havoid, ⟨s, hs, hcount, ?_⟩, ?_⟩
  · simpa only [nat_order_eq P hP] using hcount
  · rw [circle_integral_of_finite_count P R (radius_pos P R hR) havoid s hs, hcount]

/-- Rouché supplies every zero, since the radius estimate excludes exterior
zeros. The constant polynomial uses the empty set. -/
lemma finite_total_count (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ s : Finset ℂ,
      (∀ a, a ∈ s ↔ P.eval a = 0) ∧
      (∑ a ∈ s, analyticOrderNatAt (fun z => P.eval z) a) = P.natDegree := by
  classical
  by_cases hn : P.natDegree = 0
  · have hpone := eq_one_of_monic_natDegree_zero hP hn
    exact ⟨∅, by simp [hpone], by simp [hn]⟩
  have hn' : 1 ≤ P.natDegree := Nat.one_le_iff_ne_zero.mpr hn
  let R : ℝ := 2 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖
  have hR : 1 + ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖ < R := by
    dsimp [R]
    linarith
  obtain ⟨s, hs, hc⟩ := circle_count_nat P hP hn' R hR
  refine ⟨s, ?_, hc⟩
  intro a
  rw [hs]
  constructor
  · exact And.right
  · intro ha
    exact ⟨by simpa only [mem_ball_iff_norm, sub_zero] using
      roots_in_radius P hP hn' R hR a ha, ha⟩

theorem total_count :
    Specs.D12Complex.Ch09.PolynomialRoots.total_count_type := by
  intro P hP
  obtain ⟨s, hs, hc⟩ := finite_total_count P hP
  have hsupport : Function.support (fun a => analyticOrderNatAt (fun z => P.eval z) a) ⊆
      (s : Set ℂ) := by
    intro a ha
    exact (hs a).mpr (apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := fun z : ℂ => P.eval z) ha)
  refine ⟨s.finite_toSet.subset hsupport, ?_, s, hs, hc, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ hsupport]
    exact hc
  · simpa only [nat_order_eq P hP] using hc

theorem degree_zero :
    Specs.D12Complex.Ch09.PolynomialRoots.degree_zero_type := by
  intro P hP hn
  have he := eq_one_of_monic_natDegree_zero hP hn
  exact ⟨he, by simp [he], by rw [(total_count P hP).2.1, hn]⟩

end D12Complex.PolynomialRoots
