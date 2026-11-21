import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.InfinityClassification
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Sphere
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SingularityCoefficients
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.TaylorSmoothness
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Operations

noncomputable section
open Set Metric Filter
open scoped Topology ENNReal

namespace D12Complex.InfinityClassification
open Laurent

/-- Inverting the variable reverses the Taylor coefficient indices. -/
private def invertedCoefficients (a : ℕ → ℂ) (n : ℤ) : ℂ :=
  if n ≤ 0 then a (-n).toNat else 0

private theorem invertedCoefficients_neg (a : ℕ → ℂ) (n : ℕ) :
    invertedCoefficients a (-(n : ℤ)) = a n := by
  simp [invertedCoefficients]

private theorem inverted_positive (a : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    positiveTerm (invertedCoefficients a) 0 n z = if n = 0 then a 0 else 0 := by
  cases n with
  | zero => simp [positiveTerm, invertedCoefficients]
  | succ n => simp [positiveTerm, invertedCoefficients]

private theorem inverted_negative (a : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    negativeTerm (invertedCoefficients a) 0 n z = a (n+1) * (z⁻¹)^(n+1) := by
  have he : -(n : ℤ) - 1 = -((n+1 : ℕ) : ℤ) := by omega
  simp only [negativeTerm, he, invertedCoefficients_neg, sub_zero, zpow_neg,
    zpow_natCast, inv_pow]

/-- This bridge only needs a convergent scalar series; no singularity
classification is hidden in the coefficient construction. -/
private theorem reciprocal_series (f : ℂ → ℂ) (a : ℕ → ℂ)
    (hs : ∀ z : ℂ, HasSum (fun n => a n * z^n) (f z)) :
    HasLaurentSeriesOn (reciprocalPullback f) 0 0 ⊤ (invertedCoefficients a) := by
  intro z hz
  have ht := hs z⁻¹
  have hp : HasSum (fun n => positiveTerm (invertedCoefficients a) 0 n z) (a 0) := by
    simp_rw [inverted_positive]
    simpa using (hasSum_ite_eq 0 (a 0))
  have hn : Summable (fun n => negativeTerm (invertedCoefficients a) 0 n z) := by
    simp_rw [inverted_negative]
    exact (summable_nat_add_iff 1).mpr ht.summable
  refine ⟨hp.summable, hn, ?_⟩
  change f z⁻¹ = _
  rw [positivePart, hp.tsum_eq, negativePart]
  simp_rw [inverted_negative]
  simpa only [Finset.sum_range_one, pow_zero, mul_one] using
    ht.summable.sum_add_tsum_nat_add 1 |>.trans ht.tsum_eq |>.symm

private theorem entire_taylor (f : ℂ → ℂ) (hf : HolomorphicOn univ f) (z : ℂ) :
    HasSum (fun n => Taylor.coefficients f 0 n * z^n) (f z) := by
  have hh : HolomorphicOn (eball (0 : ℂ) ⊤) f := by simpa using hf
  simpa using TaylorSmoothness.taylor_hasSum 0 ⊤ f (by simp) hh z (by simp)

private theorem reciprocal_holomorphic (f : ℂ → ℂ) (hf : HolomorphicOn univ f) :
    HolomorphicOn (annulus 0 0 ⊤) (reciprocalPullback f) := by
  refine ⟨?_, fun z hz => ?_⟩
  · simpa [annulus, sub_zero] using (isOpen_ne_fun continuous_id continuous_const :
      IsOpen {z : ℂ | z ≠ 0})
  · exact (hf.2 z⁻¹ (mem_univ _)).comp z
      (differentiableAt_inv_iff.mpr (norm_pos_iff.mp (by simpa using hz.1)))

private theorem entire_isolated (f : ℂ → ℂ) (hf : HolomorphicOn univ f) :
    IsolatedSingularityAtInfinity f := by
  exact SingularityCoefficients.isolated_of_holomorphic (by simp)
    (reciprocal_holomorphic f hf)

/-- A finite Taylor tail is an actual polynomial, with the original
coefficients at every index (including those beyond the truncation). -/
private theorem polynomial_of_finite_series (a : ℕ → ℂ) (m : ℕ)
    (hz : ∀ n, m < n → a n = 0) :
    ∃ p : Polynomial ℂ, (∀ n, p.coeff n = a n) ∧
      ∀ z : ℂ, HasSum (fun n => a n * z^n) (p.eval z) := by
  classical
  let p : Polynomial ℂ := ∑ n ∈ Finset.range (m+1), Polynomial.monomial n (a n)
  have hc (n : ℕ) : p.coeff n = a n := by
    dsimp [p]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      simp [hbn]
    · intro hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [hz n (by omega)]
      simp
  refine ⟨p, hc, fun z => ?_⟩
  have hs : HasSum (fun n => a n * z^n)
      (∑ n ∈ Finset.range (m+1), a n * z^n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [hz n (by
      simp only [Finset.mem_range, not_lt] at hn
      omega), zero_mul]
  convert hs using 1
  dsimp [p]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

private theorem polynomial_series (p : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => p.coeff n * z^n) (p.eval z) := by
  rw [Polynomial.eval_eq_sum_range]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
    simp only [Finset.mem_range, not_lt] at hn
    omega), zero_mul]

/-- Constants have a holomorphic extension in the reciprocal coordinate,
including the zero constant. -/
private theorem constant_removable (c : ℂ) :
    RemovableSingularityAtInfinity (fun _ => c) := by
  have hi : IsolatedSingularityAtInfinity (fun _ => c) :=
    entire_isolated _ ⟨isOpen_univ, fun _ _ => differentiableAt_const c⟩
  exact ⟨hi, 1, zero_lt_one, fun _ => c,
    ⟨isOpen_ball, fun _ _ => differentiableAt_const c⟩, fun _ _ => rfl⟩

theorem removable_iff_constant :
    Specs.D12Complex.Ch07.InfinityClassification.removable_iff_constant_type := by
  intro f hf
  constructor
  · intro hr
    let a := Taylor.coefficients f 0
    have hc := reciprocal_series f a (entire_taylor f hf)
    have hz := (SingularityCoefficients.removable_iff _ 0 ⊤ _ (by simp)
      (reciprocal_holomorphic f hf) hc).mp hr
    have ha (n : ℕ) (hn : 0 < n) : a n = 0 := by
      have h := hz (-(n : ℤ)) (by omega)
      simpa only [invertedCoefficients_neg] using h
    refine ⟨a 0, fun z => ?_⟩
    have hsum : HasSum (fun n => a n * z^n) (a 0) := by
      convert hasSum_ite_eq 0 (a 0) using 1
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, ha n (Nat.pos_of_ne_zero hn)]
    exact (entire_taylor f hf z).unique hsum
  · rintro ⟨c, hc⟩
    have heq : f = fun _ => c := funext hc
    rw [heq]
    exact constant_removable c

theorem pole_iff_polynomial_degree :
    Specs.D12Complex.Ch07.InfinityClassification.pole_iff_polynomial_degree_type := by
  intro f hf m hm
  constructor
  · intro hpo
    let a := Taylor.coefficients f 0
    have hc := reciprocal_series f a (entire_taylor f hf)
    obtain ⟨hlead, hz⟩ := (SingularityCoefficients.poleOfOrder_iff _ 0 ⊤ _ (by simp)
      (reciprocal_holomorphic f hf) hc m hm).mp hpo
    have ha (n : ℕ) (hn : m < n) : a n = 0 := by
      have h := hz (-(n : ℤ)) (by omega)
      simpa only [invertedCoefficients_neg] using h
    obtain ⟨p, hp, hs⟩ := polynomial_of_finite_series a m ha
    refine ⟨p, ?_, fun z => (entire_taylor f hf z).unique (hs z)⟩
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun n hn => (hp n).trans (ha n hn))
    · simpa only [hp, invertedCoefficients_neg] using hlead
  · rintro ⟨p, hpm, hfp⟩
    have hs (z : ℂ) : HasSum (fun n => p.coeff n * z^n) (f z) :=
      hfp z ▸ polynomial_series p z
    have hc := reciprocal_series f p.coeff hs
    apply (SingularityCoefficients.poleOfOrder_iff _ 0 ⊤ _ (by simp)
      (reciprocal_holomorphic f hf) hc m hm).mpr
    constructor
    · rw [invertedCoefficients_neg, ← hpm]
      rw [Polynomial.coeff_natDegree]
      apply Polynomial.leadingCoeff_ne_zero.mpr
      intro hp0
      simp [hp0] at hpm
      omega
    · intro n hn
      have hn0 : n ≤ 0 := by omega
      have hmn : m < (-n).toNat := by omega
      simp only [invertedCoefficients, ite_eq_left hn0]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem nonpolynomial_essential :
    Specs.D12Complex.Ch07.InfinityClassification.nonpolynomial_essential_type := by
  intro f hf hnp
  refine ⟨entire_isolated f hf, ?_, ?_⟩
  · intro hr
    obtain ⟨c, hc⟩ := (removable_iff_constant f hf).mp hr
    exact hnp ⟨Polynomial.C c, fun z => by simpa using hc z⟩
  · rintro ⟨m, hm⟩
    obtain ⟨p, _, hp⟩ := (pole_iff_polynomial_degree f hf m hm.1).mp hm
    exact hnp ⟨p, hp⟩

end D12Complex.InfinityClassification
