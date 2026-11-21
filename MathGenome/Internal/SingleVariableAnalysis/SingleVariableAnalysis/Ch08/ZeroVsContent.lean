import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.ZeroVsContent
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.ZeroCovers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ClosedPreimage
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Countable length zero differs from finite content zero

K03.08.zero_vs_content. We use countability for the countable-cover assertion.
Rational density gives closure equal to [0,1]. A finite union of closed
intervals is closed, so a finite cover of the rational points by closed
intervals covers [0,1]. Enlarging the closed intervals by arbitrarily small
amounts reduces their length inequality to the upstream open-cover inequality.
This uses no measure or integration representation.
-/
namespace SingleVariableAnalysis

open Set
open scoped BigOperators

/-- The rational points of the real closed unit interval. -/
def rationalUnitInterval : Set ℝ :=
  Set.range (fun q : ℚ => (q : ℝ)) ∩ Icc 0 1

/-- Arbitrarily small finite open bounded interval covers. -/
def FiniteContentZero (E : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℕ) (a b : ℕ → ℝ),
    (∀ i ∈ s, a i < b i) ∧ E ⊆ ⋃ i ∈ s, Ioo (a i) (b i) ∧
      (∑ i ∈ s, (b i - a i)) < ε

theorem rationalUnitInterval_lengthZero : LengthZero rationalUnitInterval := by
  apply lengthZero_countable
  exact (Set.countable_range (fun q : ℚ => (q : ℝ))).mono inter_subset_left

/-- The endpoints are included by taking the closure of the open interval. -/
theorem closure_rationalUnitInterval :
    closure rationalUnitInterval = Icc (0 : ℝ) 1 := by
  apply subset_antisymm
  · exact closure_minimal inter_subset_right isClosed_Icc
  · have hinterior : Ioo (0 : ℝ) 1 ⊆ closure rationalUnitInterval := by
      intro x hx
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      have hgap : max 0 (x - ε) < min 1 (x + ε) := by
        apply max_lt
        · exact lt_min (by norm_num) (by linarith [hx.1])
        · exact lt_min (by linarith [hx.2]) (by linarith)
      obtain ⟨q, hqlo, hqhi⟩ := rational_density _ _ hgap
      have hq0 : 0 < (q : ℝ) := (le_max_left _ _).trans_lt hqlo
      have hq1 : (q : ℝ) < 1 := hqhi.trans_le (min_le_left _ _)
      have hqleft : x - ε < (q : ℝ) := (le_max_right _ _).trans_lt hqlo
      have hqright : (q : ℝ) < x + ε := hqhi.trans_le (min_le_right _ _)
      refine ⟨(q : ℝ), ⟨⟨q, rfl⟩, hq0.le, hq1.le⟩, ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h := closure_minimal hinterior isClosed_closure
    simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using h

/-- Closed intervals have the same finite-cover length bound as open ones. -/
theorem finite_closed_interval_cover_length (s : Finset ℕ) (a b : ℕ → ℝ) (c d : ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hcover : Icc c d ⊆ ⋃ i ∈ s, Icc (a i) (b i)) :
    d - c ≤ ∑ i ∈ s, (b i - a i) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (2 * ((s.card : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (2 * ((s.card : ℝ) + 1)) = ε := by
    exact div_mul_cancel₀ _ (by positivity)
  have hopen : Icc c d ⊆ ⋃ i ∈ s, Ioo (a i - δ) (b i + δ) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ s, x ∈ Icc (a i) (b i) := by
      simpa only [mem_iUnion, exists_prop] using hcover hx
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, ?_⟩⟩
    constructor <;> linarith [hxi.1, hxi.2]
  have h := finite_interval_cover_length s (fun i => a i - δ) (fun i => b i + δ)
    c d (fun i hi => by linarith [hab i hi]) hopen
  have hsum : (∑ i ∈ s, (b i + δ - (a i - δ))) =
      (∑ i ∈ s, (b i - a i)) + (s.card : ℝ) * (2 * δ) := by
    simp_rw [show ∀ i, b i + δ - (a i - δ) = (b i - a i) + 2 * δ by
      intro i; ring]
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum] at h
  nlinarith

/-- Closing a finite cover forces it to cover the whole unit interval. -/
theorem rationalUnitInterval_finite_closed_cover_length
    (s : Finset ℕ) (a b : ℕ → ℝ) (hab : ∀ i ∈ s, a i ≤ b i)
    (hcover : rationalUnitInterval ⊆ ⋃ i ∈ s, Icc (a i) (b i)) :
    1 ≤ ∑ i ∈ s, (b i - a i) := by
  have hclosed : IsClosed (⋃ i ∈ s, Icc (a i) (b i)) :=
    isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  have hfull := closure_minimal hcover hclosed
  rw [closure_rationalUnitInterval] at hfull
  simpa using finite_closed_interval_cover_length s a b 0 1 hab hfull

/-- Any endpoint convention is allowed, since each covering set lies in
its closed interval hull with the same length. -/
theorem rationalUnitInterval_finite_cover_length
    (s : Finset ℕ) (a b : ℕ → ℝ) (J : ℕ → Set ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hJ : ∀ i ∈ s, J i ⊆ Icc (a i) (b i))
    (hcover : rationalUnitInterval ⊆ ⋃ i ∈ s, J i) :
    1 ≤ ∑ i ∈ s, (b i - a i) := by
  apply rationalUnitInterval_finite_closed_cover_length s a b hab
  exact hcover.trans (iUnion_mono fun i => iUnion_mono fun hi => hJ i hi)

theorem rationalUnitInterval_finite_open_cover_length
    (s : Finset ℕ) (a b : ℕ → ℝ) (hab : ∀ i ∈ s, a i ≤ b i)
    (hcover : rationalUnitInterval ⊆ ⋃ i ∈ s, Ioo (a i) (b i)) :
    1 ≤ ∑ i ∈ s, (b i - a i) := by
  apply rationalUnitInterval_finite_closed_cover_length s a b hab
  exact hcover.trans (iUnion_mono fun _ => iUnion_mono fun _ => Ioo_subset_Icc_self)

theorem rationalUnitInterval_not_finiteContentZero :
    ¬ FiniteContentZero rationalUnitInterval := by
  intro h
  obtain ⟨s, a, b, hab, hcover, hsum⟩ := h 1 zero_lt_one
  exact (not_lt_of_ge (rationalUnitInterval_finite_open_cover_length s a b
    (fun i hi => (hab i hi).le) hcover)) hsum

theorem lengthZero_not_finiteContentZero :
    ∃ E : Set ℝ, LengthZero E ∧ ¬ FiniteContentZero E :=
  ⟨rationalUnitInterval, rationalUnitInterval_lengthZero,
    rationalUnitInterval_not_finiteContentZero⟩

end SingleVariableAnalysis
