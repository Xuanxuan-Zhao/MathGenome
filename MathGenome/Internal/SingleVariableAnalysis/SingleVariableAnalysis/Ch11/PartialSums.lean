import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.LimitAlgebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
# Ordinary series and finite changes

K03.11.partial_sums, paper.tex:979–988. Terms begin at index zero;
`partialSum a N` includes the term at N. The sum predicates below mean
ordinary convergence of this particular sequence of finite sums, and allow
conditionally convergent series. All sums are finite real or complex scalars.

The finite-correction proof uses a finite-sum identity on every tail N ≥ m.
Translation by this fixed correction preserves and reflects a finite limit.
Linearity is obtained from the upstream limit algebra and finite distributivity.
No theorem about unconditional infinite summation is used.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

/-- Finite algebra behind changing a finite prefix of a series. -/
theorem sum_range_eq_add_correction {A : Type*} [AddCommGroup A]
    (a b : ℕ → A) (m N : ℕ) (h : ∀ n, m < n → b n = a n) (hN : m ≤ N) :
    (∑ n ∈ Finset.range (N + 1), b n) =
      (∑ n ∈ Finset.range (N + 1), a n) +
        ∑ n ∈ Finset.range (m + 1), (b n - a n) := by
  have hs : (∑ n ∈ Finset.range (m + 1), (b n - a n)) =
      ∑ n ∈ Finset.range (N + 1), (b n - a n) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
    intro n _ hn
    have hmn : m < n := Nat.lt_of_succ_le (Nat.le_of_not_gt (by simpa using hn))
    rw [h n hmn, sub_self]
  rw [hs, Finset.sum_sub_distrib, add_sub_cancel]

/-- Inclusive partial sum a₀ + ⋯ + a_N. -/
noncomputable def realPartialSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), a n

/-- Ordinary series sum: the ordered partial sums have the finite limit S. -/
def RealSeriesHasSum (a : ℕ → ℝ) (S : ℝ) : Prop :=
  RealSequenceConverges (realPartialSum a) S

def RealSeriesConverges (a : ℕ → ℝ) : Prop :=
  ∃ S : ℝ, RealSeriesHasSum a S

def RealSeriesDiverges (a : ℕ → ℝ) : Prop :=
  ¬ RealSeriesConverges a

theorem real_series_hasSum_iff (a : ℕ → ℝ) (S : ℝ) :
    RealSeriesHasSum a S ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M, |((∑ n ∈ Finset.range (N + 1), a n) - S)| < ε := Iff.rfl

theorem real_series_sum_unique (a : ℕ → ℝ) (S T : ℝ)
    (hS : RealSeriesHasSum a S) (hT : RealSeriesHasSum a T) : S = T :=
  real_limit_unique (realPartialSum a) S T hS hT

theorem real_partialSum_correction (a b : ℕ → ℝ) (m : ℕ)
    (h : ∀ n, m < n → b n = a n) (N : ℕ) (hN : m ≤ N) :
    realPartialSum b N = realPartialSum a N +
      ∑ n ∈ Finset.range (m + 1), (b n - a n) :=
  sum_range_eq_add_correction a b m N h hN

/-- Every finite prefix alteration preserves the sum up to its exact correction.
Both directions concern ordinary convergence, with no condition on absolute values. -/
theorem real_series_finite_correction_iff (a b : ℕ → ℝ) (m : ℕ)
    (h : ∀ n, m < n → b n = a n) (S : ℝ) :
    RealSeriesHasSum a S ↔
      RealSeriesHasSum b (S + ∑ n ∈ Finset.range (m + 1), (b n - a n)) := by
  let C := ∑ n ∈ Finset.range (m + 1), (b n - a n)
  have he : realPartialSum b =ᶠ[Filter.atTop] (fun N => realPartialSum a N + C) :=
    Filter.eventually_atTop.mpr ⟨m, fun N hN => real_partialSum_correction a b m h N hN⟩
  change RealSequenceConverges (realPartialSum a) S ↔
    RealSequenceConverges (realPartialSum b) (S + C)
  rw [realSequenceConverges_iff, realSequenceConverges_iff]
  constructor
  · intro ha
    exact (ha.add_const C).congr' he.symm
  · intro hb
    have hh := (hb.congr' he).sub_const C
    simpa only [add_sub_cancel_right] using hh

theorem real_series_finite_changes_iff (a b : ℕ → ℝ) (m : ℕ)
    (h : ∀ n, m < n → b n = a n) :
    RealSeriesConverges a ↔ RealSeriesConverges b := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨_, (real_series_finite_correction_iff a b m h S).mp hS⟩
  · rintro ⟨T, hT⟩
    let C := ∑ n ∈ Finset.range (m + 1), (b n - a n)
    refine ⟨T - C, (real_series_finite_correction_iff a b m h (T - C)).mpr ?_⟩
    simpa only [show (∑ n ∈ Finset.range (m + 1), (b n - a n)) = C from rfl,
      sub_add_cancel] using hT

theorem real_series_add (a b : ℕ → ℝ) (S T : ℝ)
    (ha : RealSeriesHasSum a S) (hb : RealSeriesHasSum b T) :
    RealSeriesHasSum (fun n => a n + b n) (S + T) := by
  change RealSequenceConverges (fun N => ∑ n ∈ Finset.range (N + 1), (a n + b n)) (S + T)
  simp only [Finset.sum_add_distrib]
  exact real_add (realPartialSum a) (realPartialSum b) S T ha hb

theorem real_series_const_mul (a : ℕ → ℝ) (S : ℝ)
    (ha : RealSeriesHasSum a S) (c : ℝ) :
    RealSeriesHasSum (fun n => c * a n) (c * S) := by
  change RealSequenceConverges (fun N => ∑ n ∈ Finset.range (N + 1), c * a n) (c * S)
  simp only [← Finset.mul_sum]
  exact real_const_mul (realPartialSum a) S ha c

/-- Linearity for every finite family, including no terms and zero coefficients. -/
theorem real_series_finite_linearity {ι : Type} (s : Finset ι)
    (c : ι → ℝ) (a : ι → ℕ → ℝ) (S : ι → ℝ)
    (h : ∀ i ∈ s, RealSeriesHasSum (a i) (S i)) :
    RealSeriesHasSum (fun n => ∑ i ∈ s, c i * a i n) (∑ i ∈ s, c i * S i) := by
  change RealSequenceConverges _ _
  apply (realSequenceConverges_iff _ _).mpr
  have ht := tendsto_finsetSum s (fun i hi =>
    ((realSequenceConverges_iff _ _).mp (h i hi)).const_mul (c i))
  apply ht.congr
  intro N
  simp only [realPartialSum, Finset.mul_sum]
  exact Finset.sum_comm

/-- Inclusive partial sum a₀ + ⋯ + a_N. -/
noncomputable def complexPartialSum (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), a n

/-- Ordinary series sum: the ordered partial sums have the finite limit S. -/
def ComplexSeriesHasSum (a : ℕ → ℂ) (S : ℂ) : Prop :=
  ComplexSequenceConverges (complexPartialSum a) S

def ComplexSeriesConverges (a : ℕ → ℂ) : Prop :=
  ∃ S : ℂ, ComplexSeriesHasSum a S

def ComplexSeriesDiverges (a : ℕ → ℂ) : Prop :=
  ¬ ComplexSeriesConverges a

theorem complex_series_hasSum_iff (a : ℕ → ℂ) (S : ℂ) :
    ComplexSeriesHasSum a S ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M, ‖((∑ n ∈ Finset.range (N + 1), a n) - S)‖ < ε := Iff.rfl

theorem complex_series_sum_unique (a : ℕ → ℂ) (S T : ℂ)
    (hS : ComplexSeriesHasSum a S) (hT : ComplexSeriesHasSum a T) : S = T :=
  complex_limit_unique (complexPartialSum a) S T hS hT

theorem complex_partialSum_correction (a b : ℕ → ℂ) (m : ℕ)
    (h : ∀ n, m < n → b n = a n) (N : ℕ) (hN : m ≤ N) :
    complexPartialSum b N = complexPartialSum a N +
      ∑ n ∈ Finset.range (m + 1), (b n - a n) :=
  sum_range_eq_add_correction a b m N h hN

/-- Every finite prefix alteration preserves the sum up to its exact correction.
Both directions concern ordinary convergence, with no condition on absolute values. -/
theorem complex_series_finite_correction_iff (a b : ℕ → ℂ) (m : ℕ)
    (h : ∀ n, m < n → b n = a n) (S : ℂ) :
    ComplexSeriesHasSum a S ↔
      ComplexSeriesHasSum b (S + ∑ n ∈ Finset.range (m + 1), (b n - a n)) := by
  let C := ∑ n ∈ Finset.range (m + 1), (b n - a n)
  have he : complexPartialSum b =ᶠ[Filter.atTop] (fun N => complexPartialSum a N + C) :=
    Filter.eventually_atTop.mpr ⟨m, fun N hN => complex_partialSum_correction a b m h N hN⟩
  change ComplexSequenceConverges (complexPartialSum a) S ↔
    ComplexSequenceConverges (complexPartialSum b) (S + C)
  rw [complexSequenceConverges_iff, complexSequenceConverges_iff]
  constructor
  · intro ha
    exact (ha.add_const C).congr' he.symm
  · intro hb
    have hh := (hb.congr' he).sub_const C
    simpa only [add_sub_cancel_right] using hh

theorem complex_series_finite_changes_iff (a b : ℕ → ℂ) (m : ℕ)
    (h : ∀ n, m < n → b n = a n) :
    ComplexSeriesConverges a ↔ ComplexSeriesConverges b := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨_, (complex_series_finite_correction_iff a b m h S).mp hS⟩
  · rintro ⟨T, hT⟩
    let C := ∑ n ∈ Finset.range (m + 1), (b n - a n)
    refine ⟨T - C, (complex_series_finite_correction_iff a b m h (T - C)).mpr ?_⟩
    simpa only [show (∑ n ∈ Finset.range (m + 1), (b n - a n)) = C from rfl,
      sub_add_cancel] using hT

theorem complex_series_add (a b : ℕ → ℂ) (S T : ℂ)
    (ha : ComplexSeriesHasSum a S) (hb : ComplexSeriesHasSum b T) :
    ComplexSeriesHasSum (fun n => a n + b n) (S + T) := by
  change ComplexSequenceConverges (fun N => ∑ n ∈ Finset.range (N + 1), (a n + b n)) (S + T)
  simp only [Finset.sum_add_distrib]
  exact complex_add (complexPartialSum a) (complexPartialSum b) S T ha hb

theorem complex_series_const_mul (a : ℕ → ℂ) (S : ℂ)
    (ha : ComplexSeriesHasSum a S) (c : ℂ) :
    ComplexSeriesHasSum (fun n => c * a n) (c * S) := by
  change ComplexSequenceConverges (fun N => ∑ n ∈ Finset.range (N + 1), c * a n) (c * S)
  simp only [← Finset.mul_sum]
  exact complex_const_mul (complexPartialSum a) S ha c

/-- Linearity for every finite family, including no terms and zero coefficients. -/
theorem complex_series_finite_linearity {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (a : ι → ℕ → ℂ) (S : ι → ℂ)
    (h : ∀ i ∈ s, ComplexSeriesHasSum (a i) (S i)) :
    ComplexSeriesHasSum (fun n => ∑ i ∈ s, c i * a i n) (∑ i ∈ s, c i * S i) := by
  change ComplexSequenceConverges _ _
  apply (complexSequenceConverges_iff _ _).mpr
  have ht := tendsto_finsetSum s (fun i hi =>
    ((complexSequenceConverges_iff _ _).mp (h i hi)).const_mul (c i))
  apply ht.congr
  intro N
  simp only [complexPartialSum, Finset.mul_sum]
  exact Finset.sum_comm

end SingleVariableAnalysis
