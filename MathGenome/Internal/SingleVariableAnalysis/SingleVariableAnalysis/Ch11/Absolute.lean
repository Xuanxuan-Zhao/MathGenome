import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Necessary
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute

/-!
# Absolute and conditional convergence of ordinary scalar series

K03.11.absolute, paper.tex:1081–1090. The series and all tails use the
upstream ordinary inclusive partial-sum limits, for both ℝ and ℂ.
We apply the upstream scalar Cauchy criterion to the finite triangle
inequality, then pass that inequality to limits. The tail identities are
finite sum subtraction followed by the shift of an ordinary limit.
No unconditional summability predicate is substituted for ordinary convergence.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

/-- Ordinary convergence of the series of real absolute values. -/
def RealSeriesAbsolutelyConverges (a : ℕ → ℝ) : Prop :=
  RealSeriesConverges (fun n => |a n|)

/-- Ordinary convergence of the series of complex magnitudes. -/
def ComplexSeriesAbsolutelyConverges (a : ℕ → ℂ) : Prop :=
  RealSeriesConverges (fun n => ‖a n‖)

/-- Ordinary convergence without absolute convergence. -/
def RealSeriesConditionallyConverges (a : ℕ → ℝ) : Prop :=
  RealSeriesConverges a ∧ ¬ RealSeriesAbsolutelyConverges a

/-- Ordinary convergence without absolute convergence. -/
def ComplexSeriesConditionallyConverges (a : ℕ → ℂ) : Prop :=
  ComplexSeriesConverges a ∧ ¬ ComplexSeriesAbsolutelyConverges a

theorem real_absolute_converges (a : ℕ → ℝ)
    (ha : RealSeriesAbsolutelyConverges a) : RealSeriesConverges a := by
  apply (real_series_cauchy_criterion a).mpr
  intro ε hε
  obtain ⟨N, hN⟩ := (real_series_cauchy_criterion (fun n => |a n|)).mp ha ε hε
  refine ⟨N, fun p hp q hq => ?_⟩
  calc
    |∑ n ∈ Finset.Icc p q, a n| ≤ ∑ n ∈ Finset.Icc p q, |a n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ |(∑ n ∈ Finset.Icc p q, |a n|)| := le_abs_self _
    _ < ε := hN p hp q hq

theorem complex_absolute_converges (a : ℕ → ℂ)
    (ha : ComplexSeriesAbsolutelyConverges a) : ComplexSeriesConverges a := by
  apply (complex_series_cauchy_criterion a).mpr
  intro ε hε
  obtain ⟨N, hN⟩ := (real_series_cauchy_criterion (fun n => ‖a n‖)).mp ha ε hε
  refine ⟨N, fun p hp q hq => ?_⟩
  calc
    ‖∑ n ∈ Finset.Icc p q, a n‖ ≤ ∑ n ∈ Finset.Icc p q, ‖a n‖ :=
      norm_sum_le _ _
    _ ≤ |∑ n ∈ Finset.Icc p q, ‖a n‖| := le_abs_self _
    _ < ε := hN p hp q hq

/-- The finite-sum identity underlying a tail starting at p. -/
theorem sum_range_shift_eq_sub {A : Type*} [AddCommGroup A]
    (a : ℕ → A) (p N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a (n + p)) =
      (∑ n ∈ Finset.range (N + p + 1), a n) - ∑ n ∈ Finset.range p, a n := by
  have h := Finset.sum_range_add a p (N + 1)
  have he : p + (N + 1) = N + p + 1 := by omega
  rw [he] at h
  simp only [Nat.add_comm p] at h
  exact eq_sub_of_add_eq' h.symm

/-- Every ordinary convergent series has the expected sum on every tail. -/
theorem real_series_tail_hasSum (a : ℕ → ℝ) (S : ℝ)
    (ha : RealSeriesHasSum a S) (p : ℕ) :
    RealSeriesHasSum (fun n => a (n + p))
      (S - ∑ n ∈ Finset.range p, a n) := by
  apply (realSequenceConverges_iff _ _).mpr
  have h := (((realSequenceConverges_iff _ _).mp ha).comp
    (Filter.tendsto_add_atTop_nat p)).sub_const (∑ n ∈ Finset.range p, a n)
  change Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a (n + p))
    Filter.atTop (𝓝 (S - ∑ n ∈ Finset.range p, a n))
  simpa only [Function.comp_def, realPartialSum, sum_range_shift_eq_sub] using h

/-- Every ordinary convergent complex series has the expected tail sums. -/
theorem complex_series_tail_hasSum (a : ℕ → ℂ) (S : ℂ)
    (ha : ComplexSeriesHasSum a S) (p : ℕ) :
    ComplexSeriesHasSum (fun n => a (n + p))
      (S - ∑ n ∈ Finset.range p, a n) := by
  apply (complexSequenceConverges_iff _ _).mpr
  have h := (((complexSequenceConverges_iff _ _).mp ha).comp
    (Filter.tendsto_add_atTop_nat p)).sub_const (∑ n ∈ Finset.range p, a n)
  change Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a (n + p))
    Filter.atTop (𝓝 (S - ∑ n ∈ Finset.range p, a n))
  simpa only [Function.comp_def, complexPartialSum, sum_range_shift_eq_sub] using h

/-- The tail inequality holds for any specified ordinary tail-sum values. -/
theorem real_series_tail_bound (a : ℕ → ℝ) (p : ℕ) (S A : ℝ)
    (hS : RealSeriesHasSum (fun n => a (n + p)) S)
    (hA : RealSeriesHasSum (fun n => |a (n + p)|) A) : |S| ≤ A := by
  apply real_limit_le_of_eventually_le _ _ _ _ (real_abs _ _ hS) hA
  exact ⟨0, fun N _ => Finset.abs_sum_le_sum_abs _ _⟩

/-- The complex version uses modulus and the same real-valued majorant. -/
theorem complex_series_tail_bound (a : ℕ → ℂ) (p : ℕ) (S : ℂ) (A : ℝ)
    (hS : ComplexSeriesHasSum (fun n => a (n + p)) S)
    (hA : RealSeriesHasSum (fun n => ‖a (n + p)‖) A) : ‖S‖ ≤ A := by
  apply real_limit_le_of_eventually_le _ _ _ _ (complex_norm _ _ hS) hA
  exact ⟨0, fun N _ => norm_sum_le _ _⟩

/-- Absolute convergence supplies both tail sums and their bound for every p. -/
theorem real_absolute_tails (a : ℕ → ℝ)
    (ha : RealSeriesAbsolutelyConverges a) (p : ℕ) :
    ∃ S A : ℝ, RealSeriesHasSum (fun n => a (n + p)) S ∧
      RealSeriesHasSum (fun n => |a (n + p)|) A ∧ |S| ≤ A := by
  obtain ⟨S, hS⟩ := real_absolute_converges a ha
  obtain ⟨A, hA⟩ := ha
  have ht := real_series_tail_hasSum a S hS p
  have hm := real_series_tail_hasSum (fun n => |a n|) A hA p
  exact ⟨_, _, ht, hm, real_series_tail_bound a p _ _ ht hm⟩

/-- Absolute convergence supplies all complex tail sums and their modulus bound. -/
theorem complex_absolute_tails (a : ℕ → ℂ)
    (ha : ComplexSeriesAbsolutelyConverges a) (p : ℕ) :
    ∃ (S : ℂ) (A : ℝ), ComplexSeriesHasSum (fun n => a (n + p)) S ∧
      RealSeriesHasSum (fun n => ‖a (n + p)‖) A ∧ ‖S‖ ≤ A := by
  obtain ⟨S, hS⟩ := complex_absolute_converges a ha
  obtain ⟨A, hA⟩ := ha
  have ht := complex_series_tail_hasSum a S hS p
  have hm := real_series_tail_hasSum (fun n => ‖a n‖) A hA p
  exact ⟨_, _, ht, hm, complex_series_tail_bound a p _ _ ht hm⟩

end SingleVariableAnalysis
