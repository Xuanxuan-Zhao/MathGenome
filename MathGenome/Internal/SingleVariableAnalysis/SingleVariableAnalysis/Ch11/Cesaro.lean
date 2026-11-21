import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cesaro
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Cesaro

/-!
# Cesàro sums of series

K03.11.cesaro (paper.tex:1160–1169). The mean averages the inclusive
ordinary partial sums, rather than the terms. Ordinary convergence implies
Cesàro convergence by applying the sequence Cesàro theorem to partial sums.
For Grandi's series the exact identity s_N = (1 + (-1)^N)/2 reduces the
Cesàro limit to the null arithmetic means of the alternating sequence.
The even and odd partial sums are 1 and 0, proving ordinary divergence.
-/
namespace SingleVariableAnalysis
open scoped BigOperators Topology

noncomputable def realSeriesCesaroMean (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (N + 1), realPartialSum a j

def RealSeriesCesaroHasSum (a : ℕ → ℝ) (S : ℝ) : Prop :=
  RealSequenceConverges (realSeriesCesaroMean a) S

def RealSeriesCesaroConverges (a : ℕ → ℝ) : Prop :=
  ∃ S, RealSeriesCesaroHasSum a S

noncomputable def complexSeriesCesaroMean (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ((N : ℂ) + 1)⁻¹ * ∑ j ∈ Finset.range (N + 1), complexPartialSum a j

def ComplexSeriesCesaroHasSum (a : ℕ → ℂ) (S : ℂ) : Prop :=
  ComplexSequenceConverges (complexSeriesCesaroMean a) S

def ComplexSeriesCesaroConverges (a : ℕ → ℂ) : Prop :=
  ∃ S, ComplexSeriesCesaroHasSum a S

theorem real_ordinary_implies_cesaro (a : ℕ → ℝ) (S : ℝ)
    (h : RealSeriesHasSum a S) : RealSeriesCesaroHasSum a S :=
  real_cesaro (realPartialSum a) S h

theorem complex_ordinary_implies_cesaro (a : ℕ → ℂ) (S : ℂ)
    (h : ComplexSeriesHasSum a S) : ComplexSeriesCesaroHasSum a S :=
  complex_cesaro (complexPartialSum a) S h

theorem real_series_cesaro_sum_unique (a : ℕ → ℝ) (S T : ℝ)
    (hS : RealSeriesCesaroHasSum a S) (hT : RealSeriesCesaroHasSum a T) : S = T :=
  real_limit_unique _ _ _ hS hT

theorem complex_series_cesaro_sum_unique (a : ℕ → ℂ) (S T : ℂ)
    (hS : ComplexSeriesCesaroHasSum a S) (hT : ComplexSeriesCesaroHasSum a T) : S = T :=
  complex_limit_unique _ _ _ hS hT

/-- The inclusive partial sums of Grandi's series. -/
theorem real_alternating_series_partialSum (N : ℕ) :
    realPartialSum (fun n => (-1 : ℝ)^n) N = (1 + (-1 : ℝ)^N)/2 := by
  induction N with
  | zero => norm_num [realPartialSum]
  | succ N ih =>
    simp only [realPartialSum, Finset.sum_range_succ] at ih ⊢
    rw [pow_succ, ih]
    ring

theorem real_alternating_series_cesaro :
    RealSeriesCesaroHasSum (fun n => (-1 : ℝ)^n) (1/2) := by
  have hAlt : RealSequenceConverges
      (fun N => ((N : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (N + 1), (-1 : ℝ)^j) 0 := by
    have h := real_const_mul _ _ alternating_cesaro (-1)
    convert h using 1
    · funext N
      simp only [pow_succ, ← Finset.sum_mul]
      ring
    · ring
  have h := real_add _ _ _ _
    ((realSequenceConverges_iff _ _).mpr
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1/2 : ℝ)) _ _))
    (real_const_mul _ _ hAlt (1/2))
  have hEq : ∀ N, realSeriesCesaroMean (fun n => (-1 : ℝ)^n) N =
      1/2 + 1/2 * (((N : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (N + 1), (-1 : ℝ)^j) := by
    intro N
    simp only [realSeriesCesaroMean, real_alternating_series_partialSum,
      div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  change RealSequenceConverges _ _
  convert h using 1
  · funext N
    exact hEq N
  · ring

theorem real_alternating_series_diverges :
    RealSeriesDiverges (fun n => (-1 : ℝ)^n) := by
  rintro ⟨S, hS⟩
  have h := (realSequenceConverges_iff _ _).mp hS
  have he : StrictMono (fun n : ℕ => 2*n) := by intro a b hab; dsimp; omega
  have ho : StrictMono (fun n : ℕ => 2*n+1) := by intro a b hab; dsimp; omega
  have hp : (fun n => realPartialSum (fun k => (-1 : ℝ)^k) (2*n)) = fun _ => 1 := by
    funext n
    rw [real_alternating_series_partialSum, Even.neg_one_pow ⟨n, by omega⟩]
    norm_num
  have hz : (fun n => realPartialSum (fun k => (-1 : ℝ)^k) (2*n+1)) = fun _ => 0 := by
    funext n
    rw [real_alternating_series_partialSum, Odd.neg_one_pow ⟨n, rfl⟩]
    norm_num
  have h1 : S = 1 := tendsto_nhds_unique
    (by simpa only [Function.comp_def, hp] using h.comp he.tendsto_atTop)
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1))
  have h0 : S = 0 := tendsto_nhds_unique
    (by simpa only [Function.comp_def, hz] using h.comp ho.tendsto_atTop)
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
  linarith

/-- Casting real terms to complex numbers commutes with both finite sums. -/
theorem complex_series_cesaroMean_ofReal (a : ℕ → ℝ) (N : ℕ) :
    complexSeriesCesaroMean (fun n => (a n : ℂ)) N = (realSeriesCesaroMean a N : ℂ) := by
  simp [complexSeriesCesaroMean, realSeriesCesaroMean, complexPartialSum, realPartialSum,
    Complex.ofReal_sum]

theorem complex_alternating_series_cesaro :
    ComplexSeriesCesaroHasSum (fun n => (-1 : ℂ)^n) (1/2) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((realSequenceConverges_iff _ _).mp real_alternating_series_cesaro)
  apply (complexSequenceConverges_iff _ _).mpr
  simpa only [Function.comp_def, ← complex_series_cesaroMean_ofReal,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat] using h

theorem complex_alternating_series_diverges :
    ComplexSeriesDiverges (fun n => (-1 : ℂ)^n) := by
  rintro ⟨S, hS⟩
  apply real_alternating_series_diverges
  refine ⟨S.re, (realSequenceConverges_iff _ _).mpr ?_⟩
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    ((complexSequenceConverges_iff _ _).mp hS)
  change Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), (-1 : ℝ)^n) _ _
  simpa only [Function.comp_def, complexPartialSum, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, ← Complex.ofReal_one, ← Complex.ofReal_sum, Complex.ofReal_re] using h

theorem real_cesaro_not_ordinary :
    ∃ a : ℕ → ℝ, RealSeriesCesaroConverges a ∧ ¬ RealSeriesConverges a :=
  ⟨_, ⟨1/2, real_alternating_series_cesaro⟩, real_alternating_series_diverges⟩

theorem complex_cesaro_not_ordinary :
    ∃ a : ℕ → ℂ, ComplexSeriesCesaroConverges a ∧ ¬ ComplexSeriesConverges a :=
  ⟨_, ⟨1/2, complex_alternating_series_cesaro⟩, complex_alternating_series_diverges⟩

end SingleVariableAnalysis
