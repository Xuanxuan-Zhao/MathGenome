import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import Mathlib.Data.PNat.Basic

/-! Independent specification of K03.12.series, paper.tex:1269–1275.
Series use indices starting at zero and inclusive partial sums. Domains are
arbitrary types (subsets are represented by subtypes). Normal convergence means
ordinary convergence of the numerical series of the exact nonnegative suprema.
The inserted zero fixes the empty-domain convention; an unbounded term has no
finite IsLUB and therefore cannot satisfy this predicate. No boundedness or
absolute convergence is required for the ordinary function-series predicates.
The diagonal example has positive natural domain and zero zeroth term. -/

namespace Specs.SingleVariableAnalysis.Ch12.Series

open scoped BigOperators

universe u

noncomputable def realFunctionPartialSumType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → ℕ → E → ℝ

noncomputable def realFunctionPartialSumValue : realFunctionPartialSumType :=
  fun u N x => ∑ n ∈ Finset.range (N + 1), u n x

noncomputable def RealFunctionSeriesPointwiseHasSumType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → (E → ℝ) → Prop

noncomputable def RealFunctionSeriesPointwiseHasSumValue : RealFunctionSeriesPointwiseHasSumType :=
  fun u f => Pointwise.realPointwiseConvergesValue (realFunctionPartialSumValue u) f

noncomputable def RealFunctionSeriesPointwiseConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → Prop

noncomputable def RealFunctionSeriesPointwiseConvergesValue : RealFunctionSeriesPointwiseConvergesType :=
  fun u => ∃ f, RealFunctionSeriesPointwiseHasSumValue u f

noncomputable def RealFunctionSeriesUniformHasSumType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → (E → ℝ) → Prop

noncomputable def RealFunctionSeriesUniformHasSumValue : RealFunctionSeriesUniformHasSumType :=
  fun u f => Uniform.realUniformConvergesValue (realFunctionPartialSumValue u) f

noncomputable def RealFunctionSeriesUniformConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → Prop

noncomputable def RealFunctionSeriesUniformConvergesValue : RealFunctionSeriesUniformConvergesType :=
  fun u => ∃ f, RealFunctionSeriesUniformHasSumValue u f

noncomputable def RealFunctionSeriesUniformAbsoluteConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → Prop

noncomputable def RealFunctionSeriesUniformAbsoluteConvergesValue : RealFunctionSeriesUniformAbsoluteConvergesType :=
  fun u => RealFunctionSeriesUniformConvergesValue (fun n x => |u n x|)

noncomputable def RealFunctionSeriesNormallyConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → Prop

noncomputable def RealFunctionSeriesNormallyConvergesValue : RealFunctionSeriesNormallyConvergesType :=
  fun u => ∃ M : ℕ → ℝ, (∀ n, IsLUB (insert 0 (Set.range (fun x => |u n x|))) (M n)) ∧ Ch11.PartialSums.realSeriesConvergesValue M

noncomputable def complexFunctionPartialSumType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → ℕ → E → ℂ

noncomputable def complexFunctionPartialSumValue : complexFunctionPartialSumType :=
  fun u N x => ∑ n ∈ Finset.range (N + 1), u n x

noncomputable def ComplexFunctionSeriesPointwiseHasSumType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → (E → ℂ) → Prop

noncomputable def ComplexFunctionSeriesPointwiseHasSumValue : ComplexFunctionSeriesPointwiseHasSumType :=
  fun u f => Pointwise.complexPointwiseConvergesValue (complexFunctionPartialSumValue u) f

noncomputable def ComplexFunctionSeriesPointwiseConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → Prop

noncomputable def ComplexFunctionSeriesPointwiseConvergesValue : ComplexFunctionSeriesPointwiseConvergesType :=
  fun u => ∃ f, ComplexFunctionSeriesPointwiseHasSumValue u f

noncomputable def ComplexFunctionSeriesUniformHasSumType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → (E → ℂ) → Prop

noncomputable def ComplexFunctionSeriesUniformHasSumValue : ComplexFunctionSeriesUniformHasSumType :=
  fun u f => Uniform.complexUniformConvergesValue (complexFunctionPartialSumValue u) f

noncomputable def ComplexFunctionSeriesUniformConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → Prop

noncomputable def ComplexFunctionSeriesUniformConvergesValue : ComplexFunctionSeriesUniformConvergesType :=
  fun u => ∃ f, ComplexFunctionSeriesUniformHasSumValue u f

noncomputable def ComplexFunctionSeriesUniformAbsoluteConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → Prop

noncomputable def ComplexFunctionSeriesUniformAbsoluteConvergesValue : ComplexFunctionSeriesUniformAbsoluteConvergesType :=
  fun u => RealFunctionSeriesUniformConvergesValue (fun n x => ‖u n x‖)

noncomputable def ComplexFunctionSeriesNormallyConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → Prop

noncomputable def ComplexFunctionSeriesNormallyConvergesValue : ComplexFunctionSeriesNormallyConvergesType :=
  fun u => ∃ M : ℕ → ℝ, (∀ n, IsLUB (insert 0 (Set.range (fun x => ‖u n x‖))) (M n)) ∧ Ch11.PartialSums.realSeriesConvergesValue M


noncomputable def constantAlternatingHarmonicType : Type (u + 1) :=
  {E : Type u} → ℕ → E → ℝ

noncomputable def constantAlternatingHarmonicValue : constantAlternatingHarmonicType :=
  fun n _ => (-1 : ℝ) ^ n / ((n : ℝ) + 1)

noncomputable def diagonalHarmonicType : Type := ℕ → ℕ+ → ℝ

noncomputable def diagonalHarmonicValue : diagonalHarmonicType :=
  fun n k => if n = (k : ℕ) then 1 / (n : ℝ) else 0

/-- Full expected proposition for `real_function_series_pointwise_iff`. -/
noncomputable def real_function_series_pointwise_iff : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℝ) (f : E → ℝ),
  RealFunctionSeriesPointwiseHasSumValue u f ↔
      ∀ x, Ch11.PartialSums.realSeriesHasSumValue (fun n => u n x) (f x)

/-- Full expected proposition for `complex_function_series_pointwise_iff`. -/
noncomputable def complex_function_series_pointwise_iff : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℂ) (f : E → ℂ),
  ComplexFunctionSeriesPointwiseHasSumValue u f ↔
      ∀ x, Ch11.PartialSums.complexSeriesHasSumValue (fun n => u n x) (f x)

/-- Full expected proposition for `real_function_series_uniform_pointwise`. -/
noncomputable def real_function_series_uniform_pointwise : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℝ) (f : E → ℝ)
    (_h : RealFunctionSeriesUniformHasSumValue u f),
  RealFunctionSeriesPointwiseHasSumValue u f

/-- Full expected proposition for `complex_function_series_uniform_pointwise`. -/
noncomputable def complex_function_series_uniform_pointwise : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℂ) (f : E → ℂ)
    (_h : ComplexFunctionSeriesUniformHasSumValue u f),
  ComplexFunctionSeriesPointwiseHasSumValue u f

/-- Full expected proposition for `constant_alternating_harmonic_separation`. -/
noncomputable def constant_alternating_harmonic_separation : Prop :=
  ∀ (E : Type u) [Nonempty E],
  RealFunctionSeriesUniformConvergesValue (constantAlternatingHarmonicValue (E := E)) ∧
    (∀ x : E, ¬ Ch11.PartialSums.realSeriesConvergesValue (fun n => |constantAlternatingHarmonicValue n x|)) ∧
    ¬ RealFunctionSeriesUniformAbsoluteConvergesValue (constantAlternatingHarmonicValue (E := E))

/-- Full expected proposition for `diagonal_harmonic_nonnegative`. -/
noncomputable def diagonal_harmonic_nonnegative : Prop :=
  ∀ (n : ℕ) (k : ℕ+),
  0 ≤ diagonalHarmonicValue n k

/-- Full expected proposition for `diagonal_harmonic_partialSum`. -/
noncomputable def diagonal_harmonic_partialSum : Prop :=
  ∀ (N : ℕ) (k : ℕ+),
  realFunctionPartialSumValue (fun n x => |diagonalHarmonicValue n x|) N k =
      if (k : ℕ) ≤ N then 1 / ((k : ℕ) : ℝ) else 0

/-- Full expected proposition for `diagonal_harmonic_error`. -/
noncomputable def diagonal_harmonic_error : Prop :=
  ∀ (N : ℕ) (k : ℕ+),
  |realFunctionPartialSumValue (fun n x => |diagonalHarmonicValue n x|) N k -
      1 / ((k : ℕ) : ℝ)| =
      if (k : ℕ) ≤ N then 0 else 1 / ((k : ℕ) : ℝ)

/-- Full expected proposition for `diagonal_harmonic_tail_supremum`. -/
noncomputable def diagonal_harmonic_tail_supremum : Prop :=
  ∀ (N : ℕ),
  IsLUB (Set.range (fun k : ℕ+ =>
      |realFunctionPartialSumValue (fun n x => |diagonalHarmonicValue n x|) N k -
        1 / ((k : ℕ) : ℝ)|)) (1 / ((N : ℝ) + 1))

/-- Full expected proposition for `diagonal_harmonic_tail_limit`. -/
noncomputable def diagonal_harmonic_tail_limit : Prop :=
  Ch01.SequenceLimit.realSequenceConvergesValue (fun N : ℕ => 1 / ((N : ℝ) + 1)) 0

/-- Full expected proposition for `diagonal_harmonic_uniform_absolute`. -/
noncomputable def diagonal_harmonic_uniform_absolute : Prop :=
  RealFunctionSeriesUniformAbsoluteConvergesValue diagonalHarmonicValue

/-- Full expected proposition for `diagonal_harmonic_term_supremum`. -/
noncomputable def diagonal_harmonic_term_supremum : Prop :=
  ∀ (n : ℕ),
  IsLUB (insert 0 (Set.range (fun k : ℕ+ => |diagonalHarmonicValue n k|)))
      (1 / (n : ℝ))

/-- Full expected proposition for `diagonal_harmonic_suprema_diverge`. -/
noncomputable def diagonal_harmonic_suprema_diverge : Prop :=
  ¬ Ch11.PartialSums.realSeriesConvergesValue (fun n : ℕ => 1 / (n : ℝ))

/-- Full expected proposition for `diagonal_harmonic_not_normal`. -/
noncomputable def diagonal_harmonic_not_normal : Prop :=
  ¬ RealFunctionSeriesNormallyConvergesValue diagonalHarmonicValue

/-- Full expected proposition for `real_function_series_absolute_uniform`. -/
noncomputable def real_function_series_absolute_uniform : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℝ)
    (_h : RealFunctionSeriesUniformAbsoluteConvergesValue u),
  RealFunctionSeriesUniformConvergesValue u

/-- Full expected proposition for `complex_function_series_absolute_uniform`. -/
noncomputable def complex_function_series_absolute_uniform : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℂ)
    (_h : ComplexFunctionSeriesUniformAbsoluteConvergesValue u),
  ComplexFunctionSeriesUniformConvergesValue u

/-- Full expected proposition for `real_function_series_normal_absolute`. -/
noncomputable def real_function_series_normal_absolute : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℝ)
    (_h : RealFunctionSeriesNormallyConvergesValue u),
  RealFunctionSeriesUniformAbsoluteConvergesValue u

/-- Full expected proposition for `complex_function_series_normal_absolute`. -/
noncomputable def complex_function_series_normal_absolute : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℂ)
    (_h : ComplexFunctionSeriesNormallyConvergesValue u),
  ComplexFunctionSeriesUniformAbsoluteConvergesValue u

end Specs.SingleVariableAnalysis.Ch12.Series
