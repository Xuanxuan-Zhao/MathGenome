import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.TermwiseIntegration
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Integration
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PartialSums

/-!
Termwise proper Riemann integration of a uniformly convergent scalar series.
Finite linearity first proves integrability of each ordered partial sum and
computes its integral. Uniform-limit integration then gives integrability of
the sum and convergence of these integrals. The finite identities identify
this sequence with the ordered partial sums of the numerical integral series.
-/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology

/-- Finite sums over an initial segment are integrable, with the expected value. -/
theorem real_sum_range_value (u : ℕ → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ n, RealIntegrable (u n) a b) (N : ℕ) :
    ∃ h : RealIntegrable (fun x => ∑ n ∈ Finset.range N, u n x) a b,
      realIntegral _ h = ∑ n ∈ Finset.range N, realIntegral (u n) (hu n) := by
  induction N with
  | zero => simpa using real_zero_value hab
  | succ N ih =>
    obtain ⟨hs, hIs⟩ := ih
    obtain ⟨ht, hIt⟩ := real_add_value hs (hu N)
    simp only [Finset.sum_range_succ]
    exact ⟨ht, hIt.trans (congrArg (fun z => z + realIntegral (u N) (hu N)) hIs)⟩

/-- The complex finite-sum identity uses the componentwise Darboux integral. -/
theorem complex_sum_range_value (u : ℕ → ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ n, ComplexIntegrable (u n) a b) (N : ℕ) :
    ∃ h : ComplexIntegrable (fun x => ∑ n ∈ Finset.range N, u n x) a b,
      complexIntegral _ h = ∑ n ∈ Finset.range N, complexIntegral (u n) (hu n) := by
  induction N with
  | zero => simpa using complex_zero_value hab
  | succ N ih =>
    obtain ⟨hs, hIs⟩ := ih
    obtain ⟨ht, hIt⟩ := complex_add_value hs (hu N)
    simp only [Finset.sum_range_succ]
    exact ⟨ht, hIt.trans (congrArg (fun z => z + complexIntegral (u N) (hu N)) hIs)⟩

theorem real_termwise_integration :
    Specs.SingleVariableAnalysis.Ch12.TermwiseIntegration.realTermwiseIntegration := by
  intro u f a b hab hu hU
  let S : ℕ → ℝ → ℝ := fun N x => realPartialSum (fun n => u n x) N
  have hS : ∀ N, ∃ h : RealIntegrable (S N) a b,
      realIntegral _ h = realPartialSum (fun n => realIntegral (u n) (hu n)) N :=
    fun N => real_sum_range_value u hab hu (N + 1)
  choose hS hIS using hS
  obtain ⟨hf, _, _, _, hlim⟩ := real_uniform_integration S f hab hS hU
  refine ⟨hf, ?_⟩
  change RealSeriesHasSum (fun n => realIntegral (u n) (hu n)) (realIntegral f hf)
  apply (realSequenceConverges_iff _ _).mpr
  exact hlim.congr (fun N => hIS N)

theorem complex_termwise_integration :
    Specs.SingleVariableAnalysis.Ch12.TermwiseIntegration.complexTermwiseIntegration := by
  intro u f a b hab hu hU
  let S : ℕ → ℝ → ℂ := fun N x => complexPartialSum (fun n => u n x) N
  have hS : ∀ N, ∃ h : ComplexIntegrable (S N) a b,
      complexIntegral _ h = complexPartialSum (fun n => complexIntegral (u n) (hu n)) N :=
    fun N => complex_sum_range_value u hab hu (N + 1)
  choose hS hIS using hS
  obtain ⟨hf, _, _, _, hlim⟩ := complex_uniform_integration S f hab hS hU
  refine ⟨hf, ?_⟩
  change ComplexSeriesHasSum (fun n => complexIntegral (u n) (hu n)) (complexIntegral f hf)
  apply (complexSequenceConverges_iff _ _).mpr
  exact hlim.congr (fun N => hIS N)

end SingleVariableAnalysis.Riemann
