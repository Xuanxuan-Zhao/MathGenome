import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SinCos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Sine and cosine constructed from their factorial series

K03.07.sin_cos, paper.tex:1652–1667. The absolute majorants are the even
and odd subseries of the exponential majorant. The upstream M-test proves
uniform convergence on bounded disks, independently of the identification.
Mathlib's `Complex.hasSum_sin/cos` identifies the constructed sums; those
lemmas derive the same series from the factorial series for exp using finite
residue-class grouping. The real series identities and canonical derivative
formulas then supply the real-increment derivatives. No ODE certificate or
unproved termwise-differentiation assumption is used.
-/
set_option maxHeartbeats 800000

noncomputable section
namespace SingleVariableAnalysis
open scoped BigOperators
open Specs.SingleVariableAnalysis.Ch07.SinCos

/-- The odd factorial series, with complex argument. -/
def seriesSin (z : ℂ) : ℂ := ∑' n, complexTerm 1 z n
/-- The even factorial series, with complex argument. -/
def seriesCos (z : ℂ) : ℂ := ∑' n, complexTerm 0 z n
/-- The real odd factorial series. -/
def realSeriesSin (x : ℝ) : ℝ := ∑' n, realTerm 1 x n
/-- The real even factorial series. -/
def realSeriesCos (x : ℝ) : ℝ := ∑' n, realTerm 0 x n

namespace SinCos

theorem factorial_subseries_summable (R : ℝ) (k : ℕ) :
    Summable (fun n : ℕ => R^(2*n+k) / ((2*n+k).factorial : ℝ)) := by
  exact (Real.summable_pow_div_factorial R).comp_injective
    (show Function.Injective (fun n : ℕ => 2*n+k) by intro m n h; dsimp at h; omega)

theorem complex_norm_term (k n : ℕ) (z : ℂ) :
    ‖complexTerm k z n‖ = ‖z‖^(2*n+k) / ((2*n+k).factorial : ℝ) := by
  simp [complexTerm, norm_pow]

theorem real_abs_term (k n : ℕ) (x : ℝ) :
    |realTerm k x n| = |x|^(2*n+k) / ((2*n+k).factorial : ℝ) := by
  simp [realTerm, abs_div, abs_mul, abs_pow]

theorem complex_norm_summable (k : ℕ) (z : ℂ) :
    Summable (fun n => ‖complexTerm k z n‖) := by
  simp only [complex_norm_term]
  exact factorial_subseries_summable ‖z‖ k

theorem real_abs_summable (k : ℕ) (x : ℝ) :
    Summable (fun n => |realTerm k x n|) := by
  simp only [real_abs_term]
  exact factorial_subseries_summable |x| k

theorem complex_disk_bound (R : ℝ) (k n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖complexTerm k z n‖ ≤ R^(2*n+k) / ((2*n+k).factorial : ℝ) := by
  rw [complex_norm_term]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)

theorem real_disk_bound (R : ℝ) (k n : ℕ) (x : ℝ) (hx : |x| ≤ R) :
    |realTerm k x n| ≤ R^(2*n+k) / ((2*n+k).factorial : ℝ) := by
  rw [real_abs_term]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx _) (by positivity)

theorem complex_uniform (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    ComplexUniformConverges
      (fun N (z : {z : ℂ // ‖z‖ ≤ R}) => complexPartialSum (complexTerm k z) N)
      (fun z => ∑' n, complexTerm k z n) := by
  obtain ⟨⟨f, hf⟩, _⟩ := complex_m_test
    (fun n (z : {z : ℂ // ‖z‖ ≤ R}) => complexTerm k z n)
    (fun n => R^(2*n+k) / ((2*n+k).factorial : ℝ))
    (fun n => by positivity)
    (fun n z => complex_disk_bound R k n z z.property)
    ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum
      (factorial_subseries_summable R k).hasSum⟩
  have he : f = fun (z : {z : ℂ // ‖z‖ ≤ R}) => ∑' n, complexTerm k z n := by
    funext z
    exact complex_series_sum_unique _ _ _ (complexUniformConverges_pointwise _ _ hf z)
      (PowerSeriesDifferentiation.complex_hasSum_of_hasSum (complex_norm_summable k z).of_norm.hasSum)
  rwa [he] at hf

theorem real_uniform (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    RealUniformConverges
      (fun N (x : {x : ℝ // |x| ≤ R}) => realPartialSum (realTerm k x) N)
      (fun x => ∑' n, realTerm k x n) := by
  obtain ⟨⟨f, hf⟩, _⟩ := real_m_test
    (fun n (x : {x : ℝ // |x| ≤ R}) => realTerm k x n)
    (fun n => R^(2*n+k) / ((2*n+k).factorial : ℝ))
    (fun n => by positivity)
    (fun n x => real_disk_bound R k n x x.property)
    ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum
      (factorial_subseries_summable R k).hasSum⟩
  have he : f = fun (x : {x : ℝ // |x| ≤ R}) => ∑' n, realTerm k x n := by
    funext x
    exact real_series_sum_unique _ _ _ (realUniformConverges_pointwise _ _ hf x)
      (PowerSeriesDifferentiation.real_hasSum_of_hasSum (real_abs_summable k x).of_norm.hasSum)
  rwa [he] at hf

end SinCos

theorem sinCosSeries_absolute : complexAbsolute := by
  intro z
  exact ⟨⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum (SinCos.complex_norm_summable 1 z).hasSum⟩,
    ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum (SinCos.complex_norm_summable 0 z).hasSum⟩⟩

theorem real_sinCosSeries_absolute : realAbsolute := by
  intro x
  exact ⟨⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum (SinCos.real_abs_summable 1 x).hasSum⟩,
    ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum (SinCos.real_abs_summable 0 x).hasSum⟩⟩

theorem sinCosSeries_hasSum : complexSeriesValue := by
  intro z
  exact ⟨PowerSeriesDifferentiation.complex_hasSum_of_hasSum (SinCos.complex_norm_summable 1 z).of_norm.hasSum,
    PowerSeriesDifferentiation.complex_hasSum_of_hasSum (SinCos.complex_norm_summable 0 z).of_norm.hasSum⟩

theorem real_sinCosSeries_hasSum : realSeriesValue := by
  intro x
  exact ⟨PowerSeriesDifferentiation.real_hasSum_of_hasSum (SinCos.real_abs_summable 1 x).of_norm.hasSum,
    PowerSeriesDifferentiation.real_hasSum_of_hasSum (SinCos.real_abs_summable 0 x).of_norm.hasSum⟩

theorem sinCosSeries_uniform_disk : complexUniformDisk := by
  intro R hR
  exact ⟨SinCos.complex_uniform R hR 1, SinCos.complex_uniform R hR 0⟩

theorem real_sinCosSeries_uniform_disk : realUniformDisk := by
  intro R hR
  exact ⟨SinCos.real_uniform R hR 1, SinCos.real_uniform R hR 0⟩

theorem sinCosSeries_eq_complex : canonicalComplex := by
  intro z
  exact ⟨(Complex.hasSum_sin z).tsum_eq, by simpa [seriesCosValue, complexTerm] using (Complex.hasSum_cos z).tsum_eq⟩

theorem sinCosSeries_eq_real : canonicalReal := by
  intro x
  exact ⟨(Real.hasSum_sin x).tsum_eq, by simpa [realSeriesCosValue, realTerm] using (Real.hasSum_cos x).tsum_eq⟩

theorem sinCosSeries_real_restriction : realRestriction := by
  intro x
  rw [(sinCosSeries_eq_complex x).1, (sinCosSeries_eq_complex x).2,
    (sinCosSeries_eq_real x).1, (sinCosSeries_eq_real x).2]
  exact ⟨(Complex.ofReal_sin x).symm, (Complex.ofReal_cos x).symm⟩

theorem real_sinCosSeries_hasDerivAt : realDerivatives := by
  have hs : realSeriesSinValue = Real.sin := funext fun x => (sinCosSeries_eq_real x).1
  have hc : realSeriesCosValue = Real.cos := funext fun x => (sinCosSeries_eq_real x).2
  rw [realDerivatives, hs, hc]
  exact fun x => ⟨Real.hasDerivAt_sin x, Real.hasDerivAt_cos x⟩

theorem sinCosSeries_real_hasDerivAt : complexRealDerivatives := by
  intro x
  have hs : (fun t : ℝ => seriesSinValue (t : ℂ)) = fun t => (realSeriesSinValue t : ℂ) :=
    funext fun t => (sinCosSeries_real_restriction t).1
  have hc : (fun t : ℝ => seriesCosValue (t : ℂ)) = fun t => (realSeriesCosValue t : ℂ) :=
    funext fun t => (sinCosSeries_real_restriction t).2
  change HasDerivAt (fun t : ℝ => seriesSinValue (t : ℂ)) (seriesCosValue (x : ℂ)) x ∧
    HasDerivAt (fun t : ℝ => seriesCosValue (t : ℂ)) (-seriesSinValue (x : ℂ)) x
  rw [hs, hc, (sinCosSeries_real_restriction x).1, (sinCosSeries_real_restriction x).2]
  exact ⟨(real_sinCosSeries_hasDerivAt x).1.ofReal_comp,
    by simpa using (real_sinCosSeries_hasDerivAt x).2.ofReal_comp⟩

theorem sinCosSeries_zero : complexInitialValues := by
  rw [complexInitialValues, (sinCosSeries_eq_complex 0).1, (sinCosSeries_eq_complex 0).2]
  simp

theorem real_sinCosSeries_zero : realInitialValues := by
  rw [realInitialValues, (sinCosSeries_eq_real 0).1, (sinCosSeries_eq_real 0).2]
  simp

end SingleVariableAnalysis
