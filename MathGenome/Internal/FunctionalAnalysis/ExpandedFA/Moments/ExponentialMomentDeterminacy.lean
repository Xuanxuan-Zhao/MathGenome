import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.ExponentialMomentDeterminacy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.HamburgerExistence
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Sufficient conditions in `paper.tex`, `fa2:p3:moment-determinacy`.
The positive even-moment series determines the cosh integral of every
representing finite measure. It supplies a common absolute exponential moment;
the complex moment-generating functions then agree near zero by their Taylor
series and on the common strip by analytic continuation. Characteristic-function
uniqueness applies to finite measures, including the zero measure.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace ExpandedFA.Moments
namespace ExponentialMomentDeterminacy

theorem even_moment_nonneg {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (n : ℕ) : 0 ≤ m (2 * n) := by
  rw [← hμ.2.2 (2 * n)]
  exact integral_nonneg fun t => (even_two_mul n).pow_nonneg t

private def coshTerm (r : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (r * t) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

private theorem coshTerm_nonneg (r : ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ coshTerm r n t := by
  unfold coshTerm
  exact div_nonneg (Even.pow_nonneg (even_two_mul n) _) (Nat.cast_nonneg _)

private theorem coshTerm_integrable {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (r : ℝ) (n : ℕ) :
    Integrable (coshTerm r n) μ := by
  change Integrable (fun t : ℝ => (r * t) ^ (2 * n) /
    (Nat.factorial (2 * n) : ℝ)) μ
  simp only [mul_pow]
  exact ((HamburgerExistenceProof.RepresentsHamburgerMoments.integrable_pow hμ
    (2 * n)).const_mul _).div_const _

private theorem integral_coshTerm {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (r : ℝ) (n : ℕ) :
    (∫ t, coshTerm r n t ∂μ) =
      m (2 * n) * r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
  simp only [coshTerm, mul_pow, integral_div, integral_const_mul, hμ.2.2]
  ring

theorem cosh_integrable {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (r : ℝ)
    (hs : Summable (fun n : ℕ => m (2 * n) * r ^ (2 * n) /
      (Nat.factorial (2 * n) : ℝ))) :
    Integrable (fun t : ℝ => Real.cosh (r * t)) μ := by
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
    (ae_of_all μ (fun t => (Real.cosh_pos _).le))).mpr ?_⟩
  have heq : (fun t : ℝ => ENNReal.ofReal (Real.cosh (r * t))) =
      fun t => ∑' n, ENNReal.ofReal (coshTerm r n t) := by
    funext t
    rw [Real.cosh_eq_tsum]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => coshTerm_nonneg r n t)
      (Real.hasSum_cosh (r * t)).summable
  rw [heq, lintegral_tsum (fun n => by unfold coshTerm; fun_prop)]
  have hi (n : ℕ) : (∫⁻ t, ENNReal.ofReal (coshTerm r n t) ∂μ) =
      ENNReal.ofReal (m (2 * n) * r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (coshTerm_integrable hμ r n)
      (ae_of_all μ (coshTerm_nonneg r n)), integral_coshTerm hμ]
  simp_rw [hi]
  exact hs.tsum_ofReal_lt_top

theorem integral_cosh {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (r : ℝ)
    (hs : Summable (fun n : ℕ => m (2 * n) * r ^ (2 * n) /
      (Nat.factorial (2 * n) : ℝ))) :
    (∫ t : ℝ, Real.cosh (r * t) ∂μ) =
      ∑' n : ℕ, m (2 * n) * r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
  have hn : Summable (fun n => ∫ t, ‖coshTerm r n t‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (coshTerm_nonneg _ _ _), integral_coshTerm hμ]
      using hs
  have h := integral_tsum_of_summable_integral_norm (coshTerm_integrable hμ r) hn
  have heq : (fun t : ℝ => ∑' n, coshTerm r n t) = fun t => Real.cosh (r * t) := by
    funext t
    exact (Real.hasSum_cosh (r * t)).tsum_eq
  rw [heq] at h
  simpa only [integral_coshTerm hμ] using h.symm

theorem exp_abs_le_two_cosh (r t : ℝ) :
    Real.exp (r * |t|) ≤ 2 * Real.cosh (r * t) := by
  rw [Real.cosh_eq]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    nlinarith [Real.exp_pos (-(r * t))]
  · rw [abs_of_nonpos ht, mul_neg]
    nlinarith [Real.exp_pos (r * t)]

theorem common_exponential_moment : ExponentialMomentDeterminacySpec.CommonExponentialMoment := by
  intro m r _hr hs μ hμ
  refine ⟨((cosh_integrable hμ r hs).const_mul 2).mono' (by fun_prop) ?_,
    integral_cosh hμ r hs⟩
  exact ae_of_all μ fun t => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_abs_le_two_cosh r t

open ProbabilityTheory

/-- The exponential bound supplies a full open interval of integrability,
and consequently the corresponding vertical strip of holomorphy. -/
theorem mem_interior_integrableExpSet {μ : Measure ℝ} {r s : ℝ}
    (_hr : 0 < r) (hμ : Integrable (fun t : ℝ => Real.exp (r * |t|)) μ)
    (hs : |s| < r) : s ∈ interior (integrableExpSet id μ) := by
  refine mem_interior.mpr ⟨Ioo (-r) r, ?_, isOpen_Ioo, abs_lt.mp hs⟩
  intro u hu
  change Integrable (fun t : ℝ => Real.exp (u * t)) μ
  refine hμ.mono' (by fun_prop) (ae_of_all μ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    u * t ≤ |u * t| := le_abs_self _
    _ = |u| * |t| := abs_mul _ _
    _ ≤ r * |t| := mul_le_mul_of_nonneg_right (abs_lt.mpr hu).le (abs_nonneg t)

/-- Equality of all moment derivatives gives equality in a neighborhood of
zero. Both functions have their actual Taylor series there. -/
theorem complexMGF_eventually_eq {m : ℕ → ℝ} {μ ν : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (hν : RepresentsHamburgerMoments m ν)
    {r : ℝ} (hr : 0 < r)
    (hμexp : Integrable (fun t : ℝ => Real.exp (r * |t|)) μ)
    (hνexp : Integrable (fun t : ℝ => Real.exp (r * |t|)) ν) :
    complexMGF id μ =ᶠ[𝓝 (0 : ℂ)] complexMGF id ν := by
  have hμ0 : (0 : ℂ).re ∈ interior (integrableExpSet id μ) :=
    mem_interior_integrableExpSet hr hμexp (by simpa using hr)
  have hν0 : (0 : ℂ).re ∈ interior (integrableExpSet id ν) :=
    mem_interior_integrableExpSet hr hνexp (by simpa using hr)
  have hd (n : ℕ) : iteratedDeriv n (complexMGF id μ) 0 =
      iteratedDeriv n (complexMGF id ν) 0 := by
    rw [iteratedDeriv_complexMGF hμ0, iteratedDeriv_complexMGF hν0]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one]
    simp_rw [← Complex.ofReal_pow, integral_complex_ofReal, hμ.2.2, hν.2.2]
  have h₁ := (analyticAt_complexMGF hμ0).hasFPowerSeriesAt.eventually_hasSum_sub
  have h₂ := (analyticAt_complexMGF hν0).hasFPowerSeriesAt.eventually_hasSum_sub
  simp_rw [hd] at h₁
  filter_upwards [h₁, h₂] with z h₁ h₂ using h₁.unique h₂

/-- Analytic continuation on the common strip reaches the entire imaginary
axis. Characteristic-function (equivalently Fourier) uniqueness then applies. -/
theorem exponential_uniqueness : ExponentialMomentDeterminacySpec.ExponentialUniqueness := by
  intro m μ ν hμ hν hexp
  obtain ⟨r, hr, hμexp, hνexp⟩ := hexp
  let : IsFiniteMeasure μ := hμ.1
  let : IsFiniteMeasure ν := hν.1
  let U : Set ℂ := {z | z.re ∈ Ioo (-r) r}
  have hμan : AnalyticOnNhd ℂ (complexMGF id μ) U := by
    intro z hz
    exact analyticAt_complexMGF
      (mem_interior_integrableExpSet hr hμexp (abs_lt.mpr hz))
  have hνan : AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro z hz
    exact analyticAt_complexMGF
      (mem_interior_integrableExpSet hr hνexp (abs_lt.mpr hz))
  have hU : IsPreconnected U :=
    ((convex_Ioo (-r) r).linear_preimage Complex.reLm).isPreconnected
  have hzero : (0 : ℂ) ∈ U := by
    change -r < (0 : ℂ).re ∧ (0 : ℂ).re < r
    simp only [Complex.zero_re]
    constructor <;> linarith
  have heq := hμan.eqOn_of_preconnected_of_eventuallyEq hνan hU hzero
    (complexMGF_eventually_eq hμ hν hr hμexp hνexp)
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  apply heq
  change -r < ((t : ℂ) * Complex.I).re ∧ ((t : ℂ) * Complex.I).re < r
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self]
  constructor <;> linarith

theorem series_determinacy : ExponentialMomentDeterminacySpec.SeriesDeterminacy := by
  intro m hm hs
  obtain ⟨μ, hμ⟩ := (hamburger_existence m).1.mp hm
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  obtain ⟨r, hr, hs⟩ := hs
  exact exponential_uniqueness m ν μ hν hμ
    ⟨r, hr, (common_exponential_moment m r hr hs ν hν).1,
      (common_exponential_moment m r hr hs μ hμ).1⟩

theorem bounded_even_determinacy : ExponentialMomentDeterminacySpec.BoundedEvenDeterminacy := by
  intro m hm hb
  obtain ⟨C, hC⟩ := hb
  obtain ⟨μ, hμ⟩ := (hamburger_existence m).1.mp hm
  apply series_determinacy m hm
  refine ⟨1, zero_lt_one, ?_⟩
  have hsum := (Real.hasSum_cosh 1).summable.mul_left C
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
  · exact div_nonneg (mul_nonneg (even_moment_nonneg hμ n) (by positivity))
      (Nat.cast_nonneg _)
  · simpa only [one_pow, mul_one, one_div, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right (hC n)
        (inv_nonneg.mpr (Nat.cast_nonneg (Nat.factorial (2 * n))))

end ExponentialMomentDeterminacy
end ExpandedFA.Moments
