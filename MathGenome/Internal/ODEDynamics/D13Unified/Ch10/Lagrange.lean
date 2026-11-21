import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace D13Unified.Ch10.Lagrange
open RegularProblem

abbrev boundaryForm := Specs.D13Unified.Ch10.Lagrange.boundaryFormValue

/-- A single nonzero real boundary pair annihilates the conjugated determinant. -/
private lemma endpoint_form_zero (alpha beta p : ℝ) (u du v dv : ℂ)
    (hn : alpha ≠ 0 ∨ beta ≠ 0)
    (hu : (alpha : ℂ) * u + (beta : ℂ) * (p : ℂ) * du = 0)
    (hv : (alpha : ℂ) * v + (beta : ℂ) * (p : ℂ) * dv = 0) :
    (p : ℂ) * (u * conj dv - du * conj v) = 0 := by
  have hvc : (alpha : ℂ) * conj v + (beta : ℂ) * (p : ℂ) * conj dv = 0 := by
    simpa using congrArg conj hv
  rcases hn with ha | hb
  · have haC : (alpha : ℂ) ≠ 0 := by exact_mod_cast ha
    apply (mul_eq_zero.mp (show (alpha : ℂ) *
      ((p : ℂ) * (u * conj dv - du * conj v)) = 0 by
      linear_combination (p : ℂ) * conj dv * hu - (p : ℂ) * du * hvc)).resolve_left haC
  · have hbC : (beta : ℂ) ≠ 0 := by exact_mod_cast hb
    apply (mul_eq_zero.mp (show (beta : ℂ) *
      ((p : ℂ) * (u * conj dv - du * conj v)) = 0 by
      linear_combination u * hvc - conj v * hu)).resolve_left hbC

theorem boundary_form_zero : Specs.D13Unified.Ch10.Lagrange.boundaryFormZeroType := by
  intro P B u v hu hv
  exact ⟨endpoint_form_zero _ _ _ _ _ _ _ B.left_nonzero hu.1 hv.1,
    endpoint_form_zero _ _ _ _ _ _ _ B.right_nonzero hu.2 hv.2⟩

private lemma p_regular_complex (P : Problem) :
    ContDiffOn ℝ 1 (fun x => (P.p x : ℂ)) (interval P) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn P.p_regular

private lemma derivative_regular (P : Problem) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ 2 u (interval P)) :
    ContDiffOn ℝ 1 (derivative P u) (interval P) :=
  hu.derivWithin (uniqueDiffOn_Icc P.a_lt_b) (by norm_num)

private lemma flux_regular (P : Problem) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ 2 u (interval P)) :
    ContDiffOn ℝ 1 (fun x => (P.p x : ℂ) * derivative P u x) (interval P) :=
  (p_regular_complex P).mul (derivative_regular P u hu)

private lemma expression_continuous (P : Problem) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ 2 u (interval P)) :
    ContinuousOn (expression P u) (interval P) := by
  exact ((flux_regular P u hu).continuousOn_derivWithin
    (uniqueDiffOn_Icc P.a_lt_b) (by norm_num)).neg.add
    ((Complex.continuous_ofReal.comp_continuousOn P.q_continuous).mul hu.continuousOn)

private lemma boundaryForm_derivative (P : Problem) (u v : ℝ → ℂ)
    (hu : ContDiffOn ℝ 2 u (interval P)) (hv : ContDiffOn ℝ 2 v (interval P))
    (x : ℝ) (hx : x ∈ interval P) :
    HasDerivWithinAt (boundaryForm P u v)
      (expression P u x * conj (v x) - u x * conj (expression P v x)) (interval P) x := by
  have hdu := (hu.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hdv := (hv.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hfu := ((flux_regular P u hu).differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hfv := ((flux_regular P v hv).differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have h := (hdu.mul hfv.star).sub (hfu.mul hdv.star)
  convert h using 1
  · ext t
    simp [boundaryForm, Specs.D13Unified.Ch10.Lagrange.boundaryFormValue]
    ring
  · simp [expression, Specs.D13Unified.Ch10.RegularProblem.expressionValue,
      derivative, Specs.D13Unified.Ch10.RegularProblem.derivativeValue]
    ring

/-- Green's formula with within-interval derivatives, including both endpoints. -/
theorem lagrange_identity : Specs.D13Unified.Ch10.Lagrange.lagrangeIdentityType := by
  intro P u v hu hv
  have hc : ContinuousOn (boundaryForm P u v) (interval P) :=
    fun x hx => (boundaryForm_derivative P u v hu hv x hx).continuousWithinAt
  have hi : ContinuousOn
      (fun x => expression P u x * conj (v x) - u x * conj (expression P v x))
      (interval P) :=
    ((expression_continuous P u hu).mul hv.continuousOn.star).sub
      (hu.continuousOn.mul (expression_continuous P v hv).star)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le P.a_lt_b.le hc
  · intro x hx
    exact (boundaryForm_derivative P u v hu hv x ⟨hx.1.le, hx.2.le⟩).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
  · exact hi.intervalIntegrable_of_Icc P.a_lt_b.le

/-- The integral identity specialized to two classical eigenfunctions. -/
private lemma spectral_pair (P : Problem) (B : BoundaryCoefficients)
    (lam mu : ℂ) (u v : ℝ → ℂ)
    (hu : IsClassicalEigenfunction P B lam u) (hv : IsClassicalEigenfunction P B mu v)
    (hu2 : MemLp u 2 (weightedMeasure P)) (hv2 : MemLp v 2 (weightedMeasure P)) :
    (lam - conj mu) * paperInner P (toHilbert P u hu2) (toHilbert P v hv2) = 0 := by
  have hip : paperInner P (toHilbert P u hu2) (toHilbert P v hv2) =
      ∫ x in P.a..P.b, u x * conj (v x) * (P.w x : ℂ) := by
    rw [inner_representatives, intervalIntegral.integral_of_le P.a_lt_b.le]
    exact integral_Icc_eq_integral_Ioc
  have hb := boundary_form_zero P B u v hu.2.2.1 hv.2.2.1
  calc
    (lam - conj mu) * paperInner P (toHilbert P u hu2) (toHilbert P v hv2) =
        ∫ x in P.a..P.b, (lam - conj mu) * (u x * conj (v x) * (P.w x : ℂ)) := by
      rw [hip, intervalIntegral.integral_const_mul]
    _ = ∫ x in P.a..P.b,
        expression P u x * conj (v x) - u x * conj (expression P v x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ interval P := by
        simpa [interval, Specs.D13Unified.Ch10.RegularProblem.intervalValue,
          uIcc_of_le P.a_lt_b.le] using hx
      have heu : expression P u x = lam * (P.w x : ℂ) * u x := hu.2.2.2 x hx'
      have hev : expression P v x = mu * (P.w x : ℂ) * v x := hv.2.2.2 x hx'
      change (lam - conj mu) * (u x * conj (v x) * (P.w x : ℂ)) =
        expression P u x * conj (v x) - u x * conj (expression P v x)
      rw [heu, hev]
      simp only [map_mul, Complex.conj_ofReal]
      ring
    _ = 0 := by rw [lagrange_identity P u v hu.1 hv.1, hb.1, hb.2, sub_self]

/-- All eigenvalues for the permitted real separated boundary conditions are real. -/
theorem eigenvalue_real : Specs.D13Unified.Ch10.Lagrange.eigenvalueRealType := by
  intro P B lam u hu
  obtain ⟨hu2, hne⟩ := eigenfunction_hilbert P B lam u hu
  have h := spectral_pair P B lam lam u u hu hu hu2 hu2
  have hn : paperInner P (toHilbert P u hu2) (toHilbert P u hu2) ≠ 0 := by
    rw [inner_norm]
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hl := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hn)
  have him := congrArg Complex.im hl
  simp only [Complex.conj_im] at him
  linarith

/-- Orthogonality is stated for actual weighted Hilbert classes of the eigenfunctions. -/
theorem eigenfunctions_orthogonal :
    Specs.D13Unified.Ch10.Lagrange.eigenfunctionsOrthogonalType := by
  intro P B lam mu u v hu hv hne hu2 hv2
  have hmu : conj mu = mu := by
    apply Complex.ext
    · simp
    · simp [eigenvalue_real P B mu v hv]
  have h := spectral_pair P B lam mu u v hu hv hu2 hv2
  rw [hmu] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

end D13Unified.Ch10.Lagrange
