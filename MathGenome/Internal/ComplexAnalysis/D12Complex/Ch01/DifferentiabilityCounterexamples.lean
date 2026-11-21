import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.DifferentiabilityCounterexamples
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The examples from paper.tex:228–245,268–289. Division at zero in a field
makes the displayed formula for F have precisely the stipulated value F(0)=0.
Real homogeneity determines its directional derivatives; the directions 1 and
1+i contradict any possible complex derivative. The squared norm is treated by
the pointwise CR bridge, using its actual real differentiability.
-/

noncomputable section
open Complex ComplexConjugate
namespace D12Complex.Counterexamples
abbrev F := Specs.D12Complex.Ch01.DifferentiabilityCounterexamples.F_value
abbrev normSquared := Specs.D12Complex.Ch01.DifferentiabilityCounterexamples.normSquared_value

theorem F_zero : F 0 = 0 := by simp [F, Specs.D12Complex.Ch01.DifferentiabilityCounterexamples.F_value]

theorem F_norm (z : ℂ) : ‖F z‖ = ‖z‖ := by
  simp only [F, Specs.D12Complex.Ch01.DifferentiabilityCounterexamples.F_value,
    norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp

private theorem denominator (z : ℂ) : (‖z‖ : ℂ) ^ 4 = (normSq z : ℂ) ^ 2 := by
  rw [normSq_eq_norm_sq, ofReal_pow]
  ring

private theorem F_formula (z : ℂ) : F z = z ^ 5 / (normSq z : ℂ) ^ 2 := by
  simp only [F, Specs.D12Complex.Ch01.DifferentiabilityCounterexamples.F_value, denominator]

private theorem F_real_mul (t : ℝ) (z : ℂ) : F ((t : ℂ) * z) = (t : ℂ) * F z := by
  rw [F_formula, F_formula, normSq_mul]
  simp only [normSq_ofReal, ofReal_mul, mul_pow]
  by_cases ht : t = 0
  · simp [ht]
  by_cases hz : z = 0
  · simp [hz, normSq_zero]
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  have hz' : (normSq z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (mt normSq_eq_zero.mp hz)
  field_simp

private theorem F_one : F 1 = 1 := by norm_num [F_formula]
private theorem F_I : F I = I := by norm_num [F_formula, pow_succ]
private theorem F_diagonal : F (1 + I) = -(1 + I) := by
  rw [F_formula]
  norm_num [normSq_apply, add_re, add_im]
  apply Complex.ext <;> norm_num [pow_succ, mul_re, mul_im]

theorem F_continuous : ContinuousAtPoint F 0 := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro z _ hz
  simpa only [F_zero, sub_zero, F_norm] using hz

private theorem F_real (t : ℝ) : F (t : ℂ) = t := by
  simpa [F_one] using F_real_mul t 1

private theorem F_imag (t : ℝ) : F ((t : ℂ) * I) = (t : ℂ) * I := by
  rw [F_real_mul, F_I]

theorem F_ray_quotients (t : ℝ) (ht : t ≠ 0) :
    F (t : ℂ) / (t : ℂ) = 1 ∧
    F ((t : ℂ) * (1 + I)) / ((t : ℂ) * (1 + I)) = -1 := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  have hd : (1 : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  constructor
  · rw [F_real, div_self ht']
  · rw [F_real_mul, F_diagonal]
    field_simp

theorem F_slices :
    HasDerivAt (fun t : ℝ => (F (t : ℂ)).re) 1 0 ∧
    HasDerivAt (fun t : ℝ => (F ((t : ℂ) * I)).re) 0 0 ∧
    HasDerivAt (fun t : ℝ => (F (t : ℂ)).im) 0 0 ∧
    HasDerivAt (fun t : ℝ => (F ((t : ℂ) * I)).im) 1 0 := by
  simp only [F_real, F_imag, ofReal_re, ofReal_im, mul_I_re, mul_I_im, neg_zero]
  exact ⟨hasDerivAt_id 0, hasDerivAt_const 0 0, hasDerivAt_const 0 0, hasDerivAt_id 0⟩

theorem F_partials :
    partialX (fun z => (F z).re) 0 = 1 ∧
    partialY (fun z => (F z).re) 0 = 0 ∧
    partialX (fun z => (F z).im) 0 = 0 ∧
    partialY (fun z => (F z).im) 0 = 1 := by
  simpa [partialX, partialY] using
    And.intro F_slices.1.deriv (And.intro F_slices.2.1.deriv
      (And.intro F_slices.2.2.1.deriv F_slices.2.2.2.deriv))

private theorem derivative_along_line {c : ℂ} (h : HasDerivAt F c 0) (z : ℂ) :
    c * z = F z := by
  have hp : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z 0 := by
    simpa using (ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z
  have hf : HasFDerivAt F (c • (1 : ℂ →L[ℝ] ℂ)) ((0 : ℂ) * z) := by
    simpa using h.complexToReal_fderiv
  have hcomp := hf.comp_hasDerivAt 0 hp
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * F z) (F z) 0 := by
    simpa using (ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (F z)
  have hh : HasDerivAt (fun t : ℝ => (t : ℂ) * F z) (c * z) 0 := by
    change HasDerivAt (fun t : ℝ => F ((t : ℂ) * z)) (c * z) 0 at hcomp
    simp_rw [F_real_mul] at hcomp
    exact hcomp
  exact hh.unique hline

theorem F_not_differentiable : ¬ ComplexDifferentiableAt F 0 := by
  rintro ⟨c, hc⟩
  have hd := (hasComplexDerivativeAt_iff F c 0).mp hc
  have h1 := derivative_along_line hd 1
  have hdiag := derivative_along_line hd (1 + I)
  simp only [mul_one, F_one] at h1
  rw [h1, one_mul, F_diagonal] at hdiag
  have hr := congrArg Complex.re hdiag
  norm_num at hr

theorem conjugation_smooth : ContDiff ℝ ⊤ (conj : ℂ → ℂ) :=
  conjCLE.contDiff

theorem conjugation_not_differentiable (a : ℂ) :
    ¬ ComplexDifferentiableAt (conj : ℂ → ℂ) a := by
  rw [complexDifferentiableAt_iff, differentiableAt_complex_iff_differentiableAt_real]
  rintro ⟨_, h⟩
  rw [show fderiv ℝ (conj : ℂ → ℂ) a = conjCLE.toContinuousLinearMap from conjCLE.fderiv] at h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem conjugation_not_holomorphic (U : Set ℂ) (hU : U.Nonempty) :
    ¬ HolomorphicOn U (conj : ℂ → ℂ) := by
  intro h
  obtain ⟨a, ha⟩ := hU
  exact conjugation_not_differentiable a ((complexDifferentiableAt_iff _ _).mpr (h.2 a ha))

private theorem normSquared_apply (z : ℂ) :
    normSquared z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
  change ((‖z‖ ^ 2 : ℝ) : ℂ) = _
  congr 1
  rw [← normSq_eq_norm_sq, normSq_apply]
  ring

private theorem normSquared_re (z : ℂ) : (normSquared z).re = z.re ^ 2 + z.im ^ 2 := by
  rw [normSquared_apply]
  exact ofReal_re _

private theorem normSquared_im (z : ℂ) : (normSquared z).im = 0 := by
  rw [normSquared_apply]
  exact ofReal_im _

private theorem normSquared_realDifferentiable : Differentiable ℝ normSquared := by
  have heq : normSquared = fun z : ℂ => ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) :=
    funext normSquared_apply
  rw [heq]
  fun_prop

private theorem normSquared_slices (a : ℂ) :
    partialX (fun z => (normSquared z).re) a = 2 * a.re ∧
    partialY (fun z => (normSquared z).re) a = 2 * a.im ∧
    partialX (fun z => (normSquared z).im) a = 0 ∧
    partialY (fun z => (normSquared z).im) a = 0 := by
  have hx : HasDerivAt (fun t : ℝ => (normSquared (a + (t : ℂ))).re) (2 * a.re) 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).const_add a.re).pow 2).add_const (a.im ^ 2)) using 1 <;>
      simp [normSquared_re]
  have hy : HasDerivAt (fun t : ℝ => (normSquared (a + (t : ℂ) * I)).re) (2 * a.im) 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).const_add a.im).pow 2).const_add (a.re ^ 2)) using 1 <;>
      simp [normSquared_re]
  exact ⟨hx.deriv, hy.deriv, by simp only [partialX, normSquared_im, deriv_const],
    by simp only [partialY, normSquared_im, deriv_const]⟩

theorem normSquared_differentiable_iff (a : ℂ) :
    ComplexDifferentiableAt normSquared a ↔ a = 0 := by
  obtain ⟨hx, hy, hix, hiy⟩ := normSquared_slices a
  rw [complexDifferentiableAt_iff_CR normSquared a (normSquared_realDifferentiable a),
    hx, hy, hix, hiy]
  constructor
  · rintro ⟨hr, hi⟩
    apply Complex.ext <;> simp only [zero_re, zero_im] <;> linarith
  · intro h
    simp [h]

theorem normSquared_derivative_zero : HasComplexDerivativeAt normSquared 0 0 := by
  obtain ⟨hx, hy, hix, hiy⟩ := normSquared_slices 0
  have hr : partialX (fun z => (normSquared z).re) 0 =
      partialY (fun z => (normSquared z).im) 0 := by simp [hx, hiy]
  have hi : partialY (fun z => (normSquared z).re) 0 =
      -partialX (fun z => (normSquared z).im) 0 := by simp [hy, hix]
  have hd := (complexDerivative_CR_formulas normSquared 0
    (normSquared_realDifferentiable 0) hr hi).1
  simpa [hx, hix] using hd

theorem normSquared_not_holomorphic (U : Set ℂ) (h0 : 0 ∈ U) :
    ¬ HolomorphicOn U normSquared := by
  rintro ⟨hU, hdiff⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hz : (r / 2 : ℂ) ∈ U := by
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, Complex.norm_div, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_ofNat, abs_of_pos hr]
    linarith
  have heq := (normSquared_differentiable_iff (r / 2 : ℂ)).mp
    ((complexDifferentiableAt_iff _ _).mpr (hdiff _ hz))
  have := congrArg Complex.re heq
  simp at this
  linarith

end D12Complex.Counterexamples
