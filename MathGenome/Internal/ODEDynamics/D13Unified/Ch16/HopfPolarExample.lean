import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfPolarExample
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap

noncomputable section
namespace D13Unified.Ch16.HopfPolarExample
open Set Filter Complex
open scoped ComplexConjugate Topology
open Specs.D13Unified.Ch16
open HopfPolarExample CubicHomologicalElimination HopfReturnExpansion

lemma norm_square_cast (z : ℂ) : (‖z‖ ^ 2 : ℂ) = z * conj z := by
  rw [← ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]

lemma coefficient_value (κ μ ω : ℝ) : computedCoefficient κ μ ω = (κ : ℂ) := by
  simp [computedCoefficient, retainedCoefficient, cubicAfterQuadratic,
    quadraticChange, zeroQuadratic, resonantCubic]

theorem normalization : Normalization := by
  refine ⟨?_, ?_, ?_⟩
  · intro κ ω μ z
    simp only [family, eigenvalue, Cubic.eval, resonantCubic]
    rw [show ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z by exact_mod_cast norm_square_cast z]
    ring
  · intro μ ω
    ext <;> simp [quadraticChange, zeroQuadratic]
  · intro κ μ ω
    refine ⟨coefficient_value κ μ ω, ?_⟩
    ext <;> simp [cubicChange, cubicAfterQuadratic, quadraticChange,
      zeroQuadratic, resonantCubic]

lemma field_polar (μ ω r θ : ℝ) :
    field μ ω (polarPoint r θ) =
      ((μ * r - r ^ 3 : ℝ) : ℂ) * direction θ +
        (r : ℂ) * direction θ * (ω * I) := by
  simp [field, family, polarPoint, direction, Complex.norm_exp, sq_abs]
  ring

theorem polar_equations : PolarEquations := by
  intro μ ω r θ v w hr
  rw [field_polar]
  have hd : direction θ ≠ 0 := Complex.exp_ne_zero _
  have heq : ((v : ℂ) * direction θ + (r : ℂ) * direction θ * (w * I) =
        ((μ * r - r ^ 3 : ℝ) : ℂ) * direction θ +
        (r : ℂ) * direction θ * (ω * I)) ↔
      (v : ℂ) + r * w * I = ((μ * r - r ^ 3 : ℝ) : ℂ) + r * ω * I := by
    constructor <;> intro h
    · apply mul_right_cancel₀ hd
      convert h using 1 <;> ring
    · calc
        _ = ((v : ℂ) + r * w * I) * direction θ := by ring
        _ = _ := congrArg (fun z : ℂ => z * direction θ) h
        _ = _ := by ring
  rw [heq]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [pow_succ] at hre him
    exact ⟨by simpa [pow_succ] using hre, him.resolve_right hr.ne'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma polar_derivative {r θ : ℝ → ℝ} {t v w : ℝ}
    (hr : HasDerivAt r v t) (hθ : HasDerivAt θ w t) :
    HasDerivAt (fun s => polarPoint (r s) (θ s))
      ((v : ℂ) * direction (θ t) +
        (r t : ℂ) * direction (θ t) * (w * I)) t := by
  have hd := (((hθ.ofReal_comp).mul_const I).cexp)
  convert (hr.ofReal_comp.mul hd) using 1
  · rfl
  · simp only [direction]
    ring

theorem polar_solutions : PolarSolutions := by
  intro μ ω r θ t v w hr hθ hpos
  have hd := polar_derivative hr hθ
  constructor
  · intro h
    exact (polar_equations μ ω (r t) (θ t) v w hpos).mp (hd.unique h)
  · intro h
    rw [← (polar_equations μ ω (r t) (θ t) v w hpos).mpr h]
    exact hd

theorem amplitude_and_degeneracy : AmplitudeAndDegeneracy := by
  constructor
  · intro μ hμ
    exact ⟨Real.sq_sqrt hμ.le, Real.sqrt_pos.2 hμ⟩
  · intro μ ω
    simp [coefficient_value]

lemma cycle_derivative (μ ω t : ℝ) (hμ : 0 < μ) :
    HasDerivAt (cycle μ ω) (field μ ω (cycle μ ω t)) t := by
  have hr : μ * Real.sqrt μ - (Real.sqrt μ) ^ 3 = 0 := by
    rw [pow_succ, Real.sq_sqrt hμ.le]
    ring
  have hd := polar_derivative (hasDerivAt_const t (Real.sqrt μ))
    ((hasDerivAt_id t).const_mul ω)
  change HasDerivAt (fun s => polarPoint (Real.sqrt μ) (ω * s))
    (field μ ω (polarPoint (Real.sqrt μ) (ω*t))) t
  rw [field_polar, hr]
  simpa only [id_eq, mul_one, ofReal_zero, zero_mul, zero_add] using hd

lemma cycle_periodic (μ ω : ℝ) (hω : ω ≠ 0) :
    Function.Periodic (cycle μ ω) (2 * Real.pi / ω) := by
  intro t
  have ht : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by
    field_simp
  simp only [cycle, polarPoint, direction, ht, ofReal_add, add_mul, Complex.exp_add]
  have he : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
    simpa using Complex.exp_two_pi_mul_I
  rw [he, mul_one]

lemma cycle_range (μ ω : ℝ) (hμ : 0 < μ) (hω : 0 < ω) :
    range (cycle μ ω) = circle μ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simp [circle, cycle, polarPoint, direction, Complex.norm_exp,
      abs_of_pos (Real.sqrt_pos.2 hμ), Metric.mem_sphere, dist_eq_norm]
  · intro hz
    have hn : ‖z‖ = Real.sqrt μ := by simpa [circle, Metric.mem_sphere, dist_eq_norm] using hz
    refine ⟨z.arg / ω, ?_⟩
    have ht : ω * (z.arg / ω) = z.arg := by field_simp
    simpa [cycle, polarPoint, direction, ht, ← hn] using Complex.norm_mul_exp_arg_mul_I z

lemma cycle_nonconstant (μ ω : ℝ) (hμ : 0 < μ) (hω : 0 < ω) :
    ∃ s t, cycle μ ω s ≠ cycle μ ω t := by
  refine ⟨0, Real.pi / ω, ?_⟩
  have ht : ω * (Real.pi / ω) = Real.pi := by field_simp
  have he : Complex.exp ((Real.pi : ℂ) * I) = -1 := Complex.exp_pi_mul_I
  simp only [cycle, polarPoint, direction, mul_zero, ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one, ht, he, mul_neg, mul_one]
  intro h
  have hr := congrArg Complex.re h
  simp only [ofReal_re, neg_re] at hr
  linarith [Real.sqrt_pos.2 hμ]

lemma cycle_least_period (μ ω : ℝ) (hμ : 0 < μ) (hω : 0 < ω)
    (S : ℝ) (hS : 0 < S) (hp : Function.Periodic (cycle μ ω) S) :
    2 * Real.pi / ω ≤ S := by
  have hr : (Real.sqrt μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hμ).ne'
  have he : Complex.exp (((ω * S : ℝ) : ℂ) * I) = 1 := by
    have h := hp 0
    simp only [cycle, polarPoint, direction, zero_add, mul_zero, ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one] at h
    exact mul_left_cancel₀ hr (by simpa using h)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff_of_im_nonneg
    (by simpa using (mul_pos hω hS).le) |>.mp he
  have him := congrArg Complex.im hn
  norm_num at him
  have hnpos : 0 < n := by
    by_contra h
    have hzero : n = 0 := by omega
    simp only [hzero, Nat.cast_zero, zero_mul] at him
    exact (mul_pos hω hS).ne' him
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  apply (div_le_iff₀ hω).mpr
  nlinarith [Real.pi_pos]

theorem periodic_circle : PeriodicCircle := by
  intro μ ω hμ hω
  refine ⟨?_, fun t => cycle_derivative μ ω t hμ, cycle_range μ ω hμ hω⟩
  refine ⟨div_pos Real.two_pi_pos hω, cycle μ ω,
    cycle_periodic μ ω hω.ne', fun t => cycle_derivative μ ω t hμ,
    cycle_nonconstant μ ω hμ hω, (cycle_range μ ω hμ hω).symm, ?_⟩
  exact fun S hS hp => cycle_least_period μ ω hμ hω S hS hp

/-- Reciprocal squared radial scale; it is positive throughout forward time. -/
def denominator (μ : ℝ) (x : ℂ) (t : ℝ) : ℝ :=
  ‖x‖ ^ 2 / μ + (1 - ‖x‖ ^ 2 / μ) * Real.exp (-2 * μ * t)

def forwardCurve (μ ω : ℝ) (x : ℂ) (t : ℝ) : ℂ :=
  direction (ω*t) * x / (Real.sqrt (denominator μ x t) : ℂ)

lemma denominator_zero (μ : ℝ) (x : ℂ) : denominator μ x 0 = 1 := by
  simp [denominator]

lemma denominator_positive {μ : ℝ} {x : ℂ} (hμ : 0 < μ) (hx : x ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) : 0 < denominator μ x t := by
  have ha : 0 < ‖x‖ ^ 2 / μ := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) hμ
  have he : 0 < Real.exp (-2 * μ * t) := Real.exp_pos _
  have he1 : Real.exp (-2 * μ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  dsimp [denominator]
  nlinarith

lemma denominator_derivative (μ : ℝ) (x : ℂ) (t : ℝ) :
    HasDerivAt (denominator μ x)
      ((1 - ‖x‖ ^ 2 / μ) * Real.exp (-2 * μ * t) * (-2*μ)) t := by
  convert (hasDerivAt_const t (‖x‖ ^ 2 / μ)).add
    ((((hasDerivAt_id t).const_mul (-2*μ)).exp).const_mul (1-‖x‖^2/μ)) using 1
  · rfl
  · simp only [id_eq, mul_one, add_zero]
    ring

lemma forwardCurve_zero (μ ω : ℝ) (x : ℂ) : forwardCurve μ ω x 0 = x := by
  simp [forwardCurve, denominator_zero, direction]

lemma forwardCurve_norm (μ ω : ℝ) (x : ℂ) (t : ℝ) :
    ‖forwardCurve μ ω x t‖ = ‖x‖ / Real.sqrt (denominator μ x t) := by
  simp [forwardCurve, direction, norm_div, Complex.norm_exp, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma forwardCurve_derivative {μ ω : ℝ} {x : ℂ} {t : ℝ}
    (hμ : μ ≠ 0) (hD : 0 < denominator μ x t) :
    HasDerivAt (forwardCurve μ ω x)
      (field μ ω (forwardCurve μ ω x t)) t := by
  have hs : Real.sqrt (denominator μ x t) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hsC : (Real.sqrt (denominator μ x t) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  have hd := (((hasDerivAt_id t).const_mul ω).ofReal_comp.mul_const I).cexp
  have hden := ((denominator_derivative μ x t).sqrt hD.ne').ofReal_comp
  have h := (hd.mul_const x).div hden hsC
  convert h using 1
  · rfl
  · simp only [field, family]
    rw [forwardCurve_norm]
    simp only [forwardCurve, direction, id_eq, mul_one]
    push_cast
    have hsq : (Real.sqrt (denominator μ x t) : ℂ)^2 = (denominator μ x t : ℂ) := by
      exact_mod_cast Real.sq_sqrt hD.le
    have hidentity : (denominator μ x t : ℂ) =
        (‖x‖ : ℂ)^2 / μ + (1-(‖x‖ : ℂ)^2/μ) * (Real.exp (-2*μ*t) : ℂ) := by
      simp only [denominator, ofReal_add, ofReal_mul, ofReal_sub, ofReal_div,
        ofReal_pow, ofReal_one]
    push_cast at hidentity
    field_simp [hsC, ofReal_ne_zero.mpr hμ]
    ring_nf
    rw [hsq, hidentity]
    field_simp [ofReal_ne_zero.mpr hμ]
    ring

lemma distance_circle (μ : ℝ) (hμ : 0 < μ) (x : ℂ) :
    Metric.infDist x (circle μ) = |‖x‖ - Real.sqrt μ| := by
  let R := Real.sqrt μ
  have hR : 0 < R := Real.sqrt_pos.2 hμ
  have hmem : (R : ℂ) ∈ circle μ := by simp [circle, R, abs_of_pos hR]
  apply le_antisymm
  · by_cases hx : x = 0
    · simpa [hx, R, abs_of_pos hR] using Metric.infDist_le_dist_of_mem (x := x) hmem
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let y : ℂ := (R / ‖x‖) • x
      have hym : y ∈ circle μ := by
        simp [y, circle, norm_smul, abs_of_pos (div_pos hR hn), hn.ne', R]
      have hd : dist x y = |‖x‖ - R| := by
        rw [dist_eq_norm, show x-y = (1-R/‖x‖) • x by rw [sub_smul, one_smul]]
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ = |(1-R/‖x‖) * ‖x‖| := by rw [abs_mul, abs_of_pos hn]
          _ = |‖x‖ - R| := by congr 1; field_simp

      simpa [hd, R] using Metric.infDist_le_dist_of_mem (x := x) hym
  · apply (Metric.le_infDist (s := circle μ) (x := x) ⟨(R : ℂ), hmem⟩).mpr
    intro y hy
    have hn : ‖y‖ = R := by simpa [circle, R] using hy
    simpa [hn, R, dist_eq_norm] using abs_norm_sub_norm_le x y

lemma forwardCurve_radius_bounds {μ ω : ℝ} {x : ℂ} (hμ : 0 < μ) (hx : x ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    min ‖x‖ (Real.sqrt μ) ≤ ‖forwardCurve μ ω x t‖ ∧
      ‖forwardCurve μ ω x t‖ ≤ max ‖x‖ (Real.sqrt μ) := by
  let D := denominator μ x t
  let n := ‖x‖
  let R := Real.sqrt μ
  let y := n / Real.sqrt D
  have hD : 0 < D := denominator_positive hμ hx ht
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  have hn : 0 < n := norm_pos_iff.mpr hx
  have hR : 0 < R := Real.sqrt_pos.2 hμ
  have hy : 0 < y := div_pos hn hs
  have hR2 : R^2 = μ := Real.sq_sqrt hμ.le
  have hyD : y^2*D = n^2 := by
    dsimp [y]
    rw [div_pow, Real.sq_sqrt hD.le]
    field_simp
  have hID : μ*D = n^2 + (μ-n^2)*Real.exp (-2*μ*t) := by
    dsimp [D, denominator, n]
    field_simp
  have he0 := (Real.exp_pos (-2*μ*t)).le
  have he1 : Real.exp (-2*μ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [forwardCurve_norm]
  change min n R ≤ y ∧ y ≤ max n R
  by_cases hnR : n ≤ R
  · rw [min_eq_left hnR, max_eq_right hnR]
    have hn2 : n^2 ≤ μ := by nlinarith
    have hD1 : D ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr he1)]
    have hDμ : n^2 ≤ μ*D := by nlinarith [mul_nonneg (sub_nonneg.mpr hn2) he0]
    have hy2 : y^2 ≤ μ := by nlinarith
    have hny2 : n^2 ≤ y^2 := by nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hD1)]
    constructor <;> nlinarith
  · have hRn := (le_of_not_ge hnR)
    rw [min_eq_right hRn, max_eq_left hRn]
    have hn2 : μ ≤ n^2 := by nlinarith
    have hD1 : 1 ≤ D := by nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr he1)]
    have hDμ : μ*D ≤ n^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn2) he0]
    have hy2 : μ ≤ y^2 := by nlinarith
    have hny2 : y^2 ≤ n^2 := by nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hD1)]
    constructor <;> nlinarith

lemma forwardCurve_distance_bound {μ ω : ℝ} {x : ℂ} (hμ : 0 < μ) (hx : x ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Metric.infDist (forwardCurve μ ω x t) (circle μ) ≤ Metric.infDist x (circle μ) := by
  rw [distance_circle μ hμ, distance_circle μ hμ]
  obtain ⟨hl, hu⟩ := forwardCurve_radius_bounds (ω := ω) hμ hx ht
  rcases le_total ‖x‖ (Real.sqrt μ) with hn | hn
  · rw [min_eq_left hn] at hl
    rw [max_eq_right hn] at hu
    rw [abs_of_nonpos (sub_nonpos.mpr hu), abs_of_nonpos (sub_nonpos.mpr hn)]
    linarith
  · rw [min_eq_right hn] at hl
    rw [max_eq_left hn] at hu
    rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonneg (sub_nonneg.mpr hn)]
    linarith

lemma field_polynomial (μ ω : ℝ) (z : ℂ) :
    field μ ω z = eigenvalue μ ω * z - z^2 * conj z := by
  simp only [field, family, eigenvalue]
  rw [show ((‖z‖^2 : ℝ) : ℂ) = z * conj z by exact_mod_cast norm_square_cast z]
  push_cast
  ring

lemma field_smooth (μ ω : ℝ) : ContDiff ℝ 1 (field μ ω) := by
  have he : field μ ω = fun z => eigenvalue μ ω * z - z^2 * conj z :=
    funext (field_polynomial μ ω)
  rw [he]
  exact (contDiff_const.mul contDiff_id).sub ((contDiff_id.pow 2).mul Complex.conjCLE.contDiff)

/-- The equation is defined on the whole original plane, without a cutoff. -/
def equation (μ ω : ℝ) : AutonomousODE ℂ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun z => field μ ω z
  continuous_field := (field_smooth μ ω).continuous.comp continuous_subtype_val

@[simp] lemma equation_eval (μ ω : ℝ) (z : ℂ) :
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue (equation μ ω) z =
      field μ ω z := by
  simp [Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue, equation]

lemma forwardCurve_canonical {μ ω : ℝ} {x : ℂ} (hμ : 0 < μ) (hx : x ≠ 0) :
    Specs.D13Unified.Ch14.OrbitalDefinitions.forwardCompleteValue (equation μ ω) x ∧
      ∀ t : ℝ, 0 ≤ t → Ch06.StateDerivative.flow (equation μ ω) t x = forwardCurve μ ω x t := by
  have hc : Continuous (denominator μ x) := by unfold denominator; fun_prop
  have hO : IsOpen {t : ℝ | 0 < denominator μ x t} := isOpen_lt continuous_const hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 (by simp [denominator_zero])
  let J : OpenTimeInterval :=
    ⟨⟨Ioi (-ε), ⟨0, by simpa using hε⟩, ordConnected_Ioi⟩, isOpen_Ioi⟩
  have hD (t : ℝ) (ht : t ∈ J.carrier) : 0 < denominator μ x t := by
    by_cases ht0 : 0 ≤ t
    · exact denominator_positive hμ hx ht0
    · apply hball
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      rw [abs_of_neg (lt_of_not_ge ht0)]
      change -ε < t at ht
      linarith
  have hs : Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue
      (equation μ ω).toODE J (forwardCurve μ ω x) 0 x := by
    refine ⟨⟨?_, fun t ht => mem_univ _, ?_⟩, by simpa [J] using hε, forwardCurve_zero μ ω x⟩
    · intro t ht
      apply ContDiffAt.contDiffWithinAt
      have hDc : ContDiffAt ℝ 1 (denominator μ x) t := by unfold denominator; fun_prop
      have hRinv : ContDiffAt ℝ 1 (fun s => (Real.sqrt (denominator μ x s))⁻¹) t :=
        (hDc.sqrt (hD t ht).ne').inv (Real.sqrt_pos.2 (hD t ht)).ne'
      have hnum : ContDiffAt ℝ 1 (fun s => direction (ω*s)*x) t := by
        have hr : ContDiffAt ℝ 1 (fun s : ℝ => ω*s) t := by fun_prop
        have ho : ContDiffAt ℝ 1 (fun s : ℝ => ((ω*s : ℝ) : ℂ)) t :=
          Complex.ofRealCLM.contDiff.contDiffAt.comp t hr
        exact (ho.mul contDiffAt_const).cexp.mul contDiffAt_const
      convert hRinv.smul hnum using 1
      funext s
      change direction (ω*s) * x / (Real.sqrt (denominator μ x s) : ℂ) =
        (Real.sqrt (denominator μ x s))⁻¹ • (direction (ω*s) * x)
      simp only [Complex.real_smul, ofReal_inv, div_eq_mul_inv]
      ring

    · intro t ht
      simpa [AutonomousODE.toODE, AutonomousODE.eval,
        Specs.D13Unified.Ch01.AutonomousParameters.autonomousToODEValue,
        Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,
        ODE.eval, equation] using forwardCurve_derivative (ω := ω) hμ.ne' (hD t ht)
  have hF : ContDiffOn ℝ 1 (equation μ ω).eval (equation μ ω).domain := by
    have heval : (equation μ ω).eval = field μ ω := by
      funext z
      exact equation_eval μ ω z
    rw [heval]
    exact (field_smooth μ ω).contDiffOn
  have hL := (equation μ ω).locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨_, _, _, _, _, hrestrict, _⟩ :=
    ODE.canonical_solution (equation μ ω).toODE hL 0 x (mem_univ _)
  obtain ⟨hsub, heq⟩ := hrestrict J (forwardCurve μ ω x) hs
  have htime (t : ℝ) (ht : 0 ≤ t) : t ∈ J.carrier := by change -ε < t; linarith
  exact ⟨⟨mem_univ _, fun t ht => hsub (htime t ht)⟩,
    fun t ht => heq (htime t ht)⟩

lemma forwardCurve_radius_limit {μ ω : ℝ} {x : ℂ} (hμ : 0 < μ) (hx : x ≠ 0) :
    Tendsto (fun t : ℝ => ‖forwardCurve μ ω x t‖) atTop (𝓝 (Real.sqrt μ)) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ha : 0 < ‖x‖^2/μ := div_pos (sq_pos_of_pos hn) hμ
  have he : Tendsto (fun t : ℝ => Real.exp (-2*μ*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -2*μ < 0 by linarith))
  have hd : Tendsto (denominator μ x) atTop (𝓝 (‖x‖^2/μ)) := by
    change Tendsto (fun t : ℝ => ‖x‖^2/μ + (1-‖x‖^2/μ)*Real.exp (-2*μ*t))
      atTop (𝓝 (‖x‖^2/μ))
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := ‖x‖^2/μ)).add (he.const_mul (1-‖x‖^2/μ))
  have hlim : Tendsto (fun t => ‖x‖ / Real.sqrt (denominator μ x t)) atTop
      (𝓝 (‖x‖ / Real.sqrt (‖x‖^2/μ))) :=
    tendsto_const_nhds.div (Real.continuous_sqrt.tendsto _ |>.comp hd)
      (Real.sqrt_pos.2 ha).ne'
  have hvalue : ‖x‖ / Real.sqrt (‖x‖^2/μ) = Real.sqrt μ := by
    rw [Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq (norm_nonneg _)]
    field_simp
  simpa only [forwardCurve_norm, hvalue] using hlim

lemma forwardCurve_distance_limit {μ ω : ℝ} {x : ℂ} (hμ : 0 < μ) (hx : x ≠ 0) :
    Tendsto (fun t : ℝ => Metric.infDist (forwardCurve μ ω x t) (circle μ)) atTop (𝓝 0) := by
  simp_rw [distance_circle μ hμ]
  simpa using ((forwardCurve_radius_limit (ω := ω) hμ hx).sub_const (Real.sqrt μ)).abs

/-- Every positive-radius initial point has a complete forward orbit; its
radial error cannot increase and tends to zero. -/
theorem stable_circle : StableCircle := by
  intro μ ω hμ hω
  refine ⟨equation μ ω, rfl, equation_eval μ ω, ?_⟩
  have hR : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hnz (x : ℂ) (hx : Metric.infDist x (circle μ) < Real.sqrt μ / 2) : x ≠ 0 := by
    intro hz
    rw [hz, distance_circle μ hμ] at hx
    simp only [norm_zero, zero_sub, abs_neg, abs_of_pos hR] at hx
    linarith
  constructor
  · intro ε hε
    refine ⟨min ε (Real.sqrt μ / 2), lt_min hε (half_pos hR), ?_⟩
    intro x hx hdist
    have hx0 := hnz x (hdist.trans_le (min_le_right _ _))
    obtain ⟨hcomplete, heq⟩ := forwardCurve_canonical (ω := ω) hμ hx0
    refine ⟨hcomplete, fun t ht => ?_⟩
    rw [heq t ht]
    exact (forwardCurve_distance_bound (ω := ω) hμ hx0 ht).trans_lt
      (hdist.trans_le (min_le_left _ _))
  · refine ⟨Real.sqrt μ / 2, half_pos hR, ?_⟩
    intro x hx hdist
    have hx0 := hnz x hdist
    obtain ⟨hcomplete, heq⟩ := forwardCurve_canonical (ω := ω) hμ hx0
    refine ⟨hcomplete, ?_⟩
    apply (forwardCurve_distance_limit (ω := ω) hμ hx0).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [heq t ht]

end D13Unified.Ch16.HopfPolarExample
