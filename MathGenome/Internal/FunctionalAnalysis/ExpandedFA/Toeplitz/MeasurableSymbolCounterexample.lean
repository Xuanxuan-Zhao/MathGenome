import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.MeasurableSymbolCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Toeplitz.Definitions
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Perfect
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Div

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology
namespace ExpandedFA.Toeplitz.MeasurableSymbolCounterexample
open ExpandedFA.PartIV
open Spec
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
local instance : Nontrivial _root_.Circle := ⟨⟨1, -1, by
  intro h
  have hh := congrArg (fun z : _root_.Circle => (z : ℂ)) h
  norm_num at hh⟩⟩
local instance : Nontrivial Torus := AddCircle.homeomorphCircle'.toEquiv.nontrivial
local instance : NullSingletonClass Definitions.Spec.circleMeasure := by
  exact Measure.IsAddHaarMeasure.nullSingletonClass _

/-- Real part of the Cayley fraction, including totalized division at one. -/
theorem cayley_re (z : ℂ) :
    ((1 + z) / (1 - z)).re = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  simp only [Complex.div_re, Complex.add_re, Complex.one_re, Complex.sub_re,
    Complex.add_im, Complex.one_im, zero_add, Complex.sub_im, zero_sub,
    Complex.normSq_apply]
  ring

theorem theta_norm_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : ‖theta z‖ = 1 := by
  rw [theta, Complex.norm_exp, Complex.neg_re, cayley_re,
    Complex.normSq_eq_norm_sq, hz]
  norm_num

theorem theta_continuousAt {z : ℂ} (hz : z ≠ 1) : ContinuousAt theta z := by
  exact Complex.continuous_exp.continuousAt.comp
    (((continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hz.symm)).neg)

theorem analytic_bound : Spec.AnalyticBound := by
  have hne (z : ℂ) (hz : z ∈ HardyDisk.disk) : z ≠ 1 := by
    intro h
    simp [h, HardyDiskSpec.disk] at hz
  constructor
  · intro z hz
    exact (Complex.differentiableAt_exp.comp z
      (((differentiableAt_const 1).add differentiableAt_id).div
        ((differentiableAt_const 1).sub differentiableAt_id)
        (sub_ne_zero.mpr (hne z hz).symm)).neg).differentiableWithinAt
  · intro z hz
    have hn : ‖z‖ < 1 := by simpa [HardyDiskSpec.disk] using hz
    rw [theta, Complex.norm_exp, Real.exp_le_one_iff, Complex.neg_re, neg_nonpos]
    rw [cayley_re, Complex.normSq_eq_norm_sq]
    exact div_nonneg (by nlinarith [norm_nonneg z]) (Complex.normSq_nonneg _)

theorem boundaryFunction_norm (t : Torus) : ‖boundaryFunction t‖ = 1 :=
  theta_norm_of_norm_eq_one (HardyDisk.norm_fourier_point 1 t)

theorem boundaryFunction_measurable : Measurable boundaryFunction := by
  unfold boundaryFunction theta
  exact Complex.continuous_exp.measurable.comp
    (((measurable_const.add (fourier 1).continuous.measurable).div
      (measurable_const.sub (fourier 1).continuous.measurable)).neg)

theorem boundaryFunction_memLp : MemLp boundaryFunction ∞ Definitions.Spec.circleMeasure :=
  memLp_top_of_bound boundaryFunction_measurable.aestronglyMeasurable 1
    (Eventually.of_forall fun t => (boundaryFunction_norm t).le)

def symbol : Definitions.ScalarSymbol :=
  Definitions.symbolOfFunction boundaryFunction boundaryFunction_memLp

theorem symbol_values : (symbol : Torus → ℂ) =ᵐ[Definitions.Spec.circleMeasure]
    boundaryFunction := Definitions.function_symbol_values _ _

theorem symbol_unimodular : ∀ᵐ t ∂Definitions.Spec.circleMeasure, ‖symbol t‖ = 1 := by
  filter_upwards [symbol_values] with t ht
  rw [ht, boundaryFunction_norm]

theorem coordinate_ne_one {t : Torus} (ht : t ≠ 0) :
    fourier (T := 2 * π) 1 t ≠ 1 := by
  rw [fourier_one]
  intro he
  apply ht
  apply AddCircle.injective_toCircle (by positivity : (2 * π : ℝ) ≠ 0)
  apply Subtype.ext
  simpa using he

theorem boundaryFunction_radial {t : Torus} (ht : t ≠ 0) :
    Tendsto (fun r : ℝ => theta ((r : ℂ) * fourier (T := 2 * π) 1 t))
      (𝓝[<] (1 : ℝ)) (𝓝 (boundaryFunction t)) := by
  have hm : Tendsto (fun r : ℝ => (r : ℂ) * fourier (T := 2 * π) 1 t)
      (𝓝[<] (1 : ℝ)) (𝓝 (fourier (T := 2 * π) 1 t)) := by
    simpa using ((Complex.continuous_ofReal.tendsto (1 : ℝ)).mul_const
      (fourier (T := 2 * π) 1 t)).mono_left nhdsWithin_le_nhds
  exact (theta_continuousAt (coordinate_ne_one ht)).tendsto.comp hm

theorem symbol_radial : ∀ᵐ t ∂Definitions.Spec.circleMeasure,
    Tendsto (fun r : ℝ => theta ((r : ℂ) * fourier (T := 2 * π) 1 t))
      (𝓝[<] (1 : ℝ)) (𝓝 (symbol t)) := by
  filter_upwards [Definitions.Spec.circleMeasure.ae_ne 0, symbol_values] with t ht he
  rw [he]
  exact boundaryFunction_radial ht

theorem boundary_construction : Spec.BoundaryConstruction :=
  ⟨symbol, symbol_values, symbol_unimodular, symbol_radial⟩

/-- The bounded analytic disk function used by the upstream multiplier. -/
def boundedTheta : HardyDisk.HInfinity := by
  refine ⟨fun z => theta z, ?_, 1, ?_⟩
  · apply analytic_bound.1.congr
    intro z hz
    change HardyDiskSpec.zeroExtend (fun z : HardyDisk.Disk => theta z) z = theta z
    simp [HardyDiskSpec.zeroExtend, hz]
  · intro z
    exact analytic_bound.2 z z.property

def analyticMultiplication : Definitions.H2 →L[ℂ] Definitions.H2 :=
  HardyDisk.multiplier boundedTheta

theorem analyticMultiplication_eval (f : Definitions.H2) {z : ℂ} (hz : z ∈ HardyDisk.disk) :
    HardyDisk.eval (analyticMultiplication f) z = theta z * HardyDisk.eval f z := by
  change HardyDisk.eval (HardyDisk.multiplierVector boundedTheta f) z = _
  rw [HardyDisk.multiplierVector_eval boundedTheta f hz]
  have hh := HardyDisk.zeroExtend_apply boundedTheta.val (⟨z, hz⟩ : HardyDisk.Disk)
  simpa [boundedTheta] using congrArg (fun c => c * HardyDisk.eval f z) hh

/-- Boundary products are identified by two successive a.e. subsequences of
radial L² convergence. No pointwise boundary convergence for arbitrary H²
functions is assumed. -/
theorem boundary_multiplication (f : Definitions.H2) :
    HardyDisk.boundary (analyticMultiplication f) =
      Definitions.multiplication symbol (HardyDisk.boundary f) := by
  let h := analyticMultiplication f
  -- The upstream radial approximants converge in L² to the actual boundary.
  have hht : Tendsto (fun r => HardyDisk.boundary (HardyDisk.radialCoefficients r h))
      (𝓝[<] (1 : ℝ)) (𝓝 (HardyDisk.boundary h)) :=
    ((HardyDisk.boundary.continuous.tendsto h).comp
      (HardyDisk.radialCoefficients_tendsto h)).mono_left nhdsWithin_le_nhds
  have hft : Tendsto (fun r => HardyDisk.boundary (HardyDisk.radialCoefficients r f))
      (𝓝[<] (1 : ℝ)) (𝓝 (HardyDisk.boundary f)) :=
    ((HardyDisk.boundary.continuous.tendsto f).comp
      (HardyDisk.radialCoefficients_tendsto f)).mono_left nhdsWithin_le_nhds
  obtain ⟨rs, hrs, hhae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hht).exists_seq_tendsto_ae'
  obtain ⟨ns, hns, hfae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hft.comp hrs)).exists_seq_tendsto_ae
  have hvalues : ∀ᵐ t ∂Definitions.Spec.circleMeasure, ∀ n : ℕ,
      0 ≤ rs (ns n) → rs (ns n) < 1 →
      HardyDisk.boundary (HardyDisk.radialCoefficients (rs (ns n)) h) t =
        theta ((rs (ns n) : ℂ) * fourier (T := 2 * π) 1 t) *
          HardyDisk.boundary (HardyDisk.radialCoefficients (rs (ns n)) f) t := by
    rw [ae_all_iff]
    intro n
    by_cases hr0 : 0 ≤ rs (ns n)
    · by_cases hr1 : rs (ns n) < 1
      · filter_upwards [HardyDisk.radial_boundary_values h hr0 hr1,
          HardyDisk.radial_boundary_values f hr0 hr1] with t hht hft
        intro _ _
        rw [hht, hft]
        exact analyticMultiplication_eval f (HardyDisk.radial_point_mem_disk hr0 hr1 t)
      · exact Eventually.of_forall fun _ _ ht => (hr1 ht).elim
    · exact Eventually.of_forall fun _ ht _ => (hr0 ht).elim
  apply Lp.ext
  filter_upwards [hhae, hfae, hvalues, Definitions.Spec.circleMeasure.ae_ne 0,
    Definitions.multiplication_values symbol (HardyDisk.boundary f), symbol_values]
      with t hht hft hvals ht hmul hsym
  have hlim := ((boundaryFunction_radial ht).comp (hrs.comp hns.tendsto_atTop)).mul hft
  have heq : (fun n => HardyDisk.boundary (HardyDisk.radialCoefficients (rs (ns n)) h) t)
      =ᶠ[atTop] (fun n => theta ((rs (ns n) : ℂ) * fourier (T := 2 * π) 1 t) *
        HardyDisk.boundary (HardyDisk.radialCoefficients (rs (ns n)) f) t) := by
    filter_upwards [(hrs.comp hns.tendsto_atTop).eventually
      (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))] with n hn
    exact hvals n hn.1.le hn.2
  rw [hmul, hsym]
  exact tendsto_nhds_unique ((hht.comp hns.tendsto_atTop).congr' heq) hlim

theorem toeplitz_eq_analyticMultiplication : Definitions.toeplitz symbol = analyticMultiplication := by
  apply ContinuousLinearMap.ext
  intro f
  change Definitions.boundaryAnalysis
    (Definitions.multiplication symbol (HardyDisk.boundary f)) = _
  rw [← boundary_multiplication, Definitions.boundaryAnalysis_boundary]

theorem multiplication_norm (g : Definitions.BoundaryL2) :
    ‖Definitions.multiplication symbol g‖ = ‖g‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Definitions.multiplication_values symbol g, symbol_unimodular] with t ht hn
    rw [ht, norm_mul, hn, one_mul]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Definitions.multiplication_values symbol g, symbol_unimodular] with t ht hn
    rw [ht, norm_mul, hn, one_mul]

theorem toeplitz_norm (f : Definitions.H2) : ‖Definitions.toeplitz symbol f‖ = ‖f‖ := by
  rw [toeplitz_eq_analyticMultiplication, ← HardyDisk.boundary.norm_map,
    boundary_multiplication, multiplication_norm, HardyDisk.boundary.norm_map]

theorem toeplitz_isometry : Isometry (Definitions.toeplitz symbol) :=
  AddMonoidHomClass.isometry_of_norm (Definitions.toeplitz symbol) toeplitz_norm

theorem toeplitz_closed_range : IsClosed (Set.range (Definitions.toeplitz symbol)) :=
  toeplitz_isometry.isClosedEmbedding.isClosed_range

/-- On the real radius the boundary singularity is an ordinary real exponential. -/
theorem theta_real_norm (r : ℝ) :
    ‖theta (r : ℂ)‖ = Real.exp (-((1 + r) / (1 - r))) := by
  have he : -((1 + (r : ℂ)) / (1 - (r : ℂ))) =
      ((-((1 + r) / (1 - r)) : ℝ) : ℂ) := by push_cast; rfl
  rw [theta, he, Complex.norm_exp, Complex.ofReal_re]

/-- A rational parametrization of radii approaching one. -/
def radius (x : ℝ) : ℝ := 1 - x⁻¹

theorem radius_mem {x : ℝ} (hx : 1 < x) : (radius x : ℂ) ∈ HardyDisk.disk := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hi : 0 < x⁻¹ := inv_pos.mpr hx0
  have hil : x⁻¹ < 1 := (inv_lt_one₀ hx0).mpr hx
  have h0 : 0 ≤ radius x := by dsimp [radius]; linarith
  simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg h0] using (show radius x < 1 by dsimp [radius]; linarith)

theorem theta_radius_norm_le {x : ℝ} (hx : 1 < x) :
    ‖theta (radius x : ℂ)‖ ≤ Real.exp (-x) := by
  rw [theta_real_norm, Real.exp_le_exp]
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have he : (1 + radius x) / (1 - radius x) = 2 * x - 1 := by
    dsimp [radius]
    field_simp
    ring
  rw [he]
  linarith

/-- A convenient weaker form of the sharp Hardy evaluation estimate. -/
theorem evaluation_radius_bound (f : Definitions.H2) {x : ℝ} (hx : 1 < x) :
    ‖HardyDisk.eval f (radius x : ℂ)‖ ≤ ‖f‖ * x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hr := radius_mem hx
  have h0 : 0 ≤ radius x := by dsimp [radius]; exact sub_nonneg.mpr ((inv_lt_one₀ hx0).mpr hx).le
  have he : 1 - radius x ^ 2 = (2 * x - 1) / x ^ 2 := by
    dsimp [radius]
    field_simp
    ring
  have hsq : x⁻¹ ^ 2 ≤ 1 - radius x ^ 2 := by
    rw [he, inv_pow, ← one_div]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hx0)).mpr
    linarith
  have hsqrt : x⁻¹ ≤ Real.sqrt (1 - radius x ^ 2) := by
    exact (Real.le_sqrt (inv_nonneg.mpr hx0.le)
      (le_trans (sq_nonneg _) hsq)).mpr hsq
  have hsqrt0 : 0 < Real.sqrt (1 - radius x ^ 2) :=
    (inv_pos.mpr hx0).trans_le hsqrt
  have hb := HardyDisk.evaluation_bound f (radius x : ℂ) hr
  have hnorm : ‖(radius x : ℂ)‖ = radius x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  rw [hnorm] at hb
  apply hb.trans
  apply (div_le_iff₀ hsqrt0).mpr
  have hh : 1 ≤ x * Real.sqrt (1 - radius x ^ 2) := by
    simpa [hx0.ne'] using mul_le_mul_of_nonneg_left hsqrt hx0.le
  nlinarith [norm_nonneg f]

/-- An H² function divisible by theta cannot be a nonzero polynomial.
The quotient polynomial after removing its finite-order zero at one would
have value zero at one by exponential decay, a contradiction. -/
theorem polynomial_not_divisible (p : Polynomial ℂ) (f : Definitions.H2)
    (heval : ∀ z ∈ HardyDisk.disk, p.eval z = theta z * HardyDisk.eval f z) : p = 0 := by
  by_contra hp
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 1
  have hq1 : q.eval 1 ≠ 0 := by
    simpa only [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] using hq
  let k := p.rootMultiplicity 1
  have hb : ∀ x : ℝ, 1 < x →
      ‖q.eval (radius x : ℂ)‖ ≤ ‖f‖ * (x ^ (k + 1) * Real.exp (-x)) := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have he := heval (radius x : ℂ) (radius_mem hx)
    have hn : ‖p.eval (radius x : ℂ)‖ = x⁻¹ ^ k * ‖q.eval (radius x : ℂ)‖ := by
      rw [hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, norm_mul, norm_pow]
      have hnorm : ‖(radius x : ℂ) - 1‖ = x⁻¹ := by
        have he : (radius x : ℂ) - 1 = (-(x⁻¹) : ℝ) := by
          simp [radius]
        rw [he, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hx0)]
      rw [hnorm]
    have hh : x⁻¹ ^ k * ‖q.eval (radius x : ℂ)‖ ≤
        Real.exp (-x) * (‖f‖ * x) := by
      rw [← hn, he, norm_mul]
      exact mul_le_mul (theta_radius_norm_le hx) (evaluation_radius_bound f hx)
        (norm_nonneg _) (Real.exp_pos _).le
    have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hx0.le k)
    have hcancel : x ^ k * (x⁻¹ ^ k * ‖q.eval (radius x : ℂ)‖) =
        ‖q.eval (radius x : ℂ)‖ := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0.ne', one_pow, one_mul]
    rw [hcancel] at hh'
    convert hh' using 1; ring
  have hr : Tendsto radius atTop (𝓝 (1 : ℝ)) := by
    unfold radius
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)) using 1; simp
  have hqcont : Tendsto (fun x : ℝ => ‖q.eval (radius x : ℂ)‖) atTop (𝓝 ‖q.eval 1‖) := by
    have hc : Tendsto (fun x : ℝ => (radius x : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    exact (q.continuous.tendsto 1).norm.comp hc
  have hlim : Tendsto (fun x : ℝ => ‖q.eval (radius x : ℂ)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) _
      (by simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1)).const_mul ‖f‖)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hb x hx
  have hezero := tendsto_nhds_unique hqcont hlim
  exact hq1 (norm_eq_zero.mp hezero)

/-- The canonical polynomial embedded in the coefficient model of H². -/
def polynomialVector : Polynomial ℂ →ₗ[ℂ] Definitions.H2 :=
  (Polynomial.basisMonomials ℂ).constr ℂ (fun n => lp.single 2 n (1 : ℂ))

theorem polynomialVector_monomial (n : ℕ) (c : ℂ) :
    polynomialVector (Polynomial.monomial n c) = lp.single 2 n c := by
  have he : Polynomial.monomial n c = c • (Polynomial.basisMonomials ℂ n) := by
    simp [Polynomial.coe_basisMonomials, Polynomial.smul_monomial]
  rw [he, map_smul]
  change c • ((Polynomial.basisMonomials ℂ).constr ℂ
    (fun n => lp.single 2 n (1 : ℂ)) (Polynomial.basisMonomials ℂ n)) = _
  rw [Module.Basis.constr_basis, ← lp.single_smul]
  simp

theorem polynomialVector_eval (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ HardyDisk.disk) :
    HardyDisk.eval (polynomialVector p) z = p.eval z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, HardyDisk.evaluation_add _ _ _ hz, hp, hq, Polynomial.eval_add]
  | monomial n c =>
    rw [polynomialVector_monomial]
    exact (HardyDisk.monomial_evaluation n c z).trans Polynomial.eval_monomial.symm

/-- All polynomial classes inject into the actual Toeplitz cokernel. -/
def polynomialCokernel : Polynomial ℂ →ₗ[ℂ]
    (Definitions.H2 ⧸ LinearMap.range (Definitions.toeplitz symbol).toLinearMap) :=
  (LinearMap.range (Definitions.toeplitz symbol).toLinearMap).mkQ.comp polynomialVector

theorem polynomialCokernel_injective : Function.Injective polynomialCokernel := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hm : polynomialVector p ∈ LinearMap.range (Definitions.toeplitz symbol).toLinearMap := by
    exact (Submodule.Quotient.mk_eq_zero _).mp hp
  obtain ⟨f, hf⟩ := hm
  apply polynomial_not_divisible p f
  intro z hz
  rw [← polynomialVector_eval p hz, ← hf]
  change HardyDisk.eval (Definitions.toeplitz symbol f) z = _
  rw [toeplitz_eq_analyticMultiplication]
  exact analyticMultiplication_eval f hz

theorem infinite_codimension :
    ¬ FiniteDimensional ℂ
      (Definitions.H2 ⧸ LinearMap.range (Definitions.toeplitz symbol).toLinearMap) := by
  intro hfinite
  have := hfinite
  have : FiniteDimensional ℂ (Polynomial ℂ) :=
    FiniteDimensional.of_injective polynomialCokernel polynomialCokernel_injective
  have : Finite ℕ := Module.Finite.finite_basis (Polynomial.basisMonomials ℂ)
  exact not_finite ℕ

theorem not_fredholm : ¬ (Definitions.toeplitz symbol).IsFredholm := by
  intro h
  exact infinite_codimension h.finite_coker

theorem counterexample : Spec.Counterexample := by
  refine ⟨analytic_bound, symbol, symbol_values, symbol_unimodular, symbol_radial,
    ?_, toeplitz_isometry, toeplitz_closed_range, infinite_codimension, not_fredholm⟩
  intro f z hz
  change HardyDisk.eval (Definitions.toeplitz symbol f) z = _
  rw [toeplitz_eq_analyticMultiplication]
  exact analyticMultiplication_eval f hz

end ExpandedFA.Toeplitz.MeasurableSymbolCounterexample
