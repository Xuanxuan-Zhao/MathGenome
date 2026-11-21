import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SymmetricEnergy
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The L² estimate of paper.tex, Theorem thm:pde-symmetric-energy.
The proof localizes with a smooth shrinking cutoff, whose support is compact
on each bounded time interval. Its transport contribution is nonpositive even
for linearly growing principal coefficients. The resulting local estimates and
ball exhaustion establish global L² membership as well as the exact bound.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology ContDiff
namespace P201.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricEnergy

/-- Local quadratic forms use the real part for both real and complex fibers. -/
theorem realPart_quadratic_bound {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (M : E →L[𝕜] E) (v : E) :
    |RCLike.re (inner 𝕜 v (M v))| ≤ ‖M‖ * ‖v‖ ^ 2 := by
  calc
    |RCLike.re (inner 𝕜 v (M v))| ≤ ‖inner 𝕜 v (M v)‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖v‖ * ‖M v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := mul_le_mul_of_nonneg_left (M.le_opNorm v) (norm_nonneg _)
    _ = ‖M‖ * ‖v‖ ^ 2 := by ring

/-- The negative inward-speed contribution dominates the normal flux without
requiring the matrix field itself to be bounded globally. -/
theorem inward_boundary_flux_nonpos {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (M : E →L[𝕜] E) (v : E) (a : ℝ) (hM : ‖M‖ ≤ a) :
    -(RCLike.re (inner 𝕜 v (M v))) / 2 - a * (‖v‖ ^ 2 / 2) ≤ 0 := by
  have h := (neg_le_abs (RCLike.re (inner 𝕜 v (M v)))).trans (realPart_quadratic_bound M v)
  have h' := mul_le_mul_of_nonneg_right hM (sq_nonneg ‖v‖)
  linarith

/-- Algebra behind the epsilon regularization at zeros of the energy. -/
theorem regularized_energy_derivative_bound {C E D F ε : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hF : 0 ≤ F) (hε : 0 < ε)
    (hD : D ≤ 2 * C * E + F * Real.sqrt (2 * E)) :
    D / Real.sqrt (2 * E + ε) - C * Real.sqrt (2 * E + ε) ≤ F := by
  have hpos : 0 < Real.sqrt (2 * E + ε) := Real.sqrt_pos.2 (by positivity)
  have hroot : Real.sqrt (2 * E) ≤ Real.sqrt (2 * E + ε) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * E + ε by positivity)
  have hprod := mul_le_mul_of_nonneg_left hroot hF
  have hCε : 0 ≤ C * ε := mul_nonneg hC hε.le
  have hnum : D ≤ (F + C * Real.sqrt (2 * E + ε)) * Real.sqrt (2 * E + ε) := by
    nlinarith
  have hdiv := (div_le_iff₀ hpos).2 hnum
  linarith


/-- An L¹ forcing term suffices; no differentiability of the square root at
zero, and no continuity of the forcing norm, is assumed. -/
theorem sqrt_energy_comparison : SqrtEnergyComparisonStatement := by
  intro T C E D F hT hC hEc hDc hderiv hE hFi hF hD
  have hreg (ε : ℝ) (hε : 0 < ε) :
      Real.sqrt (2 * E T + ε) ≤ Real.exp (C * T) *
        (Real.sqrt (2 * E 0 + ε) + ∫ s in (0 : ℝ)..T, F s) := by
    let Q : ℝ → ℝ := fun s => Real.sqrt (2 * E s + ε)
    let V : ℝ → ℝ := fun s => Real.exp (-C * s) * Q s
    let W : ℝ → ℝ := fun s => Real.exp (-C * s) * (D s / Q s - C * Q s)
    have hQpos (s : ℝ) (hs : s ∈ Icc 0 T) : 0 < Q s := by
      apply Real.sqrt_pos.2
      have := hE s hs
      positivity
    have hQc : ContinuousOn Q (Icc 0 T) := ((hEc.const_mul 2).add_const ε).sqrt
    have hExp : Continuous (fun s : ℝ => Real.exp (-C * s)) := by fun_prop
    have hVc : ContinuousOn V (Icc 0 T) := hExp.continuousOn.mul hQc
    have hWc : ContinuousOn W (Icc 0 T) :=
      hExp.continuousOn.mul ((hDc.div hQc (fun s hs => (hQpos s hs).ne')).sub
        (hQc.const_mul C))
    have hVder (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt V (W s) s := by
      have harg : 2 * E s + ε ≠ 0 := by
        have := hE s (mem_Icc_of_Ioo hs)
        positivity
      have hQder := (((hderiv s hs).const_mul 2).add_const ε).sqrt harg
      have hExpder := ((hasDerivAt_id s).const_mul (-C)).exp
      convert hExpder.mul hQder using 1
      · rfl
      · dsimp [W, Q]
        ring
    have hWi : IntervalIntegrable W volume 0 T := hWc.intervalIntegrable_of_Icc hT
    have hFii : IntervalIntegrable F volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hFi
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hVc hVder hWi
    have hWF : W ≤ᵐ[volume.restrict (Icc 0 T)] F := by
      filter_upwards [hF, hD, ae_restrict_mem measurableSet_Icc] with s hFs hDs hs
      have hb := regularized_energy_derivative_bound hC (hE s hs) hFs hε hDs
      have he : Real.exp (-C * s) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hC hs.1])
      calc
        W s ≤ Real.exp (-C * s) * F s :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
        _ ≤ F s := mul_le_of_le_one_left hFs he
    have hInt := intervalIntegral.integral_mono_ae_restrict hT hWi hFii hWF
    rw [hFTC] at hInt
    have hv0 : V 0 = Q 0 := by simp [V]
    rw [hv0] at hInt
    have hv : Real.exp (-C * T) * Q T ≤ Q 0 + ∫ s in (0 : ℝ)..T, F s := by
      change V T ≤ _
      linarith
    have hm := mul_le_mul_of_nonneg_left hv (Real.exp_pos (C * T)).le
    have hexp : Real.exp (C * T) * Real.exp (-C * T) = 1 := by
      rw [← Real.exp_add]
      simp only [neg_mul, add_neg_cancel, Real.exp_zero]
    simpa only [← mul_assoc, hexp, one_mul] using hm
  have hleft : Tendsto (fun ε : ℝ => Real.sqrt (2 * E T + ε)) (𝓝[>] 0)
      (𝓝 (Real.sqrt (2 * E T))) := by
    have hc : Continuous (fun ε : ℝ => Real.sqrt (2 * E T + ε)) := by fun_prop
    simpa only [add_zero] using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hright : Tendsto (fun ε : ℝ => Real.exp (C * T) *
      (Real.sqrt (2 * E 0 + ε) + ∫ s in (0 : ℝ)..T, F s)) (𝓝[>] 0)
      (𝓝 (Real.exp (C * T) * (Real.sqrt (2 * E 0) + ∫ s in (0 : ℝ)..T, F s))) := by
    have hc : Continuous (fun ε : ℝ => Real.exp (C * T) *
      (Real.sqrt (2 * E 0 + ε) + ∫ s in (0 : ℝ)..T, F s)) := by fun_prop
    simpa only [add_zero] using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hreg ε hε


/-- The local-to-global step uses Fatou on expanding-ball indicators. It makes
no assumption that the full-space L² integral was finite beforehand. -/
theorem ball_exhaustion : BallExhaustionStatement := by
  intro n m 𝕜 _ f K hK hf hlocal
  classical
  let b (k : ℕ) : Set (P201Specs.Space n) := Metric.ball 0 ((k : ℝ) + 1)
  have hb (k : ℕ) : MeasurableSet (b k) := Metric.isOpen_ball.measurableSet
  have hbound (k : ℕ) : eLpNorm ((b k).indicator f) 2 volume ≤ ENNReal.ofReal K := by
    obtain ⟨hmem, hnorm⟩ := hlocal ((k : ℝ) + 1) (by positivity)
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hb k).nullMeasurableSet]
    rw [← ofReal_lpNorm hmem]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hlim : ∀ᵐ x ∂(volume : Measure (P201Specs.Space n)),
      Tendsto (fun k : ℕ => (b k).indicator f x) atTop (𝓝 (f x)) := by
    apply ae_of_all
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with k hk
    have hx : x ∈ b k := by
      simp only [b, Metric.mem_ball, dist_zero_right]
      have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    simp only [Set.indicator_of_mem hx]
  have hglobal : eLpNorm f 2 volume ≤ ENNReal.ofReal K :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound)
      (fun k => hf.indicator (hb k)) hf hlim
  refine ⟨lt_of_le_of_lt hglobal ENNReal.ofReal_lt_top, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hglobal
  simpa only [ENNReal.toReal_ofReal hK, l2Norm, lpNorm] using hreal

/-- Taking the real quadratic form discards exactly the skew-Hermitian part. -/
theorem hermitian_part_quadratic {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (M : Operator m 𝕜) (v : Fiber 𝕜 m) :
    RCLike.re (inner 𝕜 v (hermitianPart M v)) = RCLike.re (inner 𝕜 v (M v)) := by
  have hhalf : (1 / 2 : 𝕜) = ((1 / 2 : ℝ) : 𝕜) := by
    simp only [RCLike.ofReal_div, RCLike.ofReal_one, RCLike.ofReal_ofNat]
  simp only [hermitianPart, smul_apply,
    add_apply, inner_smul_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right, hhalf, RCLike.re_ofReal_mul, map_add]
  rw [inner_re_symm (M v) v]
  ring

/-- The lower-order term uses the exact norm in the manuscript, rather than
replacing it by the possibly larger norm of B. -/
theorem lower_order_energy_bound {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (M : Operator m 𝕜) (v : Fiber 𝕜 m) :
    -RCLike.re (inner 𝕜 v (M v)) ≤ ‖hermitianPart M‖ * ‖v‖ ^ 2 := by
  rw [← hermitian_part_quadratic M v]
  exact (neg_le_abs _).trans (realPart_quadratic_bound _ v)

/-- Bounded derivatives imply a linear-growth estimate. This helper applies
to each fixed-time coefficient slice, without assuming bounded coefficients. -/
theorem norm_le_origin_add_derivative_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M : X → Y) (K : ℝ) (hd : Differentiable ℝ M)
    (hb : ∀ x, ‖fderiv ℝ M x‖ ≤ K) (x : X) :
    ‖M x‖ ≤ ‖M 0‖ + K * ‖x‖ := by
  have hdiff := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := (univ : Set X)) (fun y _ => hd y) (fun y _ => hb y)
    (convex_univ : Convex ℝ (univ : Set X)) (mem_univ (0 : X)) (mem_univ x)
  simp only [sub_zero] at hdiff
  calc
    ‖M x‖ = ‖M 0 + (M x - M 0)‖ := by congr 1; abel
    _ ≤ ‖M 0‖ + ‖M x - M 0‖ := norm_add_le _ _
    _ ≤ ‖M 0‖ + K * ‖x‖ := by linarith


/-- An actual Bochner source supplies precisely the scalar L¹ function used
in the local energy differential inequality. -/
theorem source_norm_integrable {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {f : Field n m 𝕜} (hf : HasL1L2Source T f) :
    IntegrableOn (fun s => l2Norm (f s)) (Ioo 0 T) := by
  obtain ⟨F, hF, hrep⟩ := hf
  apply hF.norm.congr
  filter_upwards [hrep] with s hs
  change ‖F s‖ = (eLpNorm (f s) 2 volume).toReal
  rw [MeasureTheory.Lp.norm_def, eLpNorm_congr_ae hs]

/-- The source class is closed under differences, with no pointwise-in-time
L² condition imposed at exceptional times. -/
theorem source_sub {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {f g : Field n m 𝕜}
    (hf : HasL1L2Source T f) (hg : HasL1L2Source T g) :
    HasL1L2Source T (fun s x => f s x - g s x) := by
  obtain ⟨F, hF, hrepF⟩ := hf
  obtain ⟨G, hG, hrepG⟩ := hg
  refine ⟨fun s => F s - G s, hF.sub hG, ?_⟩
  filter_upwards [hrepF, hrepG] with s hsF hsG
  exact (hsF.sub hsG).trans (MeasureTheory.Lp.coeFn_sub (F s) (G s)).symm

/-- Spatial sections of a smooth solution are smooth at endpoint times too. -/
theorem smooth_solution_section {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜} {f u : Field n m 𝕜}
    (hu : IsSmoothSolution T A B f u) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ContDiff ℝ ∞ (u s) := by
  exact hu.1.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨hs, mem_univ x⟩)

/-- Interior time sections have the classical derivative appearing in the PDE. -/
theorem smooth_solution_time_differentiable {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜} {f u : Field n m 𝕜}
    (hu : IsSmoothSolution T A B f u) {s : ℝ} (hs : s ∈ Ioo 0 T) (x : P201Specs.Space n) :
    DifferentiableAt ℝ (fun r => u r x) s := by
  have hnhds : slab n T ∈ 𝓝 (s, x) :=
    prod_mem_nhds (Icc_mem_nhds hs.1 hs.2) Filter.univ_mem
  exact ((hu.1.contDiffAt hnhds).comp s
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

/-- Linearity is checked on the actual derivatives and continuous linear
operators, so the difference remains in the original smooth solution class. -/
theorem smooth_solution_sub {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    {f g u v : Field n m 𝕜}
    (hu : IsSmoothSolution T A B f u) (hv : IsSmoothSolution T A B g v) :
    IsSmoothSolution T A B (fun s x => f s x - g s x) (fun s x => u s x - v s x) := by
  refine ⟨hu.1.sub hv.1, ?_⟩
  intro s hs x
  have hdu := smooth_solution_time_differentiable hu hs x
  have hdv := smooth_solution_time_differentiable hv hs x
  have hxu := (smooth_solution_section hu (mem_Icc_of_Ioo hs)).differentiable (by simp)
  have hxv := (smooth_solution_section hv (mem_Icc_of_Ioo hs)).differentiable (by simp)
  change deriv ((fun r => u r x) - (fun r => v r x)) s +
    (∑ j, A j s x (fderiv ℝ (u s - v s) x (P201Specs.coordinate n j))) +
      B s x (u s x - v s x) = f s x - g s x
  rw [deriv_sub hdu hdv, fderiv_sub (hxu x) (hxv x)]
  simp only [sub_apply, map_sub]
  rw [Finset.sum_sub_distrib, ← hu.2 s hs x, ← hv.2 s hs x]
  abel

/-- Formal reduction of quantitative stability to the full original estimate.
The premise is explicit; the unconditional PDE estimate is proved below. -/
theorem difference_estimate_of_energy_estimate (henergy : EnergyEstimateStatement) :
    DifferenceEstimateStatement := by
  intro n m 𝕜 _ hn T hT A B hcoeff f g u v hu hv hu0 hv0 hf hg
  exact henergy hn T hT A B hcoeff
    (fun s x => f s x - g s x) (fun s x => u s x - v s x)
    (smooth_solution_sub hu hv) (hu0.sub hv0) (source_sub hf hg)

/-- A zero L² difference has identical smooth spatial representatives. -/
theorem uniqueness_of_difference_estimate (hdifference : DifferenceEstimateStatement) :
    UniquenessStatement := by
  intro n m 𝕜 _ hn T hT A B hcoeff f u v hu hv hu0 hv0 hf hinit t ht
  have hbound := hdifference hn T hT A B hcoeff f f u v hu hv hu0 hv0 hf hf t ht
  have hzero0 : l2Norm (fun x => u 0 x - v 0 x) = 0 := by
    change lpNorm _ 2 volume = 0
    apply (lpNorm_eq_zero (hu0.sub hv0) (by norm_num)).2
    filter_upwards [hinit] with x hx
    exact sub_eq_zero.mpr hx
  have hnorm : l2Norm (fun x => u t x - v t x) = 0 := by
    apply le_antisymm _ lpNorm_nonneg
    have hbound' := hbound.2
    rw [hzero0] at hbound'
    simpa [l2Norm] using hbound' 
  have hae : (fun x => u t x - v t x) =ᵐ[volume] 0 :=
    (lpNorm_eq_zero hbound.1 (by norm_num)).1 hnorm
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume) _ (smooth_solution_section hu ht).continuous
    (smooth_solution_section hv ht).continuous
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx


/-- Differentiation of the scalar real flux along a coordinate line. The
self-adjointness is used only at the point where the derivative is taken. -/
theorem hasDerivAt_symmetric_flux {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : ℝ → Operator m 𝕜} {u : ℝ → Fiber 𝕜 m}
    {A' : Operator m 𝕜} {u' : Fiber 𝕜 m} {s : ℝ}
    (hA : HasDerivAt A A' s) (hu : HasDerivAt u u' s)
    (hsym : IsSelfAdjoint (A s)) :
    HasDerivAt (fun r => RCLike.re (inner 𝕜 (u r) (A r (u r))) / 2)
      (RCLike.re (inner 𝕜 (u s) (A' (u s))) / 2 +
        RCLike.re (inner 𝕜 (u s) (A s u'))) s := by
  let restriction := ContinuousLinearMap.restrictScalarsL 𝕜 (Fiber 𝕜 m) (Fiber 𝕜 m) ℝ ℝ
  have hAr : HasDerivAt (fun r => (A r).restrictScalars ℝ) (A'.restrictScalars ℝ) s := by
    have hRestriction : HasFDerivAt (𝕜 := ℝ)
        (fun a : Operator m 𝕜 => a.restrictScalars ℝ) restriction (A s) := by
      exact restriction.hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
      (F := Operator m 𝕜) (E := Fiber 𝕜 m →L[ℝ] Fiber 𝕜 m)
      (f := A) (f' := A') (l := fun a => a.restrictScalars ℝ)
      (l' := restriction) s hRestriction hA
  have hAu : HasDerivAt (fun r => A r (u r)) (A' (u s) + A s u') s :=
    hAr.clm_apply hu
  have hinner := hu.inner 𝕜 hAu
  have hre : HasDerivAt (fun r => RCLike.re (inner 𝕜 (u r) (A r (u r))))
      (RCLike.re (inner 𝕜 (u s) (A' (u s) + A s u') + inner 𝕜 u' (A s (u s)))) s := by
    exact RCLike.reCLM.hasFDerivAt.comp_hasDerivAt s hinner
  have hcross : RCLike.re (inner 𝕜 u' (A s (u s))) =
      RCLike.re (inner 𝕜 (u s) (A s u')) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hsym.adjoint_eq, inner_re_symm]
  convert hre.div_const 2 using 1
  simp only [inner_add_right, map_add]
  rw [hcross]
  ring

/-- The pointwise real energy inequality with the exact diagonal derivative
and Hermitian lower-order operator norms. Integration and localization remain
separate obligations. -/
theorem pointwise_energy_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A D : Fin n → Operator m 𝕜) (B : Operator m 𝕜)
    (u ut f : Fiber 𝕜 m) (dx : Fin n → Fiber 𝕜 m)
    (hpde : ut + (∑ j, A j (dx j)) + B u = f) :
    RCLike.re (inner 𝕜 u ut) +
      (∑ j, (RCLike.re (inner 𝕜 u (D j u)) / 2 +
        RCLike.re (inner 𝕜 u (A j (dx j))))) ≤
      ((1 / 2 : ℝ) * ∑ j, ‖D j‖ + ‖hermitianPart B‖) * ‖u‖ ^ 2 + ‖u‖ * ‖f‖ := by
  have hp := congrArg (fun z => RCLike.re (inner 𝕜 u z)) hpde
  simp only [inner_add_right, inner_sum, map_add, map_sum] at hp
  have hD : (∑ j, RCLike.re (inner 𝕜 u (D j u))) ≤ (∑ j, ‖D j‖) * ‖u‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact (le_abs_self _).trans (realPart_quadratic_bound (D j) u)
  have hB := lower_order_energy_bound B u
  have hf := re_inner_le_norm (𝕜 := 𝕜) u f
  simp only [Finset.sum_add_distrib, ← Finset.sum_div]
  nlinarith


theorem lpNorm_two_eq_sqrt_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {u : X → E}
    (hu : AEStronglyMeasurable u μ) :
    lpNorm u 2 μ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hu]
  norm_num [Real.sqrt_eq_rpow]

theorem integral_norm_mul_le_lpNorm_two {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {u v : X → E}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (∫ x, ‖u x‖ * ‖v x‖ ∂μ) ≤ lpNorm u 2 μ * lpNorm v 2 μ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two
    (by simpa using hu) (by simpa using hv)
  rw [lpNorm_two_eq_sqrt_integral hu.aestronglyMeasurable,
    lpNorm_two_eq_sqrt_integral hv.aestronglyMeasurable]
  simpa [Real.sqrt_eq_rpow, Real.rpow_natCast] using h

theorem weighted_source_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    (w : X → ℝ) (u f : X → E) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hu : MemLp (fun x => Real.sqrt (w x) • u x) 2 μ)
    (hf : MemLp f 2 μ) :
    Integrable (fun x => w x * ‖u x‖ * ‖f x‖) μ ∧
      (∫ x, w x * ‖u x‖ * ‖f x‖ ∂μ) ≤
        Real.sqrt (∫ x, w x * ‖u x‖ ^ 2 ∂μ) * lpNorm f 2 μ := by
  have hroot (x) : Real.sqrt (w x) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hw1 x)
  have hmeas : AEStronglyMeasurable (fun x => Real.sqrt (w x) • f x) μ :=
    hw.sqrt.aestronglyMeasurable.smul hf.aestronglyMeasurable
  have hbound (x) : ‖Real.sqrt (w x) • f x‖ ≤ ‖f x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hroot x)
  have hf' : MemLp (fun x => Real.sqrt (w x) • f x) 2 μ :=
    hf.mono hmeas (ae_of_all _ hbound)
  have hprod (x) : ‖Real.sqrt (w x) • u x‖ * ‖Real.sqrt (w x) • f x‖ =
      w x * ‖u x‖ * ‖f x‖ := by
    simp only [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ = (Real.sqrt (w x)) ^ 2 * ‖u x‖ * ‖f x‖ := by ring
      _ = _ := by rw [Real.sq_sqrt (hw0 x)]
  have hsq (x) : ‖Real.sqrt (w x) • u x‖ ^ 2 = w x * ‖u x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hw0 x)]
  have hi : Integrable (fun x => ‖Real.sqrt (w x) • u x‖ *
      ‖Real.sqrt (w x) • f x‖) μ :=
    memLp_one_iff_integrable.mp (hu.norm.mul hf'.norm)
  refine ⟨by simpa only [hprod] using hi, ?_⟩
  calc
    (∫ x, w x * ‖u x‖ * ‖f x‖ ∂μ) =
        ∫ x, ‖Real.sqrt (w x) • u x‖ * ‖Real.sqrt (w x) • f x‖ ∂μ := by
      simp only [hprod]
    _ ≤ lpNorm (fun x => Real.sqrt (w x) • u x) 2 μ *
        lpNorm (fun x => Real.sqrt (w x) • f x) 2 μ :=
      integral_norm_mul_le_lpNorm_two hu hf'
    _ ≤ Real.sqrt (∫ x, w x * ‖u x‖ ^ 2 ∂μ) * lpNorm f 2 μ := by
      rw [lpNorm_two_eq_sqrt_integral hu.aestronglyMeasurable]
      simp only [hsq]
      gcongr
      simpa only [lpNorm_norm hf.aestronglyMeasurable] using lpNorm_mono_real hf.norm hbound

theorem weighted_norm_eq_sqrt {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    (w : X → ℝ) (u : X → E) (hw0 : ∀ x, 0 ≤ w x)
    (hu : AEStronglyMeasurable (fun x => Real.sqrt (w x) • u x) μ) :
    lpNorm (fun x => Real.sqrt (w x) • u x) 2 μ =
      Real.sqrt (∫ x, w x * ‖u x‖ ^ 2 ∂μ) := by
  rw [lpNorm_two_eq_sqrt_integral hu]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hw0 x)]

theorem weighted_norm_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    (w : X → ℝ) (u : X → E) (hw1 : ∀ x, w x ≤ 1)
    (hu : MemLp u 2 μ) :
    lpNorm (fun x => Real.sqrt (w x) • u x) 2 μ ≤ lpNorm u 2 μ := by
  simpa only [lpNorm_norm hu.aestronglyMeasurable] using
    lpNorm_mono_real hu.norm (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hw1 x)))

theorem restricted_norm_le_weighted {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    (w : X → ℝ) (u : X → E) (S : Set X) (hS : MeasurableSet S)
    (hwS : ∀ x ∈ S, w x = 1) (hu : AEStronglyMeasurable u μ)
    (hwu : MemLp (fun x => Real.sqrt (w x) • u x) 2 μ) :
    MemLp u 2 (μ.restrict S) ∧ lpNorm u 2 (μ.restrict S) ≤
      lpNorm (fun x => Real.sqrt (w x) • u x) 2 μ := by
  classical
  have hb (x) : ‖S.indicator u x‖ ≤ ‖Real.sqrt (w x) • u x‖ := by
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx, hwS x hx]
    · simp [Set.indicator_of_notMem hx]
  have hi : MemLp (S.indicator u) 2 μ :=
    hwu.mono (hu.indicator hS) (ae_of_all _ hb)
  refine ⟨(memLp_indicator_iff_restrict hS.nullMeasurableSet).1 hi, ?_⟩
  have hm := lpNorm_mono_real hwu.norm hb
  simpa only [lpNorm, eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet,
    eLpNorm_norm _ hwu.aestronglyMeasurable] using hm


theorem compact_integral_differentiation {n : ℕ} (T : ℝ)
    (F D : ℝ → P201Specs.Space n → ℝ)
    (K : Set (P201Specs.Space n)) (hK : IsCompact K)
    (hF : ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (Icc 0 T ×ˢ univ))
    (hFs : ∀ s ∈ Icc 0 T, ∀ x ∉ K, F s x = 0)
    (hDs : ∀ s ∈ Icc 0 T, ∀ x ∉ K, D s x = 0)
    (hd : ∀ s ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => F r x) (D s x) s) :
    ContinuousOn (fun s => ∫ x, F s x) (Icc 0 T) ∧
      ContinuousOn (fun s => ∫ x, D s x) (Icc 0 T) ∧
        ∀ s ∈ Ioo 0 T,
          HasDerivAt (fun r => ∫ x, F r x) (∫ x, D s x) s := by
  have Fsec : ∀ s ∈ Icc 0 T, Continuous (F s) := by
    intro s hs
    exact hF.comp_continuous (continuous_const.prodMk continuous_id)
      (by intro x; exact ⟨hs, mem_univ _⟩)
  have Dsec : ∀ s ∈ Icc 0 T, Continuous (D s) := by
    intro s hs
    exact hD.comp_continuous (continuous_const.prodMk continuous_id)
      (by intro x; exact ⟨hs, mem_univ _⟩)
  have Fint : ∀ s ∈ Icc 0 T, Integrable (F s) := by
    intro s hs
    apply (Fsec s hs).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hK
    exact hFs s hs
  have DFbound : ∃ M : ℝ, ∀ s ∈ Icc 0 T, ∀ x ∈ K, ‖D s x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      (hD.mono (Set.prod_mono_right (subset_univ K)))
    exact ⟨M, fun s hs x hx => hM (s,x) ⟨hs,hx⟩⟩
  obtain ⟨M, hM⟩ := DFbound
  refine ⟨?_, ?_, ?_⟩
  · exact continuousOn_integral_of_compact_support hK hF
      (fun s x hs hx => hFs s hs x hx)
  · exact continuousOn_integral_of_compact_support hK hD
      (fun s x hs hx => hDs s hs x hx)
  · intro s hs
    have his : Ioo 0 T ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs
    have hbint : Integrable (K.indicator (fun _ : P201Specs.Space n => M)) := by
      exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le his
      (F := F) (F' := D) (bound := K.indicator (fun _ => M))
      ?_ (Fint s ⟨hs.1.le,hs.2.le⟩) ?_ ?_ hbint ?_).2
    · filter_upwards [his] with r hr
      exact (Fsec r ⟨hr.1.le,hr.2.le⟩).aestronglyMeasurable
    · exact (Dsec s ⟨hs.1.le,hs.2.le⟩).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x r hr => by
        by_cases hx : x ∈ K
        · simpa only [Set.indicator_of_mem hx] using hM r ⟨hr.1.le,hr.2.le⟩ x hx
        · simp only [Set.indicator_of_notMem hx, hDs r ⟨hr.1.le,hr.2.le⟩ x hx,
            norm_zero, le_refl]
    · exact Filter.Eventually.of_forall fun x r hr => hd r hr x


/-- Fixed-support smooth cutoff energies can be differentiated before any
full-space energy is known to be finite. -/
theorem compact_cutoff_energy_derivative {n : ℕ} (T : ℝ)
    (e a χ c : ℝ → P201Specs.Space n → ℝ)
    (K : Set (P201Specs.Space n)) (hK : IsCompact K)
    (he : ContinuousOn (Function.uncurry e) (Icc 0 T ×ˢ univ))
    (ha : ContinuousOn (Function.uncurry a) (Icc 0 T ×ˢ univ))
    (hχ : ContinuousOn (Function.uncurry χ) (Icc 0 T ×ˢ univ))
    (hc : ContinuousOn (Function.uncurry c) (Icc 0 T ×ˢ univ))
    (hχs : ∀ s ∈ Icc 0 T, ∀ x ∉ K, χ s x = 0)
    (hcs : ∀ s ∈ Icc 0 T, ∀ x ∉ K, c s x = 0)
    (hde : ∀ s ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => e r x) (a s x) s)
    (hdχ : ∀ s ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => χ r x) (c s x) s) :
    ContinuousOn (fun s => ∫ x, χ s x * e s x) (Icc 0 T) ∧
      ContinuousOn (fun s => ∫ x, c s x * e s x + χ s x * a s x) (Icc 0 T) ∧
        ∀ s ∈ Ioo 0 T,
          HasDerivAt (fun r => ∫ x, χ r x * e r x)
            (∫ x, c s x * e s x + χ s x * a s x) s := by
  apply compact_integral_differentiation T
    (fun s x => χ s x * e s x) (fun s x => c s x * e s x + χ s x * a s x)
    K hK (hχ.mul he) ((hc.mul he).add (hχ.mul ha))
  · intro s hs x hx
    simp only [hχs s hs x hx, zero_mul]
  · intro s hs x hx
    simp only [hχs s hs x hx, hcs s hs x hx, zero_mul, add_zero]
  · intro s hs x
    exact (hdχ s hs x).mul (hde s hs x)


/-- Local scalar energy integration with a compact cutoff. None of e, a, q,
or b needs a global integral. Only the products with the cutoff do. -/
theorem compact_cutoff_energy_bound {n : ℕ} (C : ℝ)
    (e a χ c g : P201Specs.Space n → ℝ)
    (q b d : Fin n → P201Specs.Space n → ℝ)
    (he : Continuous e) (ha : Continuous a) (hχ : Continuous χ) (hc : Continuous c)
    (hq : ∀ j, Continuous (q j)) (hb : ∀ j, Continuous (b j))
    (hd : ∀ j, Continuous (d j))
    (hχK : HasCompactSupport χ) (hcK : HasCompactSupport c)
    (hdK : ∀ j, HasCompactSupport (d j))
    (hχnn : ∀ x, 0 ≤ χ x)
    (hχder : ∀ j x, HasLineDerivAt ℝ χ (d j x) x (P201Specs.coordinate n j))
    (hqder : ∀ j x, HasLineDerivAt ℝ (q j) (b j x) x (P201Specs.coordinate n j))
    (hpde : ∀ x, a x + ∑ j, b j x ≤ 2 * C * e x + g x)
    (htransport : ∀ x, c x * e x + ∑ j, d j x * q j x ≤ 0)
    (hg : Integrable (fun x => χ x * g x)) :
    (∫ x, c x * e x + χ x * a x) ≤
      2 * C * (∫ x, χ x * e x) + ∫ x, χ x * g x := by
  have χe : Integrable (fun x => χ x * e x) :=
    (hχ.mul he).integrable_of_hasCompactSupport hχK.mul_right
  have χa : Integrable (fun x => χ x * a x) :=
    (hχ.mul ha).integrable_of_hasCompactSupport hχK.mul_right
  have ce : Integrable (fun x => c x * e x) :=
    (hc.mul he).integrable_of_hasCompactSupport hcK.mul_right
  have χb : ∀ j, Integrable (fun x => χ x * b j x) := fun j =>
    (hχ.mul (hb j)).integrable_of_hasCompactSupport hχK.mul_right
  have dq : ∀ j, Integrable (fun x => d j x * q j x) := fun j =>
    ((hd j).mul (hq j)).integrable_of_hasCompactSupport (hdK j).mul_right
  have χq : ∀ j, Integrable (fun x => χ x * q j x) := fun j =>
    (hχ.mul (hq j)).integrable_of_hasCompactSupport hχK.mul_right
  have ibp (j : Fin n) :
      (∫ x, χ x * b j x) = -(∫ x, d j x * q j x) := by
    apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ) (dq j) (χb j) (χq j)
    · intro x _
      exact hχder j x
    · intro x _
      exact hqder j x
  have χbsum : Integrable (fun x => χ x * ∑ j, b j x) := by
    simpa only [Finset.mul_sum] using (integrable_finsetSum Finset.univ (fun j _ => χb j))
  have dqsum : Integrable (fun x => ∑ j, d j x * q j x) :=
    integrable_finsetSum Finset.univ (fun j _ => dq j)
  have ibpsum : (∫ x, χ x * ∑ j, b j x) = -(∫ x, ∑ j, d j x * q j x) := by
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ => χb j), integral_finsetSum _ (fun j _ => dq j)]
    simp only [ibp, Finset.sum_neg_distrib]
  have hnonpos : (∫ x, c x * e x + ∑ j, d j x * q j x) ≤ 0 := by
    exact integral_nonpos htransport
  have hlocal : (∫ x, χ x * (a x + ∑ j, b j x)) ≤
      ∫ x, χ x * (2 * C * e x + g x) := by
    apply integral_mono
    · convert χa.add χbsum using 1
      funext x
      dsimp
      ring
    · convert (χe.const_mul (2*C)).add hg using 1
      funext x
      dsimp
      ring
    · exact fun x => mul_le_mul_of_nonneg_left (hpde x) (hχnn x)
  rw [show (fun x => χ x * (a x + ∑ j, b j x)) =
      (fun x => χ x * a x + χ x * ∑ j, b j x) by funext x; ring,
    integral_add χa χbsum, ibpsum] at hlocal
  have hrhs : (∫ x, χ x * (2 * C * e x + g x)) =
      2 * C * (∫ x, χ x * e x) + ∫ x, χ x * g x := by
    simp_rw [mul_add, show ∀ x, χ x * (2*C*e x) = 2*C*(χ x*e x) by intro x; ring]
    rw [integral_add (χe.const_mul _) hg, integral_const_mul]
  rw [hrhs] at hlocal
  rw [integral_add ce dqsum] at hnonpos
  rw [integral_add ce χa]
  linarith


theorem coefficient_section_contDiff {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) (j : Fin n) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ContDiff ℝ 1 (A j s) := by
  exact (h.1 j).comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun x => ⟨hs, mem_univ x⟩)

theorem coefficient_section_fderiv {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) (j : Fin n) {s : ℝ} (hs : s ∈ Icc 0 T)
    (x : P201Specs.Space n) :
    fderiv ℝ (A j s) x =
      (fderivWithin ℝ (Function.uncurry (A j)) (slab n T) (s,x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n)) := by
  have hg := ((h.1 j).differentiableOn (by simp) (s,x) ⟨hs, mem_univ x⟩).hasFDerivWithinAt
  have hin : HasFDerivAt (fun y : P201Specs.Space n => (s,y))
      (ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n)) x := by
    simpa using ((ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n)).hasFDerivAt
      (x := x)).add_const (s,0)
  exact ((hg.comp x hin.hasFDerivWithinAt (s := univ) (fun y _ => ⟨hs, mem_univ y⟩)).hasFDerivAt (by simp)).fderiv

theorem coefficient_spatial_derivative_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j, ∀ s ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (A j s) x‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := h.2.1
  refine ⟨K, hK, fun j s hs x => ?_⟩
  rw [coefficient_section_fderiv h j hs x]
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro y
  calc
    ‖(fderivWithin ℝ (Function.uncurry (A j)) (slab n T) (s,x))
        ((ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n)) y)‖ ≤
        ‖fderivWithin ℝ (Function.uncurry (A j)) (slab n T) (s,x)‖ * ‖y‖ := by
      simpa using (fderivWithin ℝ (Function.uncurry (A j)) (slab n T) (s,x)).le_opNorm
        ((ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n)) y)
    _ ≤ K * ‖y‖ := mul_le_mul_of_nonneg_right (hb j (s,x) ⟨hs, mem_univ x⟩) (norm_nonneg _)

theorem diagonalDerivative_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j, ∀ s ∈ Icc 0 T, ∀ x, ‖diagonalDerivative A j s x‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := coefficient_spatial_derivative_bound h
  refine ⟨K, hK, fun j s hs x => ?_⟩
  have hc : ‖P201Specs.coordinate n j‖ = 1 := by
    simp [P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single]
  calc
    ‖diagonalDerivative A j s x‖ ≤ ‖fderiv ℝ (A j s) x‖ * ‖P201Specs.coordinate n j‖ :=
      (fderiv ℝ (A j s) x).le_opNorm _
    _ ≤ K := by simpa only [hc, mul_one] using hb j s hs x


theorem uniformNorm_bddAbove {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {M : LowerOrder n m 𝕜}
    (h : ∀ s ∈ Icc 0 T, ∀ x, ‖M s x‖ ≤ K) :
    BddAbove ((fun z : ℝ × P201Specs.Space n => ‖M z.1 z.2‖) '' slab n T) := by
  refine ⟨K, ?_⟩
  rintro _ ⟨⟨s,x⟩, hs, rfl⟩
  exact h s hs.1 x

theorem norm_le_uniformNorm {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {M : LowerOrder n m 𝕜}
    (h : ∀ s ∈ Icc 0 T, ∀ x, ‖M s x‖ ≤ K)
    {s : ℝ} (hs : s ∈ Icc 0 T) (x : P201Specs.Space n) :
    ‖M s x‖ ≤ uniformNorm T M := by
  exact le_csSup (uniformNorm_bddAbove h) ⟨(s,x), ⟨hs, mem_univ x⟩, rfl⟩

theorem uniformNorm_nonneg {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {M : LowerOrder n m 𝕜} (hT : 0 ≤ T)
    (h : ∀ s ∈ Icc 0 T, ∀ x, ‖M s x‖ ≤ K) :
    0 ≤ uniformNorm T M := by
  exact (norm_nonneg (M 0 0)).trans (norm_le_uniformNorm h ⟨le_rfl, hT⟩ 0)

theorem uniformNorm_le_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {M : LowerOrder n m 𝕜} (hT : 0 ≤ T)
    (h : ∀ s ∈ Icc 0 T, ∀ x, ‖M s x‖ ≤ K) :
    uniformNorm T M ≤ K := by
  refine csSup_le (s := ((fun z : ℝ × P201Specs.Space n => ‖M z.1 z.2‖) '' slab n T)) ?_ ?_
  · exact ⟨‖M 0 0‖, (0,0), ⟨⟨le_rfl, hT⟩, mem_univ _⟩, rfl⟩
  · rintro _ ⟨⟨s,x⟩, hs, rfl⟩
    exact h s hs.1 x

theorem hermitianPart_norm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜] (M : Operator m 𝕜) :
    ‖hermitianPart M‖ ≤ ‖M‖ := by
  have hhalf : (1 / 2 : 𝕜) = ((1 / 2 : ℝ) : 𝕜) := by
    simp only [RCLike.ofReal_div, RCLike.ofReal_one, RCLike.ofReal_ofNat]
  calc
    ‖hermitianPart M‖ = (1 / 2 : ℝ) * ‖M + M.adjoint‖ := by
      rw [hermitianPart, norm_smul, hhalf, RCLike.norm_ofReal]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖M‖ + ‖M.adjoint‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖M‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

theorem hermitianPart_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc 0 T, ∀ x, ‖hermitianPart (B s x)‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := h.2.2.2
  exact ⟨K, hK, fun s hs x => (hermitianPart_norm_le (B s x)).trans (hb s hs x)⟩


theorem energyConstant_nonneg {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (hT : 0 ≤ T) (h : CoefficientHypotheses T A B) :
    0 ≤ energyConstant T A B := by
  obtain ⟨K, hK, hd⟩ := diagonalDerivative_bound h
  obtain ⟨J, hJ, hb⟩ := hermitianPart_bound h
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => uniformNorm_nonneg hT (hd j))
  · exact uniformNorm_nonneg hT hb

theorem pointwise_energy_coefficient_le {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) {s : ℝ} (hs : s ∈ Icc 0 T)
    (x : P201Specs.Space n) :
    (1 / 2 : ℝ) * (∑ j, ‖diagonalDerivative A j s x‖) + ‖hermitianPart (B s x)‖ ≤
      energyConstant T A B := by
  obtain ⟨K, hK, hd⟩ := diagonalDerivative_bound h
  obtain ⟨J, hJ, hb⟩ := hermitianPart_bound h
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => norm_le_uniformNorm (hd j) hs x) (by norm_num)
  · exact norm_le_uniformNorm hb hs x


theorem coefficient_origin_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j, ∀ s ∈ Icc 0 T, ‖A j s 0‖ ≤ K := by
  classical
  have hex (j : Fin n) : ∃ K : ℝ, ∀ s ∈ Icc 0 T, ‖A j s 0‖ ≤ K := by
    have hc : ContinuousOn (fun s : ℝ => ‖A j s 0‖) (Icc 0 T) :=
      ((h.1 j).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, mem_univ _⟩)).norm
    obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hc
    exact ⟨K, fun s hs => hK ⟨s, hs, rfl⟩⟩
  choose K hK using hex
  refine ⟨∑ j, max (K j) 0, Finset.sum_nonneg (fun j _ => le_max_right _ _), fun j s hs => ?_⟩
  exact (hK j s hs).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun i _ => le_max_right (K i) 0) (Finset.mem_univ j)))

theorem coefficient_linear_growth {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) :
    ∃ L : ℝ, 0 < L ∧ ∀ s ∈ Icc 0 T, ∀ x (ν : P201Specs.Space n), ‖ν‖ = 1 →
      ‖∑ j, (ν j) • A j s x‖ ≤ L * (1 + ‖x‖) := by
  obtain ⟨K, hK, hA0⟩ := coefficient_origin_bound h
  obtain ⟨D, hD, hAD⟩ := coefficient_spatial_derivative_bound h
  let L : ℝ := (n : ℝ) * (K + D) + 1
  have hL : 0 < L := by positivity
  refine ⟨L, hL, fun s hs x ν hν => ?_⟩
  have hg (j : Fin n) : ‖A j s x‖ ≤ K + D * ‖x‖ := by
    exact (norm_le_origin_add_derivative_bound (A j s) D
      ((coefficient_section_contDiff h j hs).differentiable (by simp)) (hAD j s hs) x).trans
      (add_le_add (hA0 j s hs) le_rfl)
  calc
    ‖∑ j, (ν j) • A j s x‖ ≤ ∑ j, ‖(ν j) • A j s x‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A j s x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      simpa only [hν] using (PiLp.norm_apply_le ν j)
    _ ≤ ∑ j : Fin n, (K + D * ‖x‖) := Finset.sum_le_sum fun j _ => hg j
    _ = (n : ℝ) * (K + D * ‖x‖) := by simp; ring
    _ ≤ L * (1 + ‖x‖) := by
      dsimp [L]
      nlinarith [norm_nonneg x, mul_nonneg (show (0 : ℝ) ≤ n by positivity) hD,
        mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ n by positivity) hK) (norm_nonneg x)]


theorem diagonalDerivative_norm_le_uniformNorm {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) (j : Fin n) {s : ℝ} (hs : s ∈ Icc 0 T)
    (x : P201Specs.Space n) :
    ‖diagonalDerivative A j s x‖ ≤ uniformNorm T (diagonalDerivative A j) := by
  obtain ⟨K, _, hb⟩ := diagonalDerivative_bound h
  exact norm_le_uniformNorm (hb j) hs x

theorem hermitianPart_norm_le_uniformNorm {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) {s : ℝ} (hs : s ∈ Icc 0 T)
    (x : P201Specs.Space n) :
    ‖hermitianPart (B s x)‖ ≤ uniformNorm T (fun s x => hermitianPart (B s x)) := by
  obtain ⟨K, _, hb⟩ := hermitianPart_bound h
  exact norm_le_uniformNorm hb hs x

theorem pointwise_energy_uniform_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) {s : ℝ} (hs : s ∈ Icc 0 T)
    (x : P201Specs.Space n) (u ut f : Fiber 𝕜 m) (dx : Fin n → Fiber 𝕜 m)
    (hpde : ut + (∑ j, A j s x (dx j)) + B s x u = f) :
    RCLike.re (inner 𝕜 u ut) +
      (∑ j, (RCLike.re (inner 𝕜 u (diagonalDerivative A j s x u)) / 2 +
        RCLike.re (inner 𝕜 u (A j s x (dx j))))) ≤
      energyConstant T A B * ‖u‖ ^ 2 + ‖u‖ * ‖f‖ := by
  exact (pointwise_energy_bound (fun j => A j s x) (fun j => diagonalDerivative A j s x)
    (B s x) u ut f dx hpde).trans
      (add_le_add (mul_le_mul_of_nonneg_right (pointwise_energy_coefficient_le h hs x)
        (sq_nonneg ‖u‖)) le_rfl)


section Cutoffs
section Integration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

theorem compact_weight_integration_by_parts {χ q : E → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hq : ContDiff ℝ 1 q)
    (hχK : HasCompactSupport χ) (v : E) :
    (∫ x, χ x * fderiv ℝ q x v ∂μ) =
      -(∫ x, fderiv ℝ χ x v * q x ∂μ) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).mul hq.continuous)
      |>.integrable_of_hasCompactSupport (hχK.fderiv_apply ℝ v).mul_right
  · exact (hχ.continuous.mul ((hq.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport hχK.mul_right
  · exact (hχ.continuous.mul hq.continuous).integrable_of_hasCompactSupport hχK.mul_right
  · exact fun x _ => hχ.differentiable (by simp) x
  · exact fun x _ => hq.differentiable (by simp) x

end Integration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cutoffArg (L a s : ℝ) (x : E) : ℝ :=
  (Real.exp (2 * L * s) * (1 + ‖x‖ ^ 2) - a) / a

def cutoff (L a s : ℝ) (x : E) : ℝ :=
  1 - Real.smoothTransition (cutoffArg L a s x)

theorem cutoff_nonneg (L a s : ℝ) (x : E) :
    0 ≤ cutoff L a s x := sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem cutoff_le_one (L a s : ℝ) (x : E) :
    cutoff L a s x ≤ 1 := by
  have := Real.smoothTransition.nonneg (cutoffArg L a s x)
  dsimp [cutoff]
  linarith

theorem cutoff_eq_one {L a s : ℝ} {x : E}
    (ha : 0 < a) (h : Real.exp (2 * L * s) * (1 + ‖x‖ ^ 2) ≤ a) :
    cutoff L a s x = 1 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) ha.le

theorem cutoff_eq_zero {L a s : ℝ} {x : E}
    (ha : 0 < a) (h : 2 * a ≤ Real.exp (2 * L * s) * (1 + ‖x‖ ^ 2)) :
    cutoff L a s x = 0 := by
  rw [cutoff, Real.smoothTransition.one_of_one_le, sub_self]
  exact (le_div_iff₀ ha).mpr (by linarith)

theorem cutoff_contDiff (L a s : ℝ) :
    ContDiff ℝ ∞ (cutoff L a s : E → ℝ) := by
  unfold cutoff cutoffArg
  have hnormSmooth : ContDiff ℝ ∞ (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul (contDiff_const.add hnormSmooth)).sub contDiff_const).div_const a))

theorem cutoff_hasCompactSupport [FiniteDimensional ℝ E] (L a s : ℝ) (ha : 0 < a) :
    HasCompactSupport (cutoff L a s : E → ℝ) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E)
    (Real.sqrt (2 * a / Real.exp (2 * L * s))))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn : ‖x‖ ^ 2 < 2 * a / Real.exp (2 * L * s) := by
    by_contra! hn
    have hmul := (div_le_iff₀ (Real.exp_pos (2 * L * s))).mp hn
    have hz : cutoff L a s x = 0 := cutoff_eq_zero ha (by nlinarith [Real.exp_pos (2 * L * s)])
    exact hx hz
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hn.le

theorem cutoff_hasDerivAt_time (L a s : ℝ) (x : E) :
    HasDerivAt (fun r => cutoff L a r x)
      (-deriv Real.smoothTransition (cutoffArg L a s x) *
        (2 * L * Real.exp (2 * L * s) * (1 + ‖x‖ ^ 2) / a)) s := by
  have hθ : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have harg := (((((hasDerivAt_id s).const_mul (2 * L)).exp).mul_const
    (1 + ‖x‖ ^ 2)).sub_const a).div_const a
  have h := (hasDerivAt_const s 1).sub ((hθ _).hasDerivAt.comp s harg)
  convert h using 1
  · rfl
  · dsimp [cutoffArg]
    ring

theorem cutoff_fderiv_apply (L a s : ℝ) (x v : E) :
    fderiv ℝ (cutoff L a s) x v =
      -deriv Real.smoothTransition (cutoffArg L a s x) *
        (Real.exp (2 * L * s) * (2 * inner ℝ x v) / a) := by
  have hθ : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hnorm : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have harg := (((hnorm.const_add 1).const_mul (Real.exp (2 * L * s))).sub_const a).mul_const a⁻¹
  have h := (hasFDerivAt_const (1 : ℝ) x).sub ((hθ _).hasFDerivAt.comp x harg)
  unfold cutoff
  simp only [cutoffArg, div_eq_mul_inv]
  change HasFDerivAt (fun y : E => 1 - Real.smoothTransition
    ((Real.exp (2 * L * s) * (1 + ‖y‖ ^ 2) - a) * a⁻¹)) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply, fderiv_eq_deriv_mul]
  ring

theorem cutoff_transport_nonpos {L a s e : ℝ} {x q : E}
    (ha : 0 < a) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hq : ‖q‖ ≤ L * Real.sqrt (1 + ‖x‖ ^ 2) * e) :
    deriv (fun r => cutoff L a r x) s * e + fderiv ℝ (cutoff L a s) x q ≤ 0 := by
  have hsqrt : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
  have hinner : -inner ℝ x q ≤ L * (1 + ‖x‖ ^ 2) * e := by
    calc
      -inner ℝ x q ≤ ‖x‖ * ‖q‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) * (L * Real.sqrt (1 + ‖x‖ ^ 2) * e) :=
        mul_le_mul hsqrt hq (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = L * (1 + ‖x‖ ^ 2) * e := by
        rw [show Real.sqrt (1 + ‖x‖ ^ 2) * (L * Real.sqrt (1 + ‖x‖ ^ 2) * e) =
          L * Real.sqrt (1 + ‖x‖ ^ 2) ^ 2 * e by ring, Real.sq_sqrt (by positivity)]
  rw [(cutoff_hasDerivAt_time L a s x).deriv, cutoff_fderiv_apply]
  calc
    _ = -((deriv Real.smoothTransition (cutoffArg L a s x) *
        (2 * Real.exp (2 * L * s) / a)) * (L * (1 + ‖x‖ ^ 2) * e + inner ℝ x q)) := by ring
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (mul_nonneg
      Real.smoothTransition.monotone.deriv_nonneg (by positivity)) (by linarith))

theorem cutoff_transport_sum_nonpos {ι : Type*} [Fintype ι]
    {K a s e : ℝ} {x : E} (v : ι → E) (q : ι → ℝ)
    (ha : 0 < a) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hv : ∀ j, |inner ℝ x (v j)| ≤ ‖x‖)
    (hq : (∑ j, |q j|) ≤ K * (1 + ‖x‖) * e) :
    deriv (fun r => cutoff (2 * K) a r x) s * e +
      (∑ j, fderiv ℝ (cutoff (2 * K) a s) x (v j) * q j) ≤ 0 := by
  have hpair : -(∑ j, inner ℝ x (v j) * q j) ≤ ‖x‖ * (∑ j, |q j|) := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      -(inner ℝ x (v j) * q j) ≤ |inner ℝ x (v j) * q j| := neg_le_abs _
      _ ≤ ‖x‖ * |q j| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hv j) (abs_nonneg _)
  have hpoly : ‖x‖ * (1 + ‖x‖) ≤ 2 * (1 + ‖x‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hinner : -(∑ j, inner ℝ x (v j) * q j) ≤ (2 * K) * (1 + ‖x‖ ^ 2) * e := by
    calc
      _ ≤ ‖x‖ * (∑ j, |q j|) := hpair
      _ ≤ ‖x‖ * (K * (1 + ‖x‖) * e) := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      _ = K * (‖x‖ * (1 + ‖x‖)) * e := by ring
      _ ≤ K * (2 * (1 + ‖x‖ ^ 2)) * e := by gcongr
      _ = (2 * K) * (1 + ‖x‖ ^ 2) * e := by ring
  rw [(cutoff_hasDerivAt_time (2 * K) a s x).deriv]
  simp_rw [cutoff_fderiv_apply]
  have hsum : (∑ j, -deriv Real.smoothTransition (cutoffArg (2 * K) a s x) *
      (Real.exp (2 * (2 * K) * s) * (2 * inner ℝ x (v j)) / a) * q j) =
      -(deriv Real.smoothTransition (cutoffArg (2 * K) a s x) *
        (2 * Real.exp (2 * (2 * K) * s) / a)) * (∑ j, inner ℝ x (v j) * q j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  calc
    _ = -((deriv Real.smoothTransition (cutoffArg (2 * K) a s x) *
        (2 * Real.exp (2 * (2 * K) * s) / a)) *
          ((2 * K) * (1 + ‖x‖ ^ 2) * e + ∑ j, inner ℝ x (v j) * q j)) := by ring
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (mul_nonneg
      Real.smoothTransition.monotone.deriv_nonneg (by positivity)) (by linarith))


theorem cutoff_joint_contDiff (L a : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (cutoff L a : ℝ → E → ℝ)) := by
  have hnormSmooth : ContDiff ℝ ∞ (fun z : ℝ × E => ‖z.2‖ ^ 2) :=
    contDiff_snd.norm_sq ℝ
  unfold cutoff cutoffArg Function.uncurry
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((((contDiff_const.mul contDiff_fst).exp).mul
      (contDiff_const.add hnormSmooth)).sub contDiff_const).div_const a))

def cutoffTime (L a s : ℝ) (x : E) : ℝ :=
  -deriv Real.smoothTransition (cutoffArg L a s x) *
    (2 * L * Real.exp (2 * L * s) * (1 + ‖x‖ ^ 2) / a)

theorem cutoffTime_eq_deriv (L a s : ℝ) (x : E) :
    cutoffTime L a s x = deriv (fun r => cutoff L a r x) s :=
  (cutoff_hasDerivAt_time L a s x).deriv.symm

theorem cutoffTime_joint_continuous (L a : ℝ) :
    Continuous (Function.uncurry (cutoffTime L a : ℝ → E → ℝ)) := by
  have harg : Continuous (Function.uncurry (cutoffArg L a : ℝ → E → ℝ)) := by
    unfold cutoffArg Function.uncurry
    fun_prop
  have hθ' : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by simp)
  unfold cutoffTime Function.uncurry
  exact ((hθ'.comp harg).neg).mul (by fun_prop)

theorem cutoffSpatial_joint_continuous (L a : ℝ) (v : E) :
    Continuous (fun z : ℝ × E => fderiv ℝ (cutoff L a z.1) z.2 v) := by
  simp_rw [cutoff_fderiv_apply]
  have harg : Continuous (Function.uncurry (cutoffArg L a : ℝ → E → ℝ)) := by
    unfold cutoffArg Function.uncurry
    fun_prop
  have hθ' : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by simp)
  exact ((hθ'.comp harg).neg).mul (by fun_prop)

theorem smoothTransition_deriv_zero_of_one_lt {z : ℝ} (hz : 1 < z) :
    deriv Real.smoothTransition z = 0 := by
  have hEq : Real.smoothTransition =ᶠ[𝓝 z] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds hz] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  simpa only [deriv_const] using hEq.deriv_eq

theorem cutoffArg_one_lt_of_not_mem {L a s : ℝ} {x : E}
    (hL : 0 ≤ L) (ha : 0 < a) (hs : 0 ≤ s)
    (hx : x ∉ Metric.closedBall (0 : E) (Real.sqrt (2 * a))) :
    1 < cutoffArg L a s x := by
  have hnorm : Real.sqrt (2 * a) < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * a by positivity)
  have hsq : 2 * a < ‖x‖ ^ 2 := by nlinarith [Real.sqrt_nonneg (2 * a)]
  have hexp : 1 ≤ Real.exp (2 * L * s) := Real.one_le_exp_iff.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hexp (show 0 ≤ 1 + ‖x‖ ^ 2 by positivity)
  unfold cutoffArg
  exact (lt_div_iff₀ ha).mpr (by nlinarith)

theorem cutoff_common_support {L a s : ℝ} {x : E}
    (hL : 0 ≤ L) (ha : 0 < a) (hs : 0 ≤ s)
    (hx : x ∉ Metric.closedBall (0 : E) (Real.sqrt (2 * a))) :
    cutoff L a s x = 0 ∧ cutoffTime L a s x = 0 := by
  have harg := cutoffArg_one_lt_of_not_mem hL ha hs hx
  constructor
  · unfold cutoff
    rw [Real.smoothTransition.one_of_one_le harg.le, sub_self]
  · unfold cutoffTime
    rw [smoothTransition_deriv_zero_of_one_lt harg]
    simp

theorem cutoff_terminal_plateau {L t R : ℝ} {x : E} (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) :
    cutoff L (Real.exp (2 * L * t) * (1 + R ^ 2)) t x = 1 := by
  apply cutoff_eq_one (by positivity)
  gcongr

end Cutoffs


theorem coefficient_sum_norm_linear_growth {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) :
    ∃ L : ℝ, 0 < L ∧ ∀ s ∈ Icc 0 T, ∀ x,
      (∑ j, ‖A j s x‖) ≤ L * (1 + ‖x‖) := by
  obtain ⟨K, hK, hA0⟩ := coefficient_origin_bound h
  obtain ⟨D, hD, hAD⟩ := coefficient_spatial_derivative_bound h
  let L : ℝ := (n : ℝ) * (K + D) + 1
  have hL : 0 < L := by positivity
  refine ⟨L, hL, fun s hs x => ?_⟩
  have hg (j : Fin n) : ‖A j s x‖ ≤ K + D * ‖x‖ := by
    exact (norm_le_origin_add_derivative_bound (A j s) D
      ((coefficient_section_contDiff h j hs).differentiable (by simp)) (hAD j s hs) x).trans
      (add_le_add (hA0 j s hs) le_rfl)
  calc
    (∑ j, ‖A j s x‖) ≤ ∑ j : Fin n, (K + D * ‖x‖) := Finset.sum_le_sum fun j _ => hg j
    _ = (n : ℝ) * (K + D * ‖x‖) := by simp; ring
    _ ≤ L * (1 + ‖x‖) := by
      dsimp [L]
      nlinarith [norm_nonneg x, mul_nonneg (show (0 : ℝ) ≤ n by positivity) hD,
        mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ n by positivity) hK) (norm_nonneg x)]

theorem scalar_flux_sum_linear_growth {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (h : CoefficientHypotheses T A B) :
    ∃ L : ℝ, 0 < L ∧ ∀ s ∈ Icc 0 T, ∀ x (v : Fiber 𝕜 m),
      (∑ j, |RCLike.re (inner 𝕜 v (A j s x v)) / 2|) ≤
        L * (1 + ‖x‖) * (‖v‖ ^ 2 / 2) := by
  obtain ⟨L, hL, hb⟩ := coefficient_sum_norm_linear_growth h
  refine ⟨L, hL, fun s hs x v => ?_⟩
  calc
    (∑ j, |RCLike.re (inner 𝕜 v (A j s x v)) / 2|) ≤
        ∑ j, ‖A j s x‖ * (‖v‖ ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro j _
      have hq := realPart_quadratic_bound (A j s x) v
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      nlinarith
    _ = (∑ j, ‖A j s x‖) * (‖v‖ ^ 2 / 2) := by rw [Finset.sum_mul]
    _ ≤ L * (1 + ‖x‖) * (‖v‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (hb s hs x) (by positivity)

theorem coordinate_inner_abs_le_norm {n : ℕ} (x : P201Specs.Space n) (j : Fin n) :
    |inner ℝ x (P201Specs.coordinate n j)| ≤ ‖x‖ := by
  have hc : ‖P201Specs.coordinate n j‖ = 1 := by
    simp [P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single]
  simpa only [Real.norm_eq_abs, hc, mul_one] using norm_inner_le_norm (𝕜 := ℝ) x (P201Specs.coordinate n j)

theorem source_norm_integrable_Icc {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {f : Field n m 𝕜} (hf : HasL1L2Source T f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntegrableOn (fun s => l2Norm (f s)) (Icc 0 t) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact (source_norm_integrable hf).mono_set fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩

theorem source_memLp_ae_Icc {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {f : Field n m 𝕜} (hf : HasL1L2Source T f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ s ∂volume.restrict (Icc 0 t), MemLp (f s) 2 volume := by
  obtain ⟨F, hF, hrep⟩ := hf
  rw [← restrict_Ioo_eq_restrict_Icc]
  have hrep' := ae_restrict_of_ae_restrict_of_subset
    (show Ioo 0 t ⊆ Ioo 0 T from fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩) hrep
  filter_upwards [hrep'] with s hs
  exact (memLp_congr_ae hs).2 (MeasureTheory.Lp.memLp (F s))


theorem operator_apply_bilinear_real {m : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    IsBoundedBilinearMap ℝ (fun p : Operator m 𝕜 × Fiber 𝕜 m => p.1 p.2) := by
  constructor
  · intro M N v
    rfl
  · intro r M v
    rfl
  · intro M v w
    exact M.map_add v w
  · intro r M v
    exact M.map_smul_of_tower r v
  · exact ⟨1, zero_lt_one, fun M v => by simpa only [one_mul] using M.le_opNorm v⟩

def energyDensity {n m : ℕ} {𝕜 : Type} [RCLike 𝕜] (u : Field n m 𝕜) :
    ℝ → P201Specs.Space n → ℝ := fun s x => ‖u s x‖ ^ 2 / 2

def energyFlux {n m : ℕ} {𝕜 : Type} [RCLike 𝕜] (A : Principal n m 𝕜) (u : Field n m 𝕜)
    (j : Fin n) : ℝ → P201Specs.Space n → ℝ :=
  fun s x => RCLike.re (inner 𝕜 (u s x) (A j s x (u s x))) / 2

theorem energy_density_contDiffOn {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜} {f u : Field n m 𝕜}
    (hu : IsSmoothSolution T A B f u) :
    ContDiffOn ℝ 1 (Function.uncurry (energyDensity u)) (slab n T) := by
  exact (((hu.1.of_le (by simp)).norm_sq 𝕜).div_const 2)

theorem energy_flux_contDiffOn {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜} {f u : Field n m 𝕜}
    (hA : CoefficientHypotheses T A B) (hu : IsSmoothSolution T A B f u) (j : Fin n) :
    ContDiffOn ℝ 1 (Function.uncurry (energyFlux A u j)) (slab n T) := by
  have hAu : ContDiffOn ℝ 1 (fun z : ℝ × P201Specs.Space n => A j z.1 z.2 (u z.1 z.2))
      (slab n T) :=
    operator_apply_bilinear_real.contDiff.comp₂_contDiffOn (hA.1 j) (hu.1.of_le (by simp))
  exact (RCLike.reCLM.contDiff.comp_contDiffOn ((hu.1.of_le (by simp)).inner 𝕜 hAu)).div_const 2

def slabTimeDerivative {n : ℕ} (T : ℝ) (e : ℝ → P201Specs.Space n → ℝ) :
    ℝ → P201Specs.Space n → ℝ :=
  fun s x => fderivWithin ℝ (Function.uncurry e) (slab n T) (s,x) (1,0)

def slabSpatialDerivative {n : ℕ} (T : ℝ) (e : ℝ → P201Specs.Space n → ℝ)
    (j : Fin n) : ℝ → P201Specs.Space n → ℝ :=
  fun s x => fderivWithin ℝ (Function.uncurry e) (slab n T) (s,x)
    (0,P201Specs.coordinate n j)

theorem slab_time_derivative_continuous {n : ℕ} {T : ℝ} (hT : 0 < T)
    {e : ℝ → P201Specs.Space n → ℝ}
    (he : ContDiffOn ℝ 1 (Function.uncurry e) (slab n T)) :
    ContinuousOn (Function.uncurry (slabTimeDerivative T e)) (slab n T) := by
  exact (he.continuousOn_fderivWithin ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ)
    le_rfl).clm_apply continuousOn_const

theorem slab_spatial_derivative_continuous {n : ℕ} {T : ℝ} (hT : 0 < T)
    {e : ℝ → P201Specs.Space n → ℝ}
    (he : ContDiffOn ℝ 1 (Function.uncurry e) (slab n T)) (j : Fin n) :
    ContinuousOn (Function.uncurry (slabSpatialDerivative T e j)) (slab n T) := by
  exact (he.continuousOn_fderivWithin ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ)
    le_rfl).clm_apply continuousOn_const

theorem hasDerivAt_slab_time_derivative {n : ℕ} {T : ℝ}
    {e : ℝ → P201Specs.Space n → ℝ}
    (he : ContDiffOn ℝ 1 (Function.uncurry e) (slab n T))
    {s : ℝ} (hs : s ∈ Ioo 0 T) (x : P201Specs.Space n) :
    HasDerivAt (fun r => e r x) (slabTimeDerivative T e s x) s := by
  have hsnhds : slab n T ∈ 𝓝 (s,x) :=
    prod_mem_nhds (Icc_mem_nhds hs.1 hs.2) Filter.univ_mem
  have hd := (he.contDiffAt hsnhds).differentiableAt one_ne_zero
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  rw [show slabTimeDerivative T e s x = fderiv ℝ (Function.uncurry e) (s,x) (1,0) by
    simp only [slabTimeDerivative, fderivWithin_of_mem_nhds hsnhds]]
  convert! hcomp using 1


theorem slab_section_hasFDerivAt {n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {T : ℝ}
    {e : ℝ → P201Specs.Space n → Y}
    (he : ContDiffOn ℝ 1 (Function.uncurry e) (slab n T))
    {s : ℝ} (hs : s ∈ Icc 0 T) (x : P201Specs.Space n) :
    HasFDerivAt (e s)
      ((fderivWithin ℝ (Function.uncurry e) (slab n T) (s,x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n))) x := by
  have hg := (he.differentiableOn (by simp) (s,x) ⟨hs, mem_univ x⟩).hasFDerivWithinAt
  have hin : HasFDerivAt (fun y : P201Specs.Space n => (s,y))
      (ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n)) x := by
    simpa using ((ContinuousLinearMap.inr ℝ ℝ (P201Specs.Space n)).hasFDerivAt
      (x := x)).add_const (s,0)
  exact (hg.comp x hin.hasFDerivWithinAt (s := univ)
    (fun y _ => ⟨hs, mem_univ y⟩)).hasFDerivAt (by simp)

theorem hasLineDerivAt_slab_spatial_derivative {n : ℕ} {T : ℝ}
    {e : ℝ → P201Specs.Space n → ℝ}
    (he : ContDiffOn ℝ 1 (Function.uncurry e) (slab n T))
    {s : ℝ} (hs : s ∈ Icc 0 T) (x : P201Specs.Space n) (j : Fin n) :
    HasLineDerivAt ℝ (e s) (slabSpatialDerivative T e j s x) x (P201Specs.coordinate n j) := by
  exact (slab_section_hasFDerivAt he hs x).hasLineDerivAt (P201Specs.coordinate n j)

theorem slab_time_derivative_energyDensity {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜} {f u : Field n m 𝕜}
    (hu : IsSmoothSolution T A B f u) {s : ℝ} (hs : s ∈ Ioo 0 T) (x : P201Specs.Space n) :
    slabTimeDerivative T (energyDensity u) s x =
      RCLike.re (inner 𝕜 (u s x) (deriv (fun r => u r x) s)) := by
  have hdu := (P201.Hyperbolic.SymmetricEnergy.smooth_solution_time_differentiable hu hs x).hasDerivAt
  have he : HasDerivAt (fun r => energyDensity u r x)
      (RCLike.re (inner 𝕜 (u s x) (deriv (fun r => u r x) s))) s := by
    have hi := hdu.inner 𝕜 hdu
    have hr := RCLike.reCLM.hasFDerivAt.comp_hasDerivAt s hi
    convert! hr.div_const 2 using 1
    · funext r
      change ‖u r x‖ ^ 2 / 2 = RCLike.re (inner 𝕜 (u r x) (u r x)) / 2
      simp only [inner_self_eq_norm_sq, RCLike.ofReal_re]
    · change RCLike.re (inner 𝕜 (u s x) (deriv (fun r => u r x) s)) =
        RCLike.re (inner 𝕜 (u s x) (deriv (fun r => u r x) s) +
          inner 𝕜 (deriv (fun r => u r x) s) (u s x)) / 2
      simp only [map_add]
      rw [inner_re_symm (deriv (fun r => u r x) s) (u s x)]
      ring
  exact (hasDerivAt_slab_time_derivative (energy_density_contDiffOn hu) hs x).unique he

theorem slab_spatial_derivative_energyFlux {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜} {f u : Field n m 𝕜}
    (hA : CoefficientHypotheses T A B) (hu : IsSmoothSolution T A B f u)
    {s : ℝ} (hs : s ∈ Icc 0 T) (x : P201Specs.Space n) (j : Fin n) :
    slabSpatialDerivative T (energyFlux A u j) j s x =
      RCLike.re (inner 𝕜 (u s x) (diagonalDerivative A j s x (u s x))) / 2 +
        RCLike.re (inner 𝕜 (u s x) (A j s x (fderiv ℝ (u s) x (P201Specs.coordinate n j)))) := by
  let v := P201Specs.coordinate n j
  have hxs : HasDerivAt (fun r : ℝ => x + r • v) v 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x) using 1 <;> simp
  have hAs : ContDiff ℝ 1 (A j s) :=
    (hA.1 j).comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨hs,mem_univ y⟩)
  have hUs := P201.Hyperbolic.SymmetricEnergy.smooth_solution_section hu hs
  have hAd : HasDerivAt (fun r : ℝ => A j s (x + r • v))
      (diagonalDerivative A j s x) 0 := by
    have hdA : HasFDerivAt (A j s) (fderiv ℝ (A j s) x) (x + (0:ℝ) • v) := by
      simpa only [zero_smul, add_zero] using (hAs.differentiable (by simp) x).hasFDerivAt
    convert! hdA.comp_hasDerivAt 0 hxs using 1
  have hUd : HasDerivAt (fun r : ℝ => u s (x + r • v))
      (fderiv ℝ (u s) x v) 0 := by
    have hdU : HasFDerivAt (u s) (fderiv ℝ (u s) x) (x + (0:ℝ) • v) := by
      simpa only [zero_smul, add_zero] using (hUs.differentiable (by simp) x).hasFDerivAt
    convert! hdU.comp_hasDerivAt 0 hxs using 1
  have hsym : IsSelfAdjoint (A j s (x + (0 : ℝ) • v)) := by
    simpa only [zero_smul, add_zero] using hA.2.2.1 j s hs x
  have hflux := P201.Hyperbolic.SymmetricEnergy.hasDerivAt_symmetric_flux hAd hUd hsym
  have hsp := hasLineDerivAt_slab_spatial_derivative (energy_flux_contDiffOn hA hu j) hs x j
  apply hsp.unique
  change HasDerivAt (fun r : ℝ => energyFlux A u j s (x + r • v)) _ 0
  convert! hflux using 1 <;> simp only [zero_smul, add_zero, v]


set_option maxHeartbeats 1000000 in
theorem energy_bound_of_flux_inequality {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (u f : Field n m 𝕜) (a : ℝ → P201Specs.Space n → ℝ)
    (q b : Fin n → ℝ → P201Specs.Space n → ℝ)
    (hu : ContinuousOn (Function.uncurry u) (slab n T))
    (ha : ContinuousOn (Function.uncurry a) (slab n T))
    (hq : ∀ j, ContinuousOn (Function.uncurry (q j)) (slab n T))
    (hb : ∀ j, ContinuousOn (Function.uncurry (b j)) (slab n T))
    (hder : ∀ s ∈ Ioo 0 T, ∀ x,
      HasDerivAt (fun r => ‖u r x‖ ^ 2 / 2) (a s x) s)
    (hqder : ∀ j s, s ∈ Icc 0 T → ∀ x,
      HasLineDerivAt ℝ (q j s) (b j s x) x (P201Specs.coordinate n j))
    (hpde : ∀ s ∈ Ioo 0 T, ∀ x,
      a s x + ∑ j, b j s x ≤ 2 * C * (‖u s x‖ ^ 2 / 2) + ‖u s x‖ * ‖f s x‖)
    (hflux : ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Icc 0 T, ∀ x,
      (∑ j, |q j s x|) ≤ K * (1 + ‖x‖) * (‖u s x‖ ^ 2 / 2))
    (hu0 : MemLp (u 0) 2 volume)
    (hFi : IntegrableOn (fun s => l2Norm (f s)) (Icc 0 T))
    (hfLp : ∀ᵐ s ∂volume.restrict (Icc 0 T), MemLp (f s) 2 volume)
    (hcoord : ∀ x : P201Specs.Space n, ∀ j, |inner ℝ x (P201Specs.coordinate n j)| ≤ ‖x‖) :
    MemLp (u T) 2 volume ∧ l2Norm (u T) ≤ Real.exp (C * T) *
      (l2Norm (u 0) + ∫ s in (0 : ℝ)..T, l2Norm (f s)) := by
  classical
  obtain ⟨K, hK, hKg⟩ := hflux
  have usec (s : ℝ) (hs : s ∈ Icc 0 T) : Continuous (u s) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hs, mem_univ x⟩)
  have sec {g : ℝ → P201Specs.Space n → ℝ}
      (hg : ContinuousOn (Function.uncurry g) (slab n T)) (s : ℝ) (hs : s ∈ Icc 0 T) :
      Continuous (g s) :=
    hg.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hs, mem_univ x⟩)
  let Bound := Real.exp (C * T) * (l2Norm (u 0) + ∫ s in (0 : ℝ)..T, l2Norm (f s))
  have hB : 0 ≤ Bound := by
    apply mul_nonneg (Real.exp_pos _).le
    exact add_nonneg lpNorm_nonneg
      (intervalIntegral.integral_nonneg_of_forall hT (fun _ => lpNorm_nonneg))
  apply ball_exhaustion (u T) Bound hB (usec T ⟨hT, le_rfl⟩).aestronglyMeasurable
  intro R hR
  let α : ℝ := Real.exp (2 * (2 * K) * T) * (1 + R ^ 2)
  have hα : 0 < α := by dsimp [α]; positivity
  let χ : ℝ → P201Specs.Space n → ℝ := cutoff (2 * K) α
  let c : ℝ → P201Specs.Space n → ℝ := cutoffTime (2 * K) α
  let e : ℝ → P201Specs.Space n → ℝ := fun s x => ‖u s x‖ ^ 2 / 2
  let E : ℝ → ℝ := fun s => ∫ x, χ s x * e s x
  let D : ℝ → ℝ := fun s => ∫ x, c s x * e s x + χ s x * a s x
  let S : Set (P201Specs.Space n) := Metric.closedBall 0 (Real.sqrt (2 * α))
  have hS : IsCompact S := isCompact_closedBall _ _
  have he : ContinuousOn (Function.uncurry e) (slab n T) := (hu.norm.pow 2).div_const 2
  have hχ : ContinuousOn (Function.uncurry χ) (slab n T) :=
    (cutoff_joint_contDiff (2 * K) α).continuous.continuousOn
  have hc : ContinuousOn (Function.uncurry c) (slab n T) :=
    (cutoffTime_joint_continuous (2 * K) α).continuousOn
  have χsec (s : ℝ) : Continuous (χ s) := (cutoff_contDiff (2 * K) α s).continuous
  have χK (s : ℝ) : HasCompactSupport (χ s) := cutoff_hasCompactSupport (2 * K) α s hα
  have χsupport : ∀ s ∈ Icc 0 T, ∀ x ∉ S, χ s x = 0 :=
    fun s hs x hx => (cutoff_common_support (by positivity) hα hs.1 hx).1
  have csupport : ∀ s ∈ Icc 0 T, ∀ x ∉ S, c s x = 0 :=
    fun s hs x hx => (cutoff_common_support (by positivity) hα hs.1 hx).2
  have hcK (s) (hs : s ∈ Icc 0 T) : HasCompactSupport (c s) :=
    HasCompactSupport.intro hS (csupport s hs)
  have localcalculus := compact_cutoff_energy_derivative T e a χ c S hS he ha hχ hc
    χsupport csupport hder (fun s _ x => cutoff_hasDerivAt_time (2 * K) α s x)
  have huweighted (s : ℝ) (hs : s ∈ Icc 0 T) :
      MemLp (fun x => Real.sqrt (χ s x) • u s x) 2 volume := by
    apply ((χsec s).sqrt.smul (usec s hs)).memLp_of_hasCompactSupport
    exact HasCompactSupport.intro hS (fun x hx => by simp [χsupport s hs x hx])
  have normE (s : ℝ) (hs : s ∈ Icc 0 T) :
      lpNorm (fun x => Real.sqrt (χ s x) • u s x) 2 volume = Real.sqrt (2 * E s) := by
    rw [weighted_norm_eq_sqrt _ _ (cutoff_nonneg (2 * K) α s) (huweighted s hs).aestronglyMeasurable]
    congr 1
    dsimp [E, e]
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  have hEnn (s : ℝ) (hs : s ∈ Icc 0 T) : 0 ≤ E s := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (cutoff_nonneg (2 * K) α s x) (by dsimp [e]; positivity)
  have hDineq : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      D s ≤ 2 * C * E s + l2Norm (f s) * Real.sqrt (2 * E s) := by
    have hI : ∀ᵐ s ∂volume.restrict (Icc 0 T), s ∈ Ioo 0 T := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hfLp, hI] with s hfs hs
    have hsc : s ∈ Icc 0 T := mem_Icc_of_Ioo hs
    have hforce := weighted_source_bound (χ s) (u s) (f s) (χsec s).measurable
      (cutoff_nonneg (2 * K) α s) (cutoff_le_one (2 * K) α s)
      (huweighted s hsc) hfs
    have hχg : Integrable (fun x => χ s x * (‖u s x‖ * ‖f s x‖)) := by
      simpa only [mul_assoc] using hforce.1
    have hlocal := compact_cutoff_energy_bound C (e s) (a s) (χ s) (c s)
      (fun x => ‖u s x‖ * ‖f s x‖) (fun j => q j s) (fun j => b j s)
      (fun j x => fderiv ℝ (χ s) x (P201Specs.coordinate n j))
      (sec he s hsc) (sec ha s hsc) (χsec s) (sec hc s hsc)
      (fun j => sec (hq j) s hsc) (fun j => sec (hb j) s hsc)
      (fun j => ((cutoff_contDiff (2 * K) α s).continuous_fderiv (by simp)).clm_apply continuous_const)
      (χK s) (hcK s hsc) (fun j => (χK s).fderiv_apply ℝ _)
      (cutoff_nonneg (2 * K) α s)
      (fun j x => ((cutoff_contDiff (2 * K) α s).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _)
      (fun j x => hqder j s hsc x) (hpde s hs)
      (fun x => by
        simpa only [χ, c, ← cutoffTime_eq_deriv] using
          cutoff_transport_sum_nonpos (P201Specs.coordinate n) (fun j => q j s x)
            hα hK.le (show 0 ≤ e s x by dsimp [e]; positivity) (hcoord x) (hKg s hsc x)) hχg
    have hforce' : (∫ x, χ s x * (‖u s x‖ * ‖f s x‖)) ≤
        l2Norm (f s) * Real.sqrt (2 * E s) := by
      have hw := (normE s hsc).symm.trans
        (weighted_norm_eq_sqrt _ _ (cutoff_nonneg (2 * K) α s) (huweighted s hsc).aestronglyMeasurable)
      rw [← hw] at hforce
      simpa only [mul_assoc, l2Norm, mul_comm] using hforce.2
    exact hlocal.trans (add_le_add le_rfl hforce')
  have hcomp := sqrt_energy_comparison T C E D (fun s => l2Norm (f s)) hT hC
    localcalculus.1 localcalculus.2.1 localcalculus.2.2 hEnn hFi
    (ae_of_all _ (fun _ => lpNorm_nonneg)) hDineq
  have hinit : Real.sqrt (2 * E 0) ≤ l2Norm (u 0) := by
    rw [← normE 0 ⟨le_rfl, hT⟩]
    exact weighted_norm_le (χ 0) (u 0) (cutoff_le_one (2 * K) α 0) hu0
  have hterm : MemLp (u T) 2 (volume.restrict (Metric.ball 0 R)) ∧
      lpNorm (u T) 2 (volume.restrict (Metric.ball 0 R)) ≤ Real.sqrt (2 * E T) := by
    have hb := restricted_norm_le_weighted (χ T) (u T) (Metric.ball 0 R)
      Metric.isOpen_ball.measurableSet
      (fun x hx => cutoff_terminal_plateau hR.le (by
        have hx' : ‖x‖ < R := by
          simpa only [Metric.mem_ball, dist_zero_right] using hx
        exact hx'.le))
      (usec T ⟨hT, le_rfl⟩).aestronglyMeasurable (huweighted T ⟨hT, le_rfl⟩)
    simpa only [normE T ⟨hT, le_rfl⟩] using hb
  exact ⟨hterm.1, hterm.2.trans (hcomp.trans (mul_le_mul_of_nonneg_left
    (add_le_add hinit le_rfl) (Real.exp_pos _).le))⟩


set_option maxHeartbeats 1000000 in
theorem energy_estimate : EnergyEstimateStatement := by
  intro n m 𝕜 _ hn T hT A B hcoeff f u hu hu0 hf t ht
  by_cases hTzero : T = 0
  · have htzero : t = 0 := by
      apply le_antisymm _ ht.1
      simpa only [hTzero] using ht.2
    subst t
    refine ⟨hu0, ?_⟩
    simp only [mul_zero, Real.exp_zero, intervalIntegral.integral_same, add_zero, one_mul,
      le_refl]
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
  let a := slabTimeDerivative T (energyDensity u)
  let q := energyFlux A u
  let b := fun j => slabSpatialDerivative T (q j) j
  have hslab : slab n t ⊆ slab n T := by
    rintro ⟨s,x⟩ ⟨hs,hx⟩
    exact ⟨⟨hs.1,hs.2.trans ht.2⟩,hx⟩
  have htime {s : ℝ} (hs : s ∈ Icc 0 t) : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
  have htime' {s : ℝ} (hs : s ∈ Ioo 0 t) : s ∈ Ioo 0 T := ⟨hs.1,hs.2.trans_le ht.2⟩
  apply energy_bound_of_flux_inequality t (energyConstant T A B) ht.1
    (energyConstant_nonneg hT hcoeff) u f a q b
    (hu.1.continuousOn.mono hslab)
    ((slab_time_derivative_continuous hTpos (energy_density_contDiffOn hu)).mono hslab)
    (fun j => (energy_flux_contDiffOn hcoeff hu j).continuousOn.mono hslab)
    (fun j => (slab_spatial_derivative_continuous hTpos
      (energy_flux_contDiffOn hcoeff hu j) j).mono hslab)
  · intro s hs x
    exact hasDerivAt_slab_time_derivative (energy_density_contDiffOn hu) (htime' hs) x
  · intro j s hs x
    exact hasLineDerivAt_slab_spatial_derivative (energy_flux_contDiffOn hcoeff hu j) (htime hs) x j
  · intro s hs x
    change slabTimeDerivative T (energyDensity u) s x +
      ∑ j, slabSpatialDerivative T (energyFlux A u j) j s x ≤ _
    rw [slab_time_derivative_energyDensity hu (htime' hs) x]
    simp_rw [slab_spatial_derivative_energyFlux hcoeff hu (htime (mem_Icc_of_Ioo hs)) x]
    convert pointwise_energy_uniform_bound hcoeff (htime (mem_Icc_of_Ioo hs)) x
      (u s x) (deriv (fun r => u r x) s) (f s x)
      (fun j => fderiv ℝ (u s) x (P201Specs.coordinate n j)) (hu.2 s (htime' hs) x) using 1 <;> ring
  · obtain ⟨K,hK,hg⟩ := scalar_flux_sum_linear_growth hcoeff
    exact ⟨K,hK,fun s hs x => hg s (htime hs) x (u s x)⟩
  · exact hu0
  · exact source_norm_integrable_Icc hf ht
  · exact source_memLp_ae_Icc hf ht
  · exact coordinate_inner_abs_le_norm

theorem difference_estimate : DifferenceEstimateStatement :=
  difference_estimate_of_energy_estimate energy_estimate

theorem uniqueness : UniquenessStatement :=
  uniqueness_of_difference_estimate difference_estimate


end P201.Hyperbolic.SymmetricEnergy
