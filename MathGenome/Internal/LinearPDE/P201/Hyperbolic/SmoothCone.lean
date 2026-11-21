import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SmoothCone
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C12.InfinitesimalFluxAndCirculation
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology ContDiff ENNReal
namespace P201.SmoothCone
open P201Specs.SmoothCone

/-- The boundary flux of a scalar wave is dominated by its inward moving
boundary energy. This applies to real and complex scalars. -/
theorem boundaryFlux_nonpos {𝕜 : Type} [RCLike 𝕜] {c m : ℝ}
    (hc : 0 ≤ c) (v q : 𝕜) (hq : ‖q‖ ≤ m) :
    c ^ 2 * RCLike.re (star v * q) -
      c * (‖v‖ ^ 2 + c ^ 2 * m ^ 2) / 2 ≤ 0 := by
  have hm : 0 ≤ m := (norm_nonneg q).trans hq
  have hprod : RCLike.re (star v * q) ≤ ‖v‖ * m := by
    calc
      RCLike.re (star v * q) ≤ ‖star v * q‖ := RCLike.re_le_norm _
      _ = ‖v‖ * ‖q‖ := by rw [norm_mul, norm_star]
      _ ≤ ‖v‖ * m := mul_le_mul_of_nonneg_left hq (norm_nonneg v)
  have hbound := mul_le_mul_of_nonneg_left hprod (sq_nonneg c)
  have hs := mul_nonneg hc (sq_nonneg (‖v‖ - c * m))
  nlinarith

/-- Taking real parts coordinatewise contracts the Euclidean norm. -/
theorem euclidean_re_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (g : EuclideanSpace 𝕜 (Fin n)) :
    ‖WithLp.toLp 2 (fun i => RCLike.re (g i))‖ ≤ ‖g‖ := by
  have hh : ‖WithLp.toLp 2 (fun i => RCLike.re (g i))‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_sum fun i _ => sq_le_sq.mpr (by
      simpa only [abs_of_nonneg (norm_nonneg _)] using RCLike.abs_re_le_norm (g i))
  nlinarith [norm_nonneg g, norm_nonneg (WithLp.toLp 2 (fun i => RCLike.re (g i)))]

/-- The full wave flux has norm at most propagation speed times energy density.
In particular its outward normal component is at most that quantity. -/
theorem waveFlux_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} (hc : 0 ≤ c) (v : 𝕜) (g : EuclideanSpace 𝕜 (Fin n)) :
    ‖WithLp.toLp 2 (fun i => c ^ 2 * RCLike.re (star v * g i))‖ ≤
      c * (‖v‖ ^ 2 + c ^ 2 * ‖g‖ ^ 2) / 2 := by
  have hid : WithLp.toLp 2 (fun i => c ^ 2 * RCLike.re (star v * g i)) =
      c ^ 2 • WithLp.toLp 2 (fun i => RCLike.re ((star v • g) i)) := by
    rfl
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]
  have hh := mul_le_mul_of_nonneg_left (euclidean_re_norm_le (star v • g)) (sq_nonneg c)
  rw [norm_smul, norm_star] at hh
  have hs := mul_nonneg hc (sq_nonneg (‖v‖ - c * ‖g‖))
  nlinarith

/-- Earlier slices contain later slices. -/
theorem coneBall_antitone {n : ℕ} (a : P201Specs.Space n) (R : ℝ)
    {c s t : ℝ} (hc : 0 ≤ c) (hst : s ≤ t) :
    coneBall c a R t ⊆ coneBall c a R s := by
  apply ball_subset_ball
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hst hc) R

/-- This is the displacement step, independent of the wave equation. It uses
u(0) itself, since vanishing energy alone cannot fix an additive constant. -/
theorem displacement_eq_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T t : ℝ} {a : P201Specs.Space n} {u v : ℝ → P201Specs.Space n → 𝕜}
    (hc : 0 ≤ c) (ht : t ∈ Icc 0 T)
    (hderiv : ∀ s ∈ Icc 0 T, ∀ x ∈ coneBall c a R s,
      HasDerivWithinAt (fun r => u r x) (v s x) (Icc 0 T) s)
    (hinit : ∀ x ∈ coneBall c a R 0, u 0 x = 0)
    (hvel : ∀ s ∈ Icc 0 T, ∀ x ∈ coneBall c a R s, v s x = 0) :
    ∀ x ∈ coneBall c a R t, u t x = 0 := by
  intro x hx
  have hd : ∀ s ∈ Icc 0 t,
      HasDerivWithinAt (fun r => u r x) (0 : 𝕜) (Icc 0 t) s := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hxs := coneBall_antitone a R hc hs.2 hx
    rw [← hvel s hsT x hxs]
    exact (hderiv s hsT x hxs).mono (Icc_subset_Icc le_rfl ht.2)
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun s _ => le_refl ‖(0 : 𝕜)‖) t (right_mem_Icc.mpr ht.1)
  have heq : u t x = u 0 x := by
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  exact heq.trans (hinit x (coneBall_antitone a R hc ht.1 hx))

/-- Spatial regularity at a fixed time, including the time endpoints. -/
theorem spatial_regular {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Icc 0 T) (hx : x ∈ closedBall a (R - c * s)) :
    ContDiffAt ℝ 2 (u s) x := by
  have hr := h.displacement_regular (s, x) ⟨hs, hx⟩
  have hh := hr.comp (s := univ) x
    (contDiffWithinAt_const.prodMk contDiffWithinAt_id)
    (fun y _ => (show (s, y) ∈ timeSlab T from ⟨hs, mem_univ y⟩))
  exact contDiffWithinAt_univ.mp hh

/-- The same spatial continuity for the velocity. -/
theorem velocity_regular {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Icc 0 T) (hx : x ∈ closedBall a (R - c * s)) :
    ContDiffAt ℝ 1 (v s) x := by
  have hr := h.velocity_regular (s, x) ⟨hs, hx⟩
  have hh := hr.comp (s := univ) x
    (contDiffWithinAt_const.prodMk contDiffWithinAt_id)
    (fun y _ => (show (s, y) ∈ timeSlab T from ⟨hs, mem_univ y⟩))
  exact contDiffWithinAt_univ.mp hh

theorem spatialGradient_continuousAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {w : P201Specs.Space n → 𝕜} {x : P201Specs.Space n}
    (h : ContDiffAt ℝ 2 w x) : ContinuousAt (spatialGradient w) x := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => 𝕜)).continuousAt.comp
  exact continuousAt_pi.mpr fun i =>
    (h.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const

/-- For real solutions the gradient is the shared canonical gradient. -/
theorem spatialGradient_real {n : ℕ} (w : P201Specs.Space n → ℝ)
    (x : P201Specs.Space n) : spatialGradient w x = P201.gradient w x := rfl

/-- A spatial partial is the ambient differential applied to a spatial vector. -/
theorem spatial_fderiv_eq_ambient {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : ℝ → P201Specs.Space n → 𝕜} {s : ℝ} {x : P201Specs.Space n}
    (h : DifferentiableAt ℝ (Function.uncurry u) (s, x)) (i : Fin n) :
    fderiv ℝ (u s) x (P201Specs.coordinate n i) =
      fderiv ℝ (Function.uncurry u) (s, x) (0, P201Specs.coordinate n i) := by
  have hd := h.hasFDerivAt.comp x
    ((hasFDerivAt_const s x).prodMk (hasFDerivAt_id x))
  exact congrArg (fun L => L (P201Specs.coordinate n i)) hd.fderiv

/-- A local C² displacement has a local C¹ joint spatial gradient. -/
theorem spatialGradient_contDiffAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : ℝ → P201Specs.Space n → 𝕜} {z : ℝ × P201Specs.Space n}
    (h : ContDiffAt ℝ 2 (Function.uncurry u) z) :
    ContDiffAt ℝ 1 (fun y : ℝ × P201Specs.Space n => spatialGradient (u y.1) y.2) z := by
  have hd : ContDiffAt ℝ 1 (fun y : ℝ × P201Specs.Space n =>
      WithLp.toLp 2 (fun i => fderiv ℝ (Function.uncurry u) y (0, P201Specs.coordinate n i))) z := by
    apply PiLp.contDiff_toLp.contDiffAt.comp z
    apply contDiffAt_pi.mpr
    intro i
    exact (h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  apply hd.congr_of_eventuallyEq
  filter_upwards [h.eventually (by norm_num)] with y hy
  apply congrArg (WithLp.toLp 2)
  funext i
  exact spatial_fderiv_eq_ambient (hy.differentiableAt (by norm_num)) i

/-- Interior times admit ordinary ambient derivatives even on the lateral
spatial boundary; this does not require any extension to negative times. -/
theorem interior_regular {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ closedBall a (R - c * s)) :
    ContDiffAt ℝ 2 (Function.uncurry u) (s, x) ∧
      ContDiffAt ℝ 1 (Function.uncurry v) (s, x) := by
  have hn : timeSlab T ∈ 𝓝 (s, x) :=
    prod_mem_nhds (Icc_mem_nhds hs.1 hs.2) Filter.univ_mem
  exact ⟨(h.displacement_regular (s, x) ⟨Ioo_subset_Icc_self hs, hx⟩).contDiffAt hn,
    (h.velocity_regular (s, x) ⟨Ioo_subset_Icc_self hs, hx⟩).contDiffAt hn⟩

/-- On a nondegenerate time slab the ambient within derivative recovers each
spatial derivative, including at the two time endpoints. -/
theorem spatial_fderiv_eq_within {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Icc 0 T) (hx : x ∈ closedBall a (R - c * s)) (i : Fin n) :
    fderiv ℝ (u s) x (P201Specs.coordinate n i) =
      fderivWithin ℝ (Function.uncurry u) (timeSlab T) (s, x)
        (0, P201Specs.coordinate n i) := by
  have hu := (h.displacement_regular (s, x) ⟨hs, hx⟩).differentiableWithinAt
    (by norm_num)
  have hd := hu.hasFDerivWithinAt.comp_hasFDerivAt x
    ((hasFDerivAt_const s x).prodMk (hasFDerivAt_id x))
    (Filter.Eventually.of_forall (fun y => (show (s, y) ∈ timeSlab T from
      ⟨hs, mem_univ y⟩)))
  exact congrArg (fun L => L (P201Specs.coordinate n i)) hd.fderiv

/-- Joint continuity of the spatial gradient on the closed cone, with one-sided
time continuity at its endpoints. -/
theorem spatialGradient_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T : ℝ} {a : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (hT : 0 < T) (h : IsLocalSmoothWave c a R T u v f) :
    ContinuousOn (fun z : ℝ × P201Specs.Space n => spatialGradient (u z.1) z.2)
      (closedCone c a R T) := by
  have hslab : UniqueDiffOn ℝ (timeSlab T) :=
    (uniqueDiffOn_Icc hT).prod (uniqueDiffOn_univ (E := P201Specs.Space n))
  have hd : ContinuousOn (fderivWithin ℝ (Function.uncurry u) (timeSlab T))
      (closedCone c a R T) := by
    intro z hz
    exact ((h.displacement_regular z hz).continuousWithinAt_fderivWithin
      hslab (by norm_num) ⟨hz.1, mem_univ z.2⟩).mono (fun _ hy => ⟨hy.1, mem_univ _⟩)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => 𝕜)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  apply (hd.clm_apply (continuousOn_const (c := (0, P201Specs.coordinate n i)))).congr
  intro z hz
  exact spatial_fderiv_eq_within h hz.1 hz.2 i

/-- Finite local energy follows from the smoothness on the compact slice. -/
theorem energyDensity_integrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a : P201Specs.Space n} {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f) (hs : s ∈ Icc 0 T) :
    IntegrableOn (fun x => ‖v s x‖ ^ 2 + c ^ 2 * ‖spatialGradient (u s) x‖ ^ 2)
      (coneBall c a R s) := by
  have hv : ContinuousOn (v s) (closedBall a (R - c * s)) :=
    fun x hx => (velocity_regular h hs hx).continuousAt.continuousWithinAt
  have hg : ContinuousOn (spatialGradient (u s)) (closedBall a (R - c * s)) :=
    fun x hx => (spatialGradient_continuousAt (spatial_regular h hs hx)).continuousWithinAt
  exact ((hv.norm.pow 2).add (continuousOn_const.mul (hg.norm.pow 2))).integrableOn_compact
    (isCompact_closedBall _ _) |>.mono_set ball_subset_closedBall

theorem localEnergy_nonneg {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : P201Specs.Space n) (R : ℝ)
    (u v : ℝ → P201Specs.Space n → 𝕜) (s : ℝ) :
    0 ≤ localEnergy c a R u v s := by
  unfold localEnergy
  apply mul_nonneg (by norm_num)
  exact integral_nonneg fun x => add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Vanishing displacement on an open ball also makes its spatial gradient zero. -/
theorem spatialGradient_eq_zero_of_eq_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {w : P201Specs.Space n → 𝕜} {a x : P201Specs.Space n} {r : ℝ}
    (hw : ∀ y ∈ ball a r, w y = 0) (hx : x ∈ ball a r) :
    spatialGradient w x = 0 := by
  have heq : w =ᶠ[𝓝 x] (fun _ => (0 : 𝕜)) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) hw
  have hd : fderiv ℝ w x = 0 := by
    rw [heq.fderiv_eq, fderiv_fun_const]
    rfl
  simp only [spatialGradient, hd, zero_apply]
  rfl

/-- Zero local energy forces the velocity to vanish pointwise on the open slice. -/
theorem velocity_eq_zero_of_energy_eq_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a : P201Specs.Space n} {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f) (hs : s ∈ Icc 0 T)
    (hE : localEnergy c a R u v s = 0) :
    ∀ x ∈ coneBall c a R s, v s x = 0 := by
  have hi : (∫ x in coneBall c a R s,
      (‖v s x‖ ^ 2 + c ^ 2 * ‖spatialGradient (u s) x‖ ^ 2)) = 0 := by
    unfold localEnergy at hE
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => add_nonneg (sq_nonneg ‖v s x‖)
      (mul_nonneg (sq_nonneg c) (sq_nonneg ‖spatialGradient (u s) x‖)))
    (energyDensity_integrable h hs)).mp hi
  have hv : v s =ᵐ[volume.restrict (coneBall c a R s)] 0 := by
    filter_upwards [hae] with x hx
    change ‖v s x‖ ^ 2 + c ^ 2 * ‖spatialGradient (u s) x‖ ^ 2 = 0 at hx
    have hn : ‖v s x‖ = 0 := by
      have hh := mul_nonneg (sq_nonneg c) (sq_nonneg ‖spatialGradient (u s) x‖)
      nlinarith [sq_nonneg ‖v s x‖]
    exact norm_eq_zero.mp hn
  apply Measure.eqOn_open_of_ae_eq hv isOpen_ball _ continuousOn_const
  exact fun x hx => (velocity_regular h hs (ball_subset_closedBall hx)).continuousAt.continuousWithinAt

/-- Both initial data vanishing gives zero initial energy. -/
theorem initialEnergy_eq_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R : ℝ} {a : P201Specs.Space n} {u v : ℝ → P201Specs.Space n → 𝕜}
    (hu : ∀ x ∈ coneBall c a R 0, u 0 x = 0)
    (hv : ∀ x ∈ coneBall c a R 0, v 0 x = 0) :
    localEnergy c a R u v 0 = 0 := by
  unfold localEnergy
  rw [setIntegral_eq_zero_of_forall_eq_zero]
  · simp
  · intro x hx
    have hg := spatialGradient_eq_zero_of_eq_zero hu hx
    simp [hv x hx, hg]

/-- Zero forcing on a cone slice gives zero local forcing norm. -/
theorem localForcingNorm_eq_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R s : ℝ} {a : P201Specs.Space n} {f : ℝ → P201Specs.Space n → 𝕜}
    (hf : ∀ x ∈ coneBall c a R s, f s x = 0) :
    localForcingNorm c a R f s = 0 := by
  unfold localForcingNorm
  rw [setIntegral_eq_zero_of_forall_eq_zero]
  · exact Real.sqrt_zero
  · intro x hx
    simp [hf x hx]

/-- The forcing is continuous on each closed spatial slice. -/
theorem forcing_continuousOn_slice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a : P201Specs.Space n} {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f) (hs : s ∈ Icc 0 T) :
    ContinuousOn (f s) (closedBall a (R - c * s)) :=
  h.forcing_continuous.comp (continuousOn_const.prodMk continuousOn_id)
    (fun _ hx => ⟨hs, hx⟩)

/-- The square integrability needed in the forcing norm is entirely local. -/
theorem forcing_memLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a : P201Specs.Space n} {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f) (hs : s ∈ Icc 0 T) :
    MemLp (f s) 2 (volume.restrict (coneBall c a R s)) := by
  have hf := forcing_continuousOn_slice h hs
  apply (memLp_two_iff_integrable_sq_norm
    ((hf.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)).mpr
  exact ((hf.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)).mono_set
    ball_subset_closedBall

/-- The square-integral formula in the Spec equals the usual L² norm of the
forcing restricted by the indicator of the moving ball. -/
theorem localForcingNorm_eq_indicator_norm {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a : P201Specs.Space n} {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f) (hs : s ∈ Icc 0 T) :
    localForcingNorm c a R f s =
      (eLpNorm ((coneBall c a R s).indicator (f s)) 2 volume).toReal := by
  have hmeas : MeasurableSet (coneBall c a R s) := measurableSet_ball
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hmeas.nullMeasurableSet,
    toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (forcing_memLp h hs).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow]
  rfl

/-- The local velocity is square integrable, without a global energy premise. -/
theorem velocity_memLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a : P201Specs.Space n} {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f) (hs : s ∈ Icc 0 T) :
    MemLp (v s) 2 (volume.restrict (coneBall c a R s)) := by
  have hv : ContinuousOn (v s) (closedBall a (R - c * s)) :=
    fun x hx => (velocity_regular h hs hx).continuousAt.continuousWithinAt
  apply (memLp_two_iff_integrable_sq_norm
    ((hv.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)).mpr
  exact ((hv.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)).mono_set
    ball_subset_closedBall

/-- The spatial forcing pairing is bounded by the local L² forcing norm times
the square root of twice the local energy. -/
theorem forcingPairing_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a : P201Specs.Space n} {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f) (hs : s ∈ Icc 0 T) :
    (∫ x in coneBall c a R s, RCLike.re (star (v s x) * f s x)) ≤
      localForcingNorm c a R f s * Real.sqrt (2 * localEnergy c a R u v s) := by
  have hv : ContinuousOn (v s) (closedBall a (R - c * s)) :=
    fun x hx => (velocity_regular h hs hx).continuousAt.continuousWithinAt
  have hf := forcing_continuousOn_slice h hs
  have hpair : IntegrableOn (fun x => RCLike.re (star (v s x) * f s x)) (coneBall c a R s) :=
    (RCLike.continuous_re.comp_continuousOn (hv.star.mul hf)).integrableOn_compact
      (isCompact_closedBall _ _) |>.mono_set ball_subset_closedBall
  have hprod : IntegrableOn (fun x => ‖f s x‖ * ‖v s x‖) (coneBall c a R s) :=
    (hf.norm.mul hv.norm).integrableOn_compact
      (isCompact_closedBall _ _) |>.mono_set ball_subset_closedBall
  have hkin := (memLp_two_iff_integrable_sq_norm (velocity_memLp h hs).aestronglyMeasurable).mp
    (velocity_memLp h hs)
  have hkin_le : (∫ x in coneBall c a R s, ‖v s x‖ ^ 2) ≤ 2 * localEnergy c a R u v s := by
    have hi := integral_mono hkin (energyDensity_integrable h hs) (fun x =>
      le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) (sq_nonneg ‖spatialGradient (u s) x‖)))
    unfold localEnergy
    linarith
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp (f s) (ENNReal.ofReal 2) (volume.restrict (coneBall c a R s)) by
      simpa using forcing_memLp h hs)
    (show MemLp (v s) (ENNReal.ofReal 2) (volume.restrict (coneBall c a R s)) by
      simpa using velocity_memLp h hs)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hholder
  calc
    _ ≤ ∫ x in coneBall c a R s, ‖f s x‖ * ‖v s x‖ := integral_mono hpair hprod fun x => by
      calc
        RCLike.re (star (v s x) * f s x) ≤ ‖star (v s x) * f s x‖ := RCLike.re_le_norm _
        _ = ‖f s x‖ * ‖v s x‖ := by rw [norm_mul, norm_star, mul_comm]
    _ ≤ localForcingNorm c a R f s * Real.sqrt (∫ x in coneBall c a R s, ‖v s x‖ ^ 2) := hholder
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkin_le) (Real.sqrt_nonneg _)

/-- Linearity of the shared Laplacian under exactly local C² hypotheses. -/
theorem laplacian_sub {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {w₁ w₂ : P201Specs.Space n → 𝕜} {x : P201Specs.Space n}
    (h₁ : ContDiffAt ℝ 2 w₁ x) (h₂ : ContDiffAt ℝ 2 w₂ x) :
    P201Specs.laplacian (fun y => w₁ y - w₂ y) x =
      P201Specs.laplacian w₁ x - P201Specs.laplacian w₂ x := by
  have hsort (i : Fin n) : Multiset.sort ({i, i} : Multiset (Fin n)) (· ≤ ·) = [i, i] := by
    simp [Multiset.sort_cons]
  simp only [P201Specs.laplacian, P201Specs.multiPartial, P102.U4.multiPartial, hsort,
    P102.U4.partialWord, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y => fderiv ℝ (fun z => w₁ z - w₂ z) y (P201Specs.coordinate n i))
      =ᶠ[𝓝 x] (fun y => fderiv ℝ w₁ y (P201Specs.coordinate n i) -
        fderiv ℝ w₂ y (P201Specs.coordinate n i)) := by
    filter_upwards [h₁.eventually (by norm_num), h₂.eventually (by norm_num)] with y hy₁ hy₂
    rw [fderiv_fun_sub (hy₁.differentiableAt (by norm_num)) (hy₂.differentiableAt (by norm_num))]
    rfl
  rw [heq.fderiv_eq]
  have hd₁ : DifferentiableAt ℝ (fun y => fderiv ℝ w₁ y (P201Specs.coordinate n i)) x :=
    ((h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const (P201Specs.coordinate n i))
  have hd₂ : DifferentiableAt ℝ (fun y => fderiv ℝ w₂ y (P201Specs.coordinate n i)) x :=
    ((h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const (P201Specs.coordinate n i))
  rw [fderiv_fun_sub hd₁ hd₂]
  rfl

/-- Differences remain local classical waves; no global solution class is used. -/
theorem IsLocalSmoothWave.sub {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T : ℝ} {a : P201Specs.Space n}
    {u₁ v₁ f₁ u₂ v₂ f₂ : ℝ → P201Specs.Space n → 𝕜}
    (h₁ : P201Specs.SmoothCone.IsLocalSmoothWave c a R T u₁ v₁ f₁)
    (h₂ : P201Specs.SmoothCone.IsLocalSmoothWave c a R T u₂ v₂ f₂) :
    P201Specs.SmoothCone.IsLocalSmoothWave c a R T
      (fun s x => u₁ s x - u₂ s x) (fun s x => v₁ s x - v₂ s x)
      (fun s x => f₁ s x - f₂ s x) where
  displacement_regular z hz := (h₁.displacement_regular z hz).sub (h₂.displacement_regular z hz)
  velocity_regular z hz := (h₁.velocity_regular z hz).sub (h₂.velocity_regular z hz)
  forcing_continuous := h₁.forcing_continuous.sub h₂.forcing_continuous
  displacement_derivative s hs x hx :=
    (h₁.displacement_derivative s hs x hx).sub (h₂.displacement_derivative s hs x hx)
  wave_equation s hs x hx := by
    have hd := (h₁.wave_equation s hs x hx).sub (h₂.wave_equation s hs x hx)
    rw [laplacian_sub (spatial_regular h₁ hs hx) (spatial_regular h₂ hs hx), smul_sub]
    convert hd using 1; abel

/-- Regularizing the square root gives the sharp additive forcing estimate,
including when the initial energy is zero. Only interior derivatives are used. -/
theorem sqrt_energy_estimate {T : ℝ} (hT : 0 ≤ T)
    {E E' F : ℝ → ℝ}
    (hE : ContinuousOn E (Icc 0 T))
    (hE_nonneg : ∀ s ∈ Icc 0 T, 0 ≤ E s)
    (hderiv : ∀ s ∈ Ioo 0 T, HasDerivAt E (E' s) s)
    (hF_nonneg : ∀ s ∈ Icc 0 T, 0 ≤ F s)
    (hF_int : IntegrableOn F (Icc 0 T))
    (hbound : ∀ s ∈ Ioo 0 T, E' s ≤ F s * Real.sqrt (2 * E s)) :
    Real.sqrt (2 * E T) ≤ Real.sqrt (2 * E 0) + ∫ s in (0 : ℝ)..T, F s := by
  have hreg (δ : ℝ) (hδ : 0 < δ) :
      Real.sqrt (2 * E T) ≤
        Real.sqrt (2 * E 0 + δ) + ∫ s in (0 : ℝ)..T, F s := by
    have hpos (s : ℝ) (hs : s ∈ Icc 0 T) : 0 < 2 * E s + δ := by
      linarith [hE_nonneg s hs]
    have hd : ∀ s ∈ Ioo 0 T,
        HasDerivAt (fun r => Real.sqrt (2 * E r + δ))
          ((2 * E' s) / (2 * Real.sqrt (2 * E s + δ))) s := by
      intro s hs
      exact (((hderiv s hs).const_mul 2).add_const δ).sqrt
        (ne_of_gt (hpos s (Ioo_subset_Icc_self hs)))
    have hb : ∀ s ∈ Ioo 0 T,
        (2 * E' s) / (2 * Real.sqrt (2 * E s + δ)) ≤ F s := by
      intro s hs
      have hs' := Ioo_subset_Icc_self hs
      have hp : 0 < Real.sqrt (2 * E s + δ) := Real.sqrt_pos.mpr (hpos s hs')
      have hm : Real.sqrt (2 * E s) ≤ Real.sqrt (2 * E s + δ) :=
        Real.sqrt_le_sqrt (by linarith)
      have hh := (hbound s hs).trans
        (mul_le_mul_of_nonneg_left hm (hF_nonneg s hs'))
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 * E s + δ))).mpr
      nlinarith
    have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hT
      ((continuousOn_const.mul hE).add continuousOn_const).sqrt
      (fun s hs => (hd s hs).hasDerivWithinAt) hF_int hb
    dsimp only [Pi.mul_apply, Pi.add_apply] at hi
    have hm : Real.sqrt (2 * E T) ≤ Real.sqrt (2 * E T + δ) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have hlim : Tendsto
      (fun δ : ℝ => Real.sqrt (2 * E 0 + δ) + ∫ s in (0 : ℝ)..T, F s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (2 * E 0) + ∫ s in (0 : ℝ)..T, F s)) := by
    have hh : Continuous
        (fun δ : ℝ => Real.sqrt (2 * E 0 + δ) + ∫ s in (0 : ℝ)..T, F s) := by
      fun_prop
    simpa only [add_zero] using
      (hh.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hreg δ hδ

/-- Translation and dilation reduce a local ball integral to a fixed unit ball.
This is an identity of the actual Bochner integrals and Lebesgue normalization. -/
theorem integral_ball_pullback {n : ℕ} (g : P201Specs.Space n → ℝ)
    (a : P201Specs.Space n) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball a r, g x) =
      r ^ Module.finrank ℝ (P201Specs.Space n) *
        ∫ y in ball (0 : P201Specs.Space n) 1, g (a + r • y) := by
  have htrans := (measurePreserving_add_left (volume : Measure (P201Specs.Space n)) a).setIntegral_image_emb (Homeomorph.addLeft a).isClosedEmbedding.measurableEmbedding
      g (ball 0 r)
  have himage : (fun y : P201Specs.Space n => a + y) '' ball 0 r = ball a r := by
    simp
  rw [himage] at htrans
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (P201Specs.Space n)) (fun y => g (a + y)) (ball 0 1) hr
  rw [smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one,
    smul_eq_mul, ← htrans] at hscale
  calc
    _ = r ^ Module.finrank ℝ (P201Specs.Space n) *
        ((r ^ Module.finrank ℝ (P201Specs.Space n))⁻¹ * ∫ x in ball a r, g x) := by
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
    _ = _ := congrArg (fun z => r ^ Module.finrank ℝ (P201Specs.Space n) * z) hscale.symm

/-- Continuous local densities have continuous integrals on shrinking balls.
Only continuity on the compact closed cone is used. -/
theorem movingBall_integral_continuousOn {n : ℕ} {c R T : ℝ}
    {a : P201Specs.Space n} {g : ℝ × P201Specs.Space n → ℝ}
    (hc : 0 < c) (hTc : T < R / c)
    (hg : ContinuousOn g (closedCone c a R T)) :
    ContinuousOn (fun s => ∫ x in coneBall c a R s, g (s, x)) (Icc 0 T) := by
  have hr : ∀ s ∈ Icc 0 T, 0 < R - c * s := by
    intro s hs
    have hh := (lt_div_iff₀ hc).mp hTc
    nlinarith [mul_le_mul_of_nonneg_left hs.2 hc.le]
  let Φ : ℝ × P201Specs.Space n → ℝ × P201Specs.Space n :=
    fun z => (z.1, a + (R - c * z.1) • z.2)
  have hΦ : Continuous Φ := by dsimp [Φ]; fun_prop
  have hmaps : MapsTo Φ (Icc 0 T ×ˢ closedBall 0 1) (closedCone c a R T) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change dist (a + (R - c * z.1) • z.2) a ≤ R - c * z.1
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hr z.1 hz.1)]
    simpa using mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz.2) (hr z.1 hz.1).le
  have hcomp : ContinuousOn (g ∘ Φ) (Icc 0 T ×ˢ closedBall 0 1) :=
    hg.comp hΦ.continuousOn hmaps
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : P201Specs.Space n) 1)).bddAbove_image hcomp.norm
  have hI : ContinuousOn
      (fun s => ∫ y in ball (0 : P201Specs.Space n) 1, g (Φ (s, y))) (Icc 0 T) := by
    apply continuousOn_of_dominated (bound := fun _ => M)
    · intro s hs
      have hh := hcomp.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy => ⟨hs, ball_subset_closedBall hy⟩)
      exact hh.aestronglyMeasurable measurableSet_ball
    · intro s hs
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact hM (mem_image_of_mem _ ⟨hs, ball_subset_closedBall hy⟩)
    · exact integrableOn_const (measure_ball_lt_top.ne)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact hcomp.comp (continuousOn_id.prodMk continuousOn_const)
        (fun s hs => ⟨hs, ball_subset_closedBall hy⟩)
  have hprod : ContinuousOn
      (fun s => (R - c * s) ^ Module.finrank ℝ (P201Specs.Space n) *
        ∫ y in ball (0 : P201Specs.Space n) 1, g (Φ (s, y))) (Icc 0 T) :=
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).pow _).mul hI
  apply hprod.congr
  intro s hs
  exact integral_ball_pullback (fun x => g (s, x)) a (hr s hs)

/-- Local energy is continuous through both endpoints of the time interval. -/
theorem localEnergy_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T : ℝ} {a : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (hc : 0 < c) (hT : 0 ≤ T) (hTc : T < R / c)
    (h : IsLocalSmoothWave c a R T u v f) :
    ContinuousOn (localEnergy c a R u v) (Icc 0 T) := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    simpa only [Icc_self] using continuousOn_singleton (localEnergy c a R u v) 0
  have hv : ContinuousOn (Function.uncurry v) (closedCone c a R T) := by
    intro z hz
    exact (h.velocity_regular z hz).continuousWithinAt.mono
      (fun _ hy => ⟨hy.1, mem_univ _⟩)
  have hg := spatialGradient_continuousOn hT h
  exact continuousOn_const.mul (movingBall_integral_continuousOn hc hTc
    ((hv.norm.pow 2).add (continuousOn_const.mul (hg.norm.pow 2))))

/-- The local forcing norm is continuous, using only the source on the cone. -/
theorem localForcingNorm_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T : ℝ} {a : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (hc : 0 < c) (hTc : T < R / c)
    (h : IsLocalSmoothWave c a R T u v f) :
    ContinuousOn (localForcingNorm c a R f) (Icc 0 T) :=
  (movingBall_integral_continuousOn hc hTc (h.forcing_continuous.norm.pow 2)).sqrt



lemma scalar_real_inner {𝕜 : Type} [RCLike 𝕜] (v w : 𝕜) :
    inner ℝ v w = RCLike.re (star v * w) := by
  rw [real_inner_eq_re_inner 𝕜, RCLike.inner_apply, mul_comm]
  rfl

lemma laplacian_eq_sum_fderiv {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : P201Specs.Space n → 𝕜) (x : P201Specs.Space n) :
    P201Specs.laplacian u x = ∑ i : Fin n,
      fderiv ℝ (fun y => fderiv ℝ u y (P201Specs.coordinate n i)) x
        (P201Specs.coordinate n i) := by
  have hsort (i : Fin n) : Multiset.sort ({i, i} : Multiset (Fin n)) (· ≤ ·) = [i, i] := by
    simp [Multiset.sort_cons]
  simp only [P201Specs.laplacian, P201Specs.multiPartial, P102.U4.multiPartial, hsort,
    P102.U4.partialWord]

def waveEnergyDensity {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (u v : ℝ → P201Specs.Space n → 𝕜) (z : ℝ × P201Specs.Space n) : ℝ :=
  (‖v z.1 z.2‖ ^ 2 + c ^ 2 * ‖spatialGradient (u z.1) z.2‖ ^ 2) / 2

def waveEnergyFlux {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (u v : ℝ → P201Specs.Space n → 𝕜) (z : ℝ × P201Specs.Space n) : P201Specs.Space n :=
  WithLp.toLp 2 (fun i => c ^ 2 * RCLike.re (star (v z.1 z.2) *
    spatialGradient (u z.1) z.2 i))

lemma spatial_waveFlux_divergence {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) {u v : P201Specs.Space n → 𝕜} {x : P201Specs.Space n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 1 v x) :
    P201Specs.divergence
      (fun y => WithLp.toLp 2 (fun i => c ^ 2 * RCLike.re
        (star (v y) * spatialGradient u y i))) x =
      c ^ 2 * ((∑ i : Fin n, RCLike.re (star (fderiv ℝ v x (P201Specs.coordinate n i)) *
        spatialGradient u x i)) + RCLike.re (star (v x) * P201Specs.laplacian u x)) := by
  have hdu (i : Fin n) : DifferentiableAt ℝ
      (fun y => fderiv ℝ u y (P201Specs.coordinate n i)) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have hi (i : Fin n) :
      fderiv ℝ (fun y => c ^ 2 * RCLike.re (star (v y) * spatialGradient u y i)) x
        (P201Specs.coordinate n i) =
      c ^ 2 * (RCLike.re (star (fderiv ℝ v x (P201Specs.coordinate n i)) * spatialGradient u x i) +
        RCLike.re (star (v x) * fderiv ℝ
          (fun y => fderiv ℝ u y (P201Specs.coordinate n i)) x (P201Specs.coordinate n i))) := by
    change fderiv ℝ (fun y => c ^ 2 * RCLike.re (star (v y) *
      fderiv ℝ u y (P201Specs.coordinate n i))) x (P201Specs.coordinate n i) = _
    simp_rw [← scalar_real_inner]
    rw [fderiv_const_mul ((hv.differentiableAt (by norm_num)).inner ℝ (hdu i))]
    simp only [smul_apply, smul_eq_mul]
    congr 1
    simpa only [add_comm, spatialGradient, PiLp.toLp_apply] using fderiv_inner_apply ℝ (hv.differentiableAt (by norm_num)) (hdu i) (P201Specs.coordinate n i)
  change (∑ i : Fin n, fderiv ℝ
    (fun y => c ^ 2 * RCLike.re (star (v y) * spatialGradient u y i)) x
      (P201Specs.coordinate n i)) = _
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 2
  rw [laplacian_eq_sum_fderiv, Finset.mul_sum, map_sum]



lemma waveEnergyDensity_contDiffAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ closedBall a (R - c * s)) :
    ContDiffAt ℝ 1 (waveEnergyDensity c u v) (s, x) := by
  obtain ⟨hu, hv⟩ := interior_regular h hs hx
  exact ((hv.norm_sq 𝕜).add (contDiffAt_const.mul
    ((spatialGradient_contDiffAt hu).norm_sq 𝕜))).div_const 2

lemma waveEnergyFlux_contDiffAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ closedBall a (R - c * s)) :
    ContDiffAt ℝ 1 (waveEnergyFlux c u v) (s, x) := by
  obtain ⟨hu, hv⟩ := interior_regular h hs hx
  have hg := spatialGradient_contDiffAt hu
  apply PiLp.contDiff_toLp.contDiffAt.comp (s, x)
  apply contDiffAt_pi.mpr
  intro i
  have hgi : ContDiffAt ℝ 1
      (fun z : ℝ × P201Specs.Space n => spatialGradient (u z.1) z.2 i) (s, x) :=
    (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin n => 𝕜) i).contDiff.contDiffAt.comp (s, x) hg
  exact contDiffAt_const.mul ((RCLike.reCLM (K := 𝕜)).contDiff.contDiffAt.comp (s, x)
    (((RCLike.conjCLE (K := 𝕜)).contDiff.contDiffAt.comp (s, x) hv).mul hgi))



lemma time_fderiv_eq_ambient {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ closedBall a (R - c * s)) :
    fderiv ℝ (Function.uncurry u) (s, x) (1, 0) = v s x := by
  have hu := (interior_regular h hs hx).1.differentiableAt (by norm_num)
  have ht := hu.hasFDerivAt.comp s
    ((hasFDerivAt_id (𝕜 := ℝ) s).prodMk (hasFDerivAt_const (𝕜 := ℝ) x s))
  have hdt : HasDerivAt (fun r => u r x)
      (fderiv ℝ (Function.uncurry u) (s, x) (1, 0)) s := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply, id_eq] using ht.hasDerivAt
  exact hdt.unique ((h.displacement_derivative s (Ioo_subset_Icc_self hs) x hx).hasDerivAt
    (Icc_mem_nhds hs.1 hs.2))

lemma openCone_nhds {n : ℕ} {c R T s : ℝ} {a x : P201Specs.Space n}
    (hs : s ∈ Ioo 0 T) (hx : x ∈ coneBall c a R s) :
    ∀ᶠ y : ℝ × P201Specs.Space n in 𝓝 (s, x),
      y.1 ∈ Ioo 0 T ∧ y.2 ∈ coneBall c a R y.1 := by
  have ho : IsOpen {y : ℝ × P201Specs.Space n |
      y.1 ∈ Ioo 0 T ∧ dist y.2 a < R - c * y.1} := by
    apply (isOpen_Ioo.preimage continuous_fst).inter
    exact isOpen_lt (continuous_snd.dist continuous_const)
      (continuous_const.sub (continuous_const.mul continuous_fst))
  exact ho.mem_nhds ⟨hs, hx⟩

lemma spatialGradient_time_partial {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ coneBall c a R s) (i : Fin n) :
    HasDerivAt (fun r => fderiv ℝ (u r) x (P201Specs.coordinate n i))
      (fderiv ℝ (v s) x (P201Specs.coordinate n i)) s := by
  let U := Function.uncurry u
  let V := Function.uncurry v
  let z : ℝ × P201Specs.Space n := (s, x)
  let A := fderiv ℝ U
  let τ : ℝ × P201Specs.Space n := (1, 0)
  let ξ : ℝ × P201Specs.Space n := (0, P201Specs.coordinate n i)
  have hu : ContDiffAt ℝ 2 U z := (interior_regular h hs (ball_subset_closedBall hx)).1
  have hv : ContDiffAt ℝ 1 V z := (interior_regular h hs (ball_subset_closedBall hx)).2
  have hA : DifferentiableAt ℝ A z := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y => A y τ) =ᶠ[𝓝 z] V := by
    filter_upwards [openCone_nhds hs hx] with y hy
    exact time_fderiv_eq_ambient h hy.1 (ball_subset_closedBall hy.2)
  have hmix : fderiv ℝ A z τ ξ = fderiv ℝ V z ξ := by
    rw [(hu.isSymmSndFDerivAt (by norm_num)).eq τ ξ]
    have hd : HasFDerivAt (fun y => A y τ)
        ((fderiv ℝ A z).flip τ) z := by
      simpa using
        hA.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) τ z)
    rw [← heq.fderiv_eq]
    exact congrArg (fun L => L ξ) hd.fderiv.symm
  have hd := (hA.hasFDerivAt.comp s
    ((hasFDerivAt_id (𝕜 := ℝ) s).prodMk (hasFDerivAt_const (𝕜 := ℝ) x s))).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) ξ s)
  have hd' : HasDerivAt (fun r => A (r, x) ξ) (fderiv ℝ V z ξ) s := by
    convert! hd.hasDerivAt using 1
    simpa [τ] using hmix.symm
  have heq' : (fun r => A (r, x) ξ) =ᶠ[𝓝 s]
      (fun r => fderiv ℝ (u r) x (P201Specs.coordinate n i)) := by
    have hu' := hu.eventually (by norm_num)
    have hh : ContinuousAt (fun r : ℝ => (r, x)) s := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hh.eventually hu'] with r hr
    exact (spatial_fderiv_eq_ambient (hr.differentiableAt (by norm_num)) i).symm
  rw [spatial_fderiv_eq_ambient (hv.differentiableAt (by norm_num)) i]
  exact hd'.congr_of_eventuallyEq heq'.symm


lemma spatialGradient_time_derivative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ coneBall c a R s) :
    HasDerivAt (fun r => spatialGradient (u r) x)
      (spatialGradient (v s) x) s := by
  have hp : HasDerivAt
      (fun r => fun i : Fin n => fderiv ℝ (u r) x (P201Specs.coordinate n i))
      (fun i : Fin n => fderiv ℝ (v s) x (P201Specs.coordinate n i)) s :=
    hasDerivAt_pi.mpr (fun i => spatialGradient_time_partial h hs hx i)
  convert! (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s hp using 1


lemma energy_density_time_derivative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ coneBall c a R s) :
    HasDerivAt (fun r => (‖v r x‖ ^ 2 +
        c ^ 2 * ‖spatialGradient (u r) x‖ ^ 2) / 2)
      (RCLike.re (star (v s x) * (c ^ 2 • laplacian (u s) x + f s x)) +
        c ^ 2 * ∑ i : Fin n,
          RCLike.re (star (fderiv ℝ (v s) x (P201Specs.coordinate n i)) *
            spatialGradient (u s) x i)) s := by
  have hv := (h.wave_equation s (Ioo_subset_Icc_self hs) x (ball_subset_closedBall hx)).hasDerivAt
    (Icc_mem_nhds hs.1 hs.2)
  have hg := spatialGradient_time_derivative h hs hx
  have he := (hv.norm_sq.add (hg.norm_sq.const_mul (c ^ 2))).div_const 2
  have hvinner : inner ℝ (v s x) (c ^ 2 • laplacian (u s) x + f s x) =
      RCLike.re (star (v s x) * (c ^ 2 • laplacian (u s) x + f s x)) := by
    rw [real_inner_eq_re_inner 𝕜, RCLike.inner_apply']
    rfl
  have hginner : inner ℝ (spatialGradient (u s) x) (spatialGradient (v s) x) =
      ∑ i : Fin n, RCLike.re
        (star (fderiv ℝ (v s) x (P201Specs.coordinate n i)) * spatialGradient (u s) x i) := by
    rw [real_inner_comm, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_eq_re_inner 𝕜, RCLike.inner_apply']
    rfl
  convert! he using 1
  rw [hvinner, hginner]
  ring



 theorem fixedBall_hasDerivAt_integral {n : ℕ} {l s u : ℝ}
    {G : ℝ × P201Specs.Space n → ℝ} (hs : s ∈ Ioo l u)
    (hG : ∀ z ∈ Ioo l u ×ˢ closedBall (0 : P201Specs.Space n) 1,
      ContDiffAt ℝ 1 G z) :
    HasDerivAt (fun t => ∫ y in ball (0 : P201Specs.Space n) 1, G (t, y))
      (∫ y in ball (0 : P201Specs.Space n) 1,
        fderiv ℝ G (s, y) (1, 0)) s := by
  let J : Set ℝ := Icc ((l + s) / 2) ((s + u) / 2)
  have hJ : J ⊆ Ioo l u := by
    intro t ht
    dsimp [J] at ht
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hsJ : J ∈ 𝓝 s := Icc_mem_nhds (by linarith [hs.1])
    (by linarith [hs.2])
  have hcont : ContinuousOn G (Ioo l u ×ˢ closedBall (0 : P201Specs.Space n) 1) :=
    fun z hz => (hG z hz).continuousAt.continuousWithinAt
  let D : ℝ × P201Specs.Space n → ℝ := fun z => fderiv ℝ G z (1, 0)
  have hD : ContinuousOn D (Ioo l u ×ˢ closedBall (0 : P201Specs.Space n) 1) := by
    intro z hz
    exact ((hG z hz).continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const |>.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod
    (isCompact_closedBall (0 : P201Specs.Space n) 1)).bddAbove_image
      (hD.norm.mono (prod_mono hJ Subset.rfl))
  have hm : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable (fun y => G (t, y))
        (volume.restrict (ball (0 : P201Specs.Space n) 1)) := by
    filter_upwards [hsJ] with t ht
    exact (hcont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun y hy => ⟨hJ ht, ball_subset_closedBall hy⟩)).aestronglyMeasurable
        measurableSet_ball
  have hi : IntegrableOn (fun y => G (s, y)) (ball (0 : P201Specs.Space n) 1) := by
    exact (hcont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun y hy => ⟨hs, hy⟩)).integrableOn_compact
        (isCompact_closedBall _ _) |>.mono_set ball_subset_closedBall
  have hmD : AEStronglyMeasurable (fun y => D (s, y))
      (volume.restrict (ball (0 : P201Specs.Space n) 1)) := by
    exact (hD.comp (continuousOn_const.prodMk continuousOn_id)
      (fun y hy => ⟨hs, ball_subset_closedBall hy⟩)).aestronglyMeasurable
        measurableSet_ball
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (ball (0 : P201Specs.Space n) 1))
    (F := fun t y => G (t, y)) (F' := fun t y => D (t, y))
    (bound := fun _ => M) hsJ hm hi hmD ?_
    (integrableOn_const (measure_ball_lt_top.ne)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    intro t ht
    exact hM (mem_image_of_mem _ ⟨ht, ball_subset_closedBall hy⟩)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    intro t ht
    exact ((hG (t, y) ⟨hJ ht, ball_subset_closedBall hy⟩).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))


 theorem movingBall_hasDerivAt_integral_pullback {n : ℕ} {c R T s : ℝ}
    {a : P201Specs.Space n} {g : ℝ × P201Specs.Space n → ℝ}
    (hc : 0 < c) (hTc : T < R / c) (hs : s ∈ Ioo 0 T)
    (hg : ∀ t ∈ Ioo 0 T, ∀ x ∈ closedBall a (R - c * t),
      ContDiffAt ℝ 1 g (t, x)) :
    HasDerivAt (fun t => ∫ x in coneBall c a R t, g (t, x))
      (∫ y in ball (0 : P201Specs.Space n) 1,
        (Module.finrank ℝ (P201Specs.Space n) : ℝ) *
          (R - c * s) ^ (Module.finrank ℝ (P201Specs.Space n) - 1) * (-c) *
            g (s, a + (R - c * s) • y) +
        (R - c * s) ^ Module.finrank ℝ (P201Specs.Space n) *
          fderiv ℝ g (s, a + (R - c * s) • y) (1, -c • y)) s := by
  let m := Module.finrank ℝ (P201Specs.Space n)
  let Φ : ℝ × P201Specs.Space n → ℝ × P201Specs.Space n :=
    fun z => (z.1, a + (R - c * z.1) • z.2)
  let G : ℝ × P201Specs.Space n → ℝ :=
    fun z => (R - c * z.1) ^ m * g (Φ z)
  have hr : ∀ t ∈ Ioo 0 T, 0 < R - c * t := by
    intro t ht
    have hh := (lt_div_iff₀ hc).mp hTc
    nlinarith [mul_le_mul_of_nonneg_left ht.2.le hc.le]
  have hΦ : ContDiff ℝ 1 Φ := by dsimp [Φ]; fun_prop
  have hmaps : ∀ z ∈ Ioo 0 T ×ˢ closedBall (0 : P201Specs.Space n) 1,
      (Φ z).2 ∈ closedBall a (R - c * z.1) := by
    intro z hz
    change dist (a + (R - c * z.1) • z.2) a ≤ R - c * z.1
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hr z.1 hz.1)]
    simpa using mul_le_mul_of_nonneg_left
      (mem_closedBall_zero_iff.mp hz.2) (hr z.1 hz.1).le
  have hG : ∀ z ∈ Ioo 0 T ×ˢ closedBall (0 : P201Specs.Space n) 1,
      ContDiffAt ℝ 1 G z := by
    intro z hz
    exact ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_fst)).pow m).mul
      ((hg z.1 hz.1 (Φ z).2 (hmaps z hz)).comp z hΦ.contDiffAt)
  have hmain := fixedBall_hasDerivAt_integral hs hG
  have heq : (fun t => ∫ y in ball (0 : P201Specs.Space n) 1, G (t, y))
      =ᶠ[𝓝 s] fun t => ∫ x in coneBall c a R t, g (t, x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    dsimp [G, Φ]
    rw [integral_const_mul]
    exact (integral_ball_pullback (fun x => g (t, x)) a (hr t ht)).symm
  have hpoint : ∀ y ∈ ball (0 : P201Specs.Space n) 1,
      fderiv ℝ G (s, y) (1, 0) =
        (m : ℝ) * (R - c * s) ^ (m - 1) * (-c) *
            g (s, a + (R - c * s) • y) +
        (R - c * s) ^ m *
          fderiv ℝ g (s, a + (R - c * s) • y) (1, -c • y) := by
    intro y hy
    have hcurve : HasDerivAt
        (fun t : ℝ => (t, a + (R - c * t) • y)) (1, -c • y) s := by
      convert (hasDerivAt_id s).prodMk
        ((hasDerivAt_const s a).add
          (((hasDerivAt_const s R).sub
            ((hasDerivAt_const s c).mul (hasDerivAt_id s))).smul_const y)) using 1 <;>
        simp
    have hpow := (((hasDerivAt_const s R).sub
      ((hasDerivAt_const s c).mul (hasDerivAt_id s))).pow m)
    have hcomp := ((hg s hs (Φ (s, y)).2
      (hmaps (s, y) ⟨hs, ball_subset_closedBall hy⟩)).differentiableAt
        (by norm_num)).hasFDerivAt.comp_hasDerivAt s hcurve
    have hh := hpow.mul hcomp
    have hder := ((hG (s, y) ⟨hs, ball_subset_closedBall hy⟩).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    apply hder.unique
    convert hh using 1 <;>
      simp [G, Φ, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_def]
    rfl
  rw [integral_congr_ae (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hpoint y hy)] at hmain
  exact hmain.congr_of_eventuallyEq heq.symm


 theorem movingBall_hasDerivAt_integral {n : ℕ} {c R T s : ℝ}
    {a : P201Specs.Space n} {g : ℝ × P201Specs.Space n → ℝ}
    (hc : 0 < c) (hTc : T < R / c) (hs : s ∈ Ioo 0 T)
    (hg : ∀ t ∈ Ioo 0 T, ∀ x ∈ closedBall a (R - c * t),
      ContDiffAt ℝ 1 g (t, x)) :
    HasDerivAt (fun t => ∫ x in coneBall c a R t, g (t, x))
      (∫ x in coneBall c a R s,
        fderiv ℝ g (s, x) (1, (-c / (R - c * s)) • (x - a)) +
          ((Module.finrank ℝ (P201Specs.Space n) : ℝ) * (-c) / (R - c * s)) *
            g (s, x)) s := by
  let m := Module.finrank ℝ (P201Specs.Space n)
  let r := R - c * s
  have hr : 0 < r := by
    have hh := (lt_div_iff₀ hc).mp hTc
    dsimp [r]
    nlinarith [mul_le_mul_of_nonneg_left hs.2.le hc.le]
  have hraw := movingBall_hasDerivAt_integral_pullback hc hTc hs hg
  convert hraw using 1
  unfold coneBall
  rw [integral_ball_pullback _ a hr, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  change r ^ m *
      (fderiv ℝ g (s, a + r • y) (1, (-c / r) • (a + r • y - a)) +
        ((m : ℝ) * (-c) / r) * g (s, a + r • y)) =
    (m : ℝ) * r ^ (m - 1) * (-c) * g (s, a + r • y) +
      r ^ m * fderiv ℝ g (s, a + r • y) (1, -c • y)
  rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hr.ne']
  by_cases hm : m = 0
  · simp [hm]
  · have hpow := pow_sub_one_mul hm r
    rw [← hpow]
    field_simp
    ring


 theorem movingBall_hasDerivAt_integral_volume {n : ℕ} {c R T s : ℝ}
    {a : P201Specs.Space n} {g : ℝ × P201Specs.Space n → ℝ}
    (hc : 0 < c) (hTc : T < R / c) (hs : s ∈ Ioo 0 T)
    (hg : ∀ t ∈ Ioo 0 T, ∀ x ∈ closedBall a (R - c * t),
      ContDiffAt ℝ 1 g (t, x)) :
    HasDerivAt (fun t => ∫ x in coneBall c a R t, g (t, x))
      (∫ x in coneBall c a R s,
        fderiv ℝ g (s, x) (1, 0) - (c / (R - c * s)) *
          ((n : ℝ) * g (s, x) + fderiv ℝ g (s, x) (0, x - a))) s := by
  convert movingBall_hasDerivAt_integral hc hTc hs hg using 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hp : ((1 : ℝ), (-c / (R - c * s)) • (x - a)) =
      ((1 : ℝ), (0 : P201Specs.Space n)) + (-c / (R - c * s)) • ((0 : ℝ), x - a) := by
    ext <;> simp
  rw [hp, map_add, map_smul]
  simp only [smul_eq_mul, P201Specs.Space, finrank_euclideanSpace_fin]
  ring

namespace BoundaryIntegration

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model

lemma coefficientIntegral_nonpos {k : ℕ} {S : Set (E k)} {f : S → ℝ}
    (hf : ProperIntegrable f) (h : ∀ x, f x ≤ 0) : coefficientIntegral f ≤ 0 := by
  obtain ⟨Q, hQ, hi⟩ := hf.2
  obtain ⟨hi', he⟩ := D04.DirectedSubstitution.proper_on_box hf Q hQ
  change D04.DirectedSubstitution.coefficientIntegral f ≤ 0
  rw [he]
  have hc := D04.Darboux.integrable_const Q (0 : ℝ)
  have hh := D04.Darboux.integral_mono hi' hc (fun x _ => by
    by_cases hx : x ∈ S
    · simpa only [Specs.D04.C06.JordanRegions.Model.zeroExtension, dite_eq_left hx] using h ⟨x, hx⟩
    · simp [hx])
  simpa only [D04.Darboux.integral_const, zero_mul] using hh

lemma hasDensityIntegral_nonpos {d n : ℕ} {M : Set (E n)} {ρ : M → ℝ} {I : ℝ}
    (hI : HasDensityIntegral (d := d) ρ I) (hρ : ∀ x, ρ x ≤ 0) : I ≤ 0 := by
  obtain ⟨P⟩ := hI.2.2.1
  rw [← (hI.2.2.2 P).2]
  apply Finset.sum_nonpos
  intro i _
  apply coefficientIntegral_nonpos ((hI.2.2.2 P).1 i)
  intro u
  exact mul_nonpos_of_nonneg_of_nonpos (P.partition.2.1 i (chartPoint (P.chart i) u))
    (mul_nonpos_of_nonpos_of_nonneg (hρ _) (Real.sqrt_nonneg _))

lemma integral_ball_divergence_nonpos {d : ℕ} (a : E (d+1)) {r : ℝ} (hr : 0 < r)
    {U : Set (E (d+1))} {F : E (d+1) → E (d+1)} (hU : IsOpen U)
    (hsub : closedBall a r ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (hb : ∀ x ∈ sphere a r, inner ℝ (F x) (x-a) ≤ 0) :
    (∫ x in Metric.ball a r, Specs.D04.C11.EuclideanVectorOperators.Model.divergence F x) ≤ 0 := by
  have hD := D04.LocalDensities.ball_regular a r hr
  obtain ⟨hi, hg⟩ := D04.Gauss.gauss hD U F hU
    (by rwa [closure_ball a hr.ne']) ((D04.crOn_iff_contDiffOn 1 U F hU).mpr hF)
  rw [← (D04.MeasureBridge.region_bridge_ambient _ isOpen_ball.measurableSet hi).2]
  apply hasDensityIntegral_nonpos hg
  intro x
  change inner ℝ (F x) (Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hD x) ≤ 0
  rw [D04.LocalDensities.ball_normal a r hr x, inner_smul_right]
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hr.le)
  apply hb x
  simpa only [frontier_ball a hr.ne'] using x.property

lemma integral_ball_divergence_nonpos_of_contDiffAt {n : ℕ} (hn : 0 < n)
    (a : E n) {r : ℝ} (hr : 0 < r) {F : E n → E n}
    (hF : ∀ x ∈ closedBall a r, ContDiffAt ℝ 1 F x)
    (hb : ∀ x ∈ sphere a r, inner ℝ (F x) (x-a) ≤ 0) :
    (∫ x in Metric.ball a r, Specs.D04.C11.EuclideanVectorOperators.Model.divergence F x) ≤ 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let U := interior {x | ContDiffAt ℝ 1 F x}
  apply integral_ball_divergence_nonpos a hr (U := U) isOpen_interior ?_ ?_ hb
  · intro x hx
    exact mem_interior_iff_mem_nhds.mpr ((hF x hx).eventually (by simp))
  · intro x hx
    have hh : ContDiffAt ℝ 1 F x := interior_subset hx
    exact hh.contDiffWithinAt

lemma divergence_eq_sum {n : ℕ} (F : E n → E n) (x : E n) :
    Specs.D04.C11.EuclideanVectorOperators.Model.divergence F x =
      ∑ i, (fderiv ℝ F x (D04.standardBasis n i)) i := by
  change D04.divergence F x = _
  rw [D04.divergence_eq_jacobian_trace]
  apply Finset.sum_congr rfl
  intro i _
  exact D04.matrixOfLinearMap_apply _ i i

lemma divergence_eq_project {n : ℕ} (F : P201Specs.Space n → P201Specs.Space n)
    (x : P201Specs.Space n) (hF : DifferentiableAt ℝ F x) :
    Specs.D04.C11.EuclideanVectorOperators.Model.divergence F x = P201Specs.divergence F x := by
  rw [divergence_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd := (PiLp.hasFDerivAt_apply 2 (F x) i).comp x hF.hasFDerivAt
  have he : fderiv ℝ (fun y => F y i) x =
      (PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ F x) := hd.fderiv
  rw [he]
  rfl

lemma integral_ball_project_divergence_nonpos {n : ℕ} (hn : 0 < n)
    (a : P201Specs.Space n) {r : ℝ} (hr : 0 < r)
    {F : P201Specs.Space n → P201Specs.Space n}
    (hF : ∀ x ∈ closedBall a r, ContDiffAt ℝ 1 F x)
    (hb : ∀ x ∈ sphere a r, inner ℝ (F x) (x-a) ≤ 0) :
    (∫ x in Metric.ball a r, P201Specs.divergence F x) ≤ 0 := by
  have h := integral_ball_divergence_nonpos_of_contDiffAt hn a hr hF hb
  apply le_trans ?_ h
  apply le_of_eq
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro x hx
  exact (divergence_eq_project F x ((hF x (ball_subset_closedBall hx)).differentiableAt (by simp))).symm


end BoundaryIntegration

set_option maxHeartbeats 1000000 in
lemma waveEnergy_balance {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c R T s : ℝ} {a x : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (h : IsLocalSmoothWave c a R T u v f)
    (hs : s ∈ Ioo 0 T) (hx : x ∈ coneBall c a R s) :
    fderiv ℝ (waveEnergyDensity c u v) (s, x) (1, 0) =
      P201Specs.divergence (fun y => waveEnergyFlux c u v (s, y)) x +
        RCLike.re (star (v s x) * f s x) := by
  have hdt := ((waveEnergyDensity_contDiffAt h hs (ball_subset_closedBall hx)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have heq := hdt.unique (energy_density_time_derivative h hs hx)
  rw [heq]
  rw [show P201Specs.divergence (fun y => waveEnergyFlux c u v (s, y)) x = _ from
    spatial_waveFlux_divergence c (spatial_regular h (Ioo_subset_Icc_self hs)
      (ball_subset_closedBall hx)) (velocity_regular h (Ioo_subset_Icc_self hs)
      (ball_subset_closedBall hx))]
  simp only [mul_add, map_add, mul_smul_comm, RCLike.smul_re]
  simp only [id_eq, mul_comm]
  ring

lemma correctedFlux_boundary_nonpos {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (hc : 0 ≤ c) (u v : ℝ → P201Specs.Space n → 𝕜)
    (s : ℝ) (a : P201Specs.Space n) (r : ℝ) (hr : 0 < r)
    {x : P201Specs.Space n} (hx : x ∈ sphere a r) :
    inner ℝ (waveEnergyFlux c u v (s, x) -
      (c / r * waveEnergyDensity c u v (s, x)) • (x - a)) (x - a) ≤ 0 := by
  have hnorm : ‖x - a‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx
  have hflux := waveFlux_norm_le hc (v s x) (spatialGradient (u s) x)
  change ‖waveEnergyFlux c u v (s, x)‖ ≤
    c * (‖v s x‖ ^ 2 + c ^ 2 * ‖spatialGradient (u s) x‖ ^ 2) / 2 at hflux
  have hbound : inner ℝ (waveEnergyFlux c u v (s, x)) (x-a) ≤
      c * waveEnergyDensity c u v (s, x) * r := by
    calc
      _ ≤ ‖waveEnergyFlux c u v (s, x)‖ * ‖x-a‖ := real_inner_le_norm _ _
      _ ≤ (c * (‖v s x‖ ^ 2 + c ^ 2 * ‖spatialGradient (u s) x‖ ^ 2) / 2) * r := by
        rw [hnorm]; exact mul_le_mul_of_nonneg_right hflux hr.le
      _ = _ := by dsimp [waveEnergyDensity]; ring
  rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hnorm, starRingEnd_apply, star_trivial]
  have heq : (c / r * waveEnergyDensity c u v (s, x)) * r ^ 2 =
      c * waveEnergyDensity c u v (s, x) * r := by field_simp
  rw [heq]
  exact sub_nonpos.mpr hbound

lemma divergence_position_smul {n : ℕ} {e : P201Specs.Space n → ℝ}
    {a x : P201Specs.Space n} (he : DifferentiableAt ℝ e x) :
    P201Specs.divergence (fun y => e y • (y - a)) x =
      (n : ℝ) * e x + fderiv ℝ e x (x - a) := by
  have hcoord : ∀ i : Fin n,
      fderiv ℝ (fun y => (e y • (y - a)) i) x (P201Specs.coordinate n i) =
        fderiv ℝ e x (P201Specs.coordinate n i) * (x - a) i + e x := by
    intro i
    have hproj := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (x - a) i).comp x
      ((hasFDerivAt_id x).sub (hasFDerivAt_const a x))
    have hh := he.hasFDerivAt.mul hproj
    have hval := congrArg (fun L => L (P201Specs.coordinate n i)) hh.fderiv
    convert hval using 1 <;>
      simp [P201Specs.coordinate, P102.U4.coordinateVector,
        EuclideanSpace.basisFun_apply, mul_comm, add_comm]
    rfl
  change (∑ i : Fin n, _) = _
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib]
  have hrepr : (∑ i : Fin n, (x - a) i • P201Specs.coordinate n i) = x - a := by
    exact (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (x - a)
  have hsum : (∑ i : Fin n, fderiv ℝ e x (P201Specs.coordinate n i) * (x - a) i) =
      fderiv ℝ e x (x - a) := by
    calc
      _ = fderiv ℝ e x (∑ i : Fin n, (x - a) i • P201Specs.coordinate n i) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = _ := congrArg (fderiv ℝ e x) hrepr
  rw [hsum]
  simp [add_comm, mul_comm]

lemma spatial_fderiv_apply_eq_ambient {n : ℕ} {g : ℝ × P201Specs.Space n → ℝ}
    {s : ℝ} {x z : P201Specs.Space n} (hg : DifferentiableAt ℝ g (s, x)) :
    fderiv ℝ (fun y => g (s, y)) x z = fderiv ℝ g (s, x) (0, z) := by
  have hd := hg.hasFDerivAt.comp x
    ((hasFDerivAt_const s x).prodMk (hasFDerivAt_id x))
  exact congrArg (fun L => L z) hd.fderiv

lemma divergence_sub_const_smul {n : ℕ} {F G : P201Specs.Space n → P201Specs.Space n}
    {x : P201Specs.Space n} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : ℝ) :
    P201Specs.divergence (fun y => F y - k • G y) x =
      P201Specs.divergence F x - k * P201Specs.divergence G x := by
  have hi (i : Fin n) :
      fderiv ℝ (fun y => (F y - k • G y) i) x (P201Specs.coordinate n i) =
      fderiv ℝ (fun y => F y i) x (P201Specs.coordinate n i) -
        k * fderiv ℝ (fun y => G y i) x (P201Specs.coordinate n i) := by
    have hFi := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F x) i).differentiableAt.comp x hF
    have hGi := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (G x) i).differentiableAt.comp x hG
    change fderiv ℝ (fun y => F y i - k * G y i) x (P201Specs.coordinate n i) = _
    have hh := hFi.hasFDerivAt.sub (hGi.hasFDerivAt.const_mul k)
    exact congrArg (fun L => L (P201Specs.coordinate n i)) hh.fderiv
  change (∑ i : Fin n, _) = _
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]


lemma project_divergence_continuousAt {n : ℕ} {F : P201Specs.Space n → P201Specs.Space n}
    {x : P201Specs.Space n} (hF : ContDiffAt ℝ 1 F x) :
    ContinuousAt (P201Specs.divergence F) x := by
  apply tendsto_finsetSum
  intro i _
  have hc := (contDiffAt_piLp 2).1 hF i
  exact (hc.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const

lemma localEnergy_eq_integral_density {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : P201Specs.Space n) (R : ℝ) (u v : ℝ → P201Specs.Space n → 𝕜)
    (s : ℝ) :
    localEnergy c a R u v s = ∫ x in coneBall c a R s, waveEnergyDensity c u v (s, x) := by
  unfold localEnergy waveEnergyDensity
  rw [integral_div]
  ring

set_option maxHeartbeats 1000000 in
/-- Differentiating the dilation pullback gives the moving-ball derivative.
The local energy balance and Gauss' theorem turn its transport term into the
outward flux of a corrected field, whose normal component is nonpositive. -/
theorem movingEnergy_calculus {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 1 ≤ n) {c R T : ℝ} {a : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (hc : 0 < c) (_hR : 0 < R) (hT : 0 ≤ T) (hTc : T < R / c)
    (h : IsLocalSmoothWave c a R T u v f) :
    ContinuousOn (localEnergy c a R u v) (Icc 0 T) ∧
    ContinuousOn (localForcingNorm c a R f) (Icc 0 T) ∧
    ∃ D : ℝ → ℝ,
      (∀ s ∈ Ioo 0 T, HasDerivAt (localEnergy c a R u v) (D s) s) ∧
      (∀ s ∈ Ioo 0 T, D s ≤
        ∫ x in coneBall c a R s, RCLike.re (star (v s x) * f s x)) := by
  refine ⟨localEnergy_continuousOn hc hT hTc h,
    localForcingNorm_continuousOn hc hTc h, ?_⟩
  let e := waveEnergyDensity c u v
  let D : ℝ → ℝ := fun s => ∫ x in coneBall c a R s,
    fderiv ℝ e (s, x) (1, 0) - (c / (R - c * s)) *
      ((n : ℝ) * e (s, x) + fderiv ℝ e (s, x) (0, x - a))
  refine ⟨D, ?_, ?_⟩
  · intro s hs
    have hd := movingBall_hasDerivAt_integral_volume hc hTc hs
      (fun t ht x hx => waveEnergyDensity_contDiffAt h ht hx)
    simpa only [← localEnergy_eq_integral_density] using hd
  · intro s hs
    let r := R - c * s
    have hr : 0 < r := by
      have hh := (lt_div_iff₀ hc).mp hTc
      dsimp [r]
      nlinarith [mul_le_mul_of_nonneg_left hs.2.le hc.le]
    let J : P201Specs.Space n → P201Specs.Space n := fun x => waveEnergyFlux c u v (s, x)
    let H : P201Specs.Space n → P201Specs.Space n :=
      fun x => J x - (c / r) • (e (s, x) • (x-a))
    have he : ∀ x ∈ closedBall a r, ContDiffAt ℝ 1 (fun y => e (s,y)) x := by
      intro x hx
      exact (waveEnergyDensity_contDiffAt h hs hx).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
    have hJ : ∀ x ∈ closedBall a r, ContDiffAt ℝ 1 J x := by
      intro x hx
      exact (waveEnergyFlux_contDiffAt h hs hx).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
    have hH : ∀ x ∈ closedBall a r, ContDiffAt ℝ 1 H x := by
      intro x hx
      have hrad : ContDiffAt ℝ 1
          (fun y => (c / r * e (s,y)) • (y-a)) x :=
        (contDiffAt_const.mul (he x hx)).smul (contDiffAt_id.sub contDiffAt_const)
      simpa only [H, smul_smul, smul_eq_mul] using (hJ x hx).sub hrad
    have hH_bound : (∫ x in ball a r, P201Specs.divergence H x) ≤ 0 := by
      apply BoundaryIntegration.integral_ball_project_divergence_nonpos hn a hr hH
      intro x hx
      have hb := correctedFlux_boundary_nonpos c hc.le u v s a r hr hx
      simpa only [H, J, e, smul_smul, smul_eq_mul] using hb
    have hH_int : IntegrableOn (P201Specs.divergence H) (ball a r) :=
      (show ContinuousOn (P201Specs.divergence H) (closedBall a r) from
        fun x hx => (project_divergence_continuousAt (hH x hx)).continuousWithinAt).integrableOn_compact
          (isCompact_closedBall _ _) |>.mono_set ball_subset_closedBall
    have hv : ContinuousOn (v s) (closedBall a r) :=
      fun x hx => (velocity_regular h (Ioo_subset_Icc_self hs) hx).continuousAt.continuousWithinAt
    have hf := forcing_continuousOn_slice h (Ioo_subset_Icc_self hs)
    have hpair : IntegrableOn (fun x => RCLike.re (star (v s x) * f s x)) (ball a r) :=
      (RCLike.continuous_re.comp_continuousOn (hv.star.mul hf)).integrableOn_compact
        (isCompact_closedBall _ _) |>.mono_set ball_subset_closedBall
    have hD : D s = (∫ x in ball a r, P201Specs.divergence H x) +
        ∫ x in ball a r, RCLike.re (star (v s x) * f s x) := by
      rw [← integral_add hH_int hpair]
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      have hdE := (waveEnergyDensity_contDiffAt h hs (ball_subset_closedBall hx)).differentiableAt
        (by norm_num)
      have hdiv := divergence_sub_const_smul ((hJ x (ball_subset_closedBall hx)).differentiableAt
        (by norm_num)) (((he x (ball_subset_closedBall hx)).differentiableAt (by norm_num)).smul
          (differentiableAt_id.sub_const a)) (c/r)
      change _ = P201Specs.divergence H x + _
      rw [show P201Specs.divergence H x = _ from hdiv]
      change fderiv ℝ e (s,x) (1,0) - (c / r) *
          ((n : ℝ) * e (s,x) + fderiv ℝ e (s,x) (0,x-a)) =
        P201Specs.divergence J x - (c / r) *
          P201Specs.divergence (fun y => e (s,y) • (y-a)) x + _
      rw [divergence_position_smul (a := a)
        ((he x (ball_subset_closedBall hx)).differentiableAt (by norm_num)),
        spatial_fderiv_apply_eq_ambient hdE]
      dsimp only [e, J]
      rw [waveEnergy_balance h hs hx]
      ring
    rw [hD]
    change (∫ x in ball a r, P201Specs.divergence H x) +
      (∫ x in ball a r, RCLike.re (star (v s x) * f s x)) ≤
        ∫ x in ball a r, RCLike.re (star (v s x) * f s x)
    linarith


/-- Combining the local flux inequality with the proved forcing-pairing bound. -/
theorem localEnergy_calculus {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 1 ≤ n) {c R T : ℝ} {a : P201Specs.Space n}
    {u v f : ℝ → P201Specs.Space n → 𝕜}
    (hc : 0 < c) (hR : 0 < R) (hT : 0 ≤ T) (hTc : T < R / c)
    (h : IsLocalSmoothWave c a R T u v f) :
    ContinuousOn (localEnergy c a R u v) (Icc 0 T) ∧
    ContinuousOn (localForcingNorm c a R f) (Icc 0 T) ∧
    ∃ D : ℝ → ℝ,
      (∀ s ∈ Ioo 0 T, HasDerivAt (localEnergy c a R u v) (D s) s) ∧
      (∀ s ∈ Ioo 0 T, D s ≤ localForcingNorm c a R f s *
        Real.sqrt (2 * localEnergy c a R u v s)) := by
  obtain ⟨hE, hF, D, hD, hb⟩ := movingEnergy_calculus hn hc hR hT hTc h
  exact ⟨hE, hF, D, hD, fun s hs => (hb s hs).trans (forcingPairing_le h (Ioo_subset_Icc_self hs))⟩

/-- Sharp local cone energy estimate for real and complex classical waves. -/
theorem localEnergyEstimate : P201Specs.SmoothCone.localEnergyEstimateStatement := by
  intro n 𝕜 _ hn c a R T u v f hc hR hT hTc h t ht
  obtain ⟨hE, hF, D, hD, hb⟩ := localEnergy_calculus hn hc hR hT hTc h
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  apply sqrt_energy_estimate ht.1 (hE.mono hsub)
    (fun s _ => localEnergy_nonneg c a R u v s)
    (fun s hs => hD s ⟨hs.1, hs.2.trans_le ht.2⟩)
    (fun s _ => Real.sqrt_nonneg _)
    ((hF.mono hsub).integrableOn_Icc)
    (fun s hs => hb s ⟨hs.1, hs.2.trans_le ht.2⟩)

/-- With zero data and source, the displacement itself is zero on every slice. -/
theorem vanishing : P201Specs.SmoothCone.vanishingStatement := by
  intro n 𝕜 _ hn c a R T u v f hc hR hT hTc h hu₀ hv₀ hf t ht
  have hE₀ := initialEnergy_eq_zero hu₀ hv₀
  have hv : ∀ s ∈ Icc 0 T, ∀ x ∈ coneBall c a R s, v s x = 0 := by
    intro s hs
    have hest := localEnergyEstimate 𝕜 hn c a R T u v f hc hR hT hTc h s hs
    have hi : (∫ r in (0 : ℝ)..s, localForcingNorm c a R f r) = 0 := by
      calc
        _ = ∫ r in (0 : ℝ)..s, (0 : ℝ) := intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le hs.1] at hr
          exact localForcingNorm_eq_zero (hf r ⟨hr.1, hr.2.trans hs.2⟩)
        _ = 0 := intervalIntegral.integral_zero
    rw [hE₀, mul_zero, Real.sqrt_zero, hi, zero_add] at hest
    have hz : Real.sqrt (2 * localEnergy c a R u v s) = 0 :=
      le_antisymm hest (Real.sqrt_nonneg _)
    have he : localEnergy c a R u v s = 0 := by
      have hn := localEnergy_nonneg c a R u v s
      have hh := Real.sq_sqrt (by linarith : 0 ≤ 2 * localEnergy c a R u v s)
      rw [hz] at hh
      linarith
    exact velocity_eq_zero_of_energy_eq_zero h hs he
  exact displacement_eq_zero hc.le ht
    (fun s hs x hx => h.displacement_derivative s hs x (ball_subset_closedBall hx)) hu₀ hv

/-- Matching local source and both Cauchy data imply local classical uniqueness. -/
theorem localUniqueness : P201Specs.SmoothCone.localUniquenessStatement := by
  intro n 𝕜 _ hn c a R T u₁ v₁ f₁ u₂ v₂ f₂ hc hR hT hTc h₁ h₂ hu hv hf t ht x hx
  have hw := IsLocalSmoothWave.sub h₁ h₂
  have hz := vanishing 𝕜 hn c a R T
    (fun s x => u₁ s x - u₂ s x) (fun s x => v₁ s x - v₂ s x)
    (fun s x => f₁ s x - f₂ s x) hc hR hT hTc hw
    (fun x hx => sub_eq_zero.mpr (hu x hx))
    (fun x hx => sub_eq_zero.mpr (hv x hx))
    (fun s hs x hx => sub_eq_zero.mpr (hf s hs x hx)) t ht x hx
  exact sub_eq_zero.mp hz

end P201.SmoothCone
