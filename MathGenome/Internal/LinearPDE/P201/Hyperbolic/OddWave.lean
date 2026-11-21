import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.OddWave
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201.Potential.MeanValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped ContDiff
namespace P201.OddWave
abbrev sphericalMean : P201Specs.OddWave.SphericalMeanType :=
  @P201Specs.OddWave.sphericalMean
abbrev radialDerivative : P201Specs.OddWave.RadialDerivativeType :=
  @P201Specs.OddWave.radialDerivative
abbrev radialIterate : P201Specs.OddWave.RadialIterateType :=
  @P201Specs.OddWave.radialIterate
abbrev velocityOne : P201Specs.OddWave.VelocityOneType :=
  @P201Specs.OddWave.velocityOne
abbrev velocityOdd : P201Specs.OddWave.VelocityOddType :=
  @P201Specs.OddWave.velocityOdd

abbrev sphereProbability : P201Specs.OddWave.SphereProbabilityType :=
  @P201Specs.OddWave.sphereProbability

theorem sphereProbability_mass : P201Specs.OddWave.SphereProbabilityStatement := by
  intro n hn
  have hω := MeanValues.omega_pos hn
  have hμ : (P201Specs.unitSurface n) univ ≠ 0 := by
    intro he
    simp [P201Specs.omega, Measure.real, he] at hω
  have hfin : (P201Specs.unitSurface n) univ ≠ ⊤ := measure_ne_top _ _
  change (ENNReal.ofReal ((P201Specs.omega n)⁻¹) • P201Specs.unitSurface n) univ = 1
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_inv_of_pos hω,
    show ENNReal.ofReal (P201Specs.omega n) = P201Specs.unitSurface n univ from
      ENNReal.ofReal_toReal hfin,
    ENNReal.inv_mul_cancel hμ hfin]

theorem sphericalMean_probability : P201Specs.OddWave.SphericalMeanProbabilityStatement := by
  intro n 𝕜 _ h x r
  change (P201Specs.omega n)⁻¹ • (∫ θ, h (x + r • θ) ∂P201Specs.unitSurface n) =
    ∫ θ, h (x + r • θ) ∂(ENNReal.ofReal ((P201Specs.omega n)⁻¹) • P201Specs.unitSurface n)
  have hnonneg : 0 ≤ (P201Specs.omega n)⁻¹ := by
    change 0 ≤ ((P201Specs.unitSurface n univ).toReal)⁻¹
    exact inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [integral_smul_measure, ENNReal.toReal_ofReal hnonneg]

theorem sphericalMean_zero {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (h : Space n → 𝕜) (x : Space n) : sphericalMean h x 0 = h x :=
  MeanValues.unitSphereMean_zero hn h x

theorem velocityOdd_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (h : Space n → 𝕜) (x : Space n) : velocityOdd c h 0 x = 0 := by
  simp [velocityOdd, P201Specs.OddWave.velocityOdd]

theorem velocityOne_zero {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (h : ℝ → 𝕜) (x : ℝ) : velocityOne c h 0 x = 0 := by
  simp [velocityOne, P201Specs.OddWave.velocityOne]

theorem velocity_three : P201Specs.OddWave.VelocityThreeStatement := by
  intro 𝕜 _ c hc h t x
  by_cases ht : t = 0
  · subst t
    simp [velocityOdd_zero]
  · simp only [P201Specs.OddWave.velocityOdd, ite_eq_right ht,
      show 3 - 2 = 1 from rfl, show (3 - 3) / 2 = 0 from rfl,
      P201Specs.OddWave.radialIterate, Function.iterate_zero, id_eq,
      Nat.doubleFactorial, Nat.cast_one, mul_one, pow_one, smul_smul]
    congr 1
    field_simp

/-- A primitive on the real line; continuity suffices for its first derivative. -/
def primitive {𝕜 : Type} [RCLike 𝕜] (h : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  ∫ y in (0 : ℝ)..x, h y

theorem primitive_hasDerivAt {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Continuous h) (x : ℝ) : HasDerivAt (primitive h) (h x) x :=
  intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable _ _)
    hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt

theorem primitive_contDiff {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) : ContDiff ℝ (⊤ : ℕ∞) (primitive h) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (primitive_hasDerivAt hh.continuous x).differentiableAt, ?_⟩
  have he : deriv (primitive h) = h := funext fun x =>
    (primitive_hasDerivAt hh.continuous x).deriv
  rw [he]
  exact hh

theorem velocityOne_eq_primitive {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Continuous h) (c t x : ℝ) :
    velocityOne c h t x = (2 * c)⁻¹ •
      (primitive h (x + c * t) - primitive h (x - c * t)) := by
  unfold velocityOne P201Specs.OddWave.velocityOne primitive
  rw [intervalIntegral.integral_interval_sub_left (hh.intervalIntegrable _ _)
    (hh.intervalIntegrable _ _)]

theorem velocityOne_contDiff {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => velocityOne c h p.1 p.2) := by
  simp_rw [velocityOne_eq_primitive hh.continuous]
  exact ((primitive_contDiff hh).comp (contDiff_snd.add (contDiff_const.mul contDiff_fst))
    |>.sub ((primitive_contDiff hh).comp
      (contDiff_snd.sub (contDiff_const.mul contDiff_fst)))).const_smul _

theorem velocityOne_hasDerivAt_time {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Continuous h) (c t x : ℝ) :
    HasDerivAt (fun s => velocityOne c h s x)
      ((2 * c)⁻¹ • (c • h (x + c * t) - (-c) • h (x - c * t))) t := by
  simp_rw [velocityOne_eq_primitive hh]
  have hp := (primitive_hasDerivAt hh (x + c * t)).scomp t
    (((hasDerivAt_id t).const_mul c).const_add x)
  have hm := (primitive_hasDerivAt hh (x - c * t)).scomp t
    ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul c))
  convert (hp.sub hm).const_smul ((2 * c)⁻¹) using 1 <;>
    simp [Function.comp_def]
  ext z
  rfl

theorem velocityOne_hasDerivAt_space {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Continuous h) (c t x : ℝ) :
    HasDerivAt (fun y => velocityOne c h t y)
      ((2 * c)⁻¹ • (h (x + c * t) - h (x - c * t))) x := by
  simp_rw [velocityOne_eq_primitive hh]
  have hp := (primitive_hasDerivAt hh (x + c * t)).scomp x
    ((hasDerivAt_id x).add_const (c * t))
  have hm := (primitive_hasDerivAt hh (x - c * t)).scomp x
    ((hasDerivAt_id x).sub_const (c * t))
  convert (hp.sub hm).const_smul ((2 * c)⁻¹) using 1 <;>
    simp [Function.comp_def]
  ext z
  rfl

theorem velocityOne_deriv_time {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Continuous h) (c t x : ℝ) :
    deriv (fun s => velocityOne c h s x) t =
      (2 * c)⁻¹ • (c • h (x + c * t) - (-c) • h (x - c * t)) :=
  (velocityOne_hasDerivAt_time hh c t x).deriv

theorem velocityOne_deriv_space {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Continuous h) (c t x : ℝ) :
    deriv (fun y => velocityOne c h t y) x =
      (2 * c)⁻¹ • (h (x + c * t) - h (x - c * t)) :=
  (velocityOne_hasDerivAt_space hh c t x).deriv

theorem velocityOne_second_time {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Differentiable ℝ h) (c t x : ℝ) :
    deriv (deriv (fun s => velocityOne c h s x)) t =
      (2 * c)⁻¹ • (c ^ 2 • (deriv h (x + c * t) - deriv h (x - c * t))) := by
  have he₁ : deriv (fun s => velocityOne c h s x) =
      fun s => (2 * c)⁻¹ • (c • h (x + c * s) - (-c) • h (x - c * s)) :=
    funext fun s => velocityOne_deriv_time hh.continuous c s x
  rw [he₁]
  have hp := (hh (x + c * t)).hasDerivAt.scomp t
    (((hasDerivAt_id t).const_mul c).const_add x)
  have hm := (hh (x - c * t)).hasDerivAt.scomp t
    ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul c))
  have hd := ((hp.const_smul c).sub (hm.const_smul (-c))).const_smul ((2 * c)⁻¹)
  have hd' : HasDerivAt
      (fun s => (2 * c)⁻¹ • (c • h (x + c * s) - (-c) • h (x - c * s)))
      ((2 * c)⁻¹ • (c • (c • deriv h (x + c * t)) -
        (-c) • ((-c) • deriv h (x - c * t)))) t := by
    convert hd using 1 <;> simp [Function.comp_def]
    ext s
    rfl
  rw [hd'.deriv]
  module

theorem velocityOne_second_space {𝕜 : Type} [RCLike 𝕜] {h : ℝ → 𝕜}
    (hh : Differentiable ℝ h) (c t x : ℝ) :
    deriv (deriv (fun y => velocityOne c h t y)) x =
      (2 * c)⁻¹ • (deriv h (x + c * t) - deriv h (x - c * t)) := by
  have he₁ : deriv (fun y => velocityOne c h t y) =
      fun y => (2 * c)⁻¹ • (h (y + c * t) - h (y - c * t)) :=
    funext fun y => velocityOne_deriv_space hh.continuous c t y
  rw [he₁]
  have hp := (hh (x + c * t)).hasDerivAt.scomp x
    ((hasDerivAt_id x).add_const (c * t))
  have hm := (hh (x - c * t)).hasDerivAt.scomp x
    ((hasDerivAt_id x).sub_const (c * t))
  have hd := (hp.sub hm).const_smul ((2 * c)⁻¹)
  have hd' : HasDerivAt
      (fun y => (2 * c)⁻¹ • (h (y + c * t) - h (y - c * t)))
      ((2 * c)⁻¹ • (deriv h (x + c * t) - deriv h (x - c * t))) x := by
    convert hd using 1 <;> simp [Function.comp_def]
    ext y
    rfl
  exact hd'.deriv

theorem velocity_one : P201Specs.OddWave.VelocityOneStatement := by
  intro 𝕜 _ c hc h hh
  refine ⟨velocityOne_contDiff hh c, ?_, ?_⟩
  · intro t x
    rw [velocityOne_second_time (hh.differentiable (by simp)),
      velocityOne_second_space (hh.differentiable (by simp))]
    rw [smul_comm]
  · intro x
    refine ⟨velocityOne_zero c h x, ?_, ?_⟩
    · rw [velocityOne_deriv_time hh.continuous]
      simp only [mul_zero, add_zero, sub_zero, neg_smul, sub_neg_eq_add]
      rw [← add_smul, ← two_mul, smul_smul,
        inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hc.ne'), one_smul]
    · rw [velocityOne_second_time (hh.differentiable (by simp))]
      simp

abbrev regularRadial : P201Specs.OddWave.RegularRadialType :=
  @P201Specs.OddWave.regularRadial

theorem regularRadial_contDiff {𝕜 : Type} [RCLike 𝕜] (m : ℕ) {F : ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (regularRadial m F) := by
  induction m generalizing F with
  | zero => exact contDiff_id.smul hF
  | succ m ih =>
    apply ih
    exact (hF.const_smul _).add
      (contDiff_id.smul (contDiff_infty_iff_deriv.mp hF).2)

theorem regularRadial_zero {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (F : ℝ → 𝕜) :
    regularRadial m F 0 = 0 := by
  induction m generalizing F with
  | zero => exact zero_smul ℝ (F 0)
  | succ m ih => exact ih _

theorem even_deriv_odd {𝕜 : Type} [RCLike 𝕜] {F : ℝ → 𝕜}
    (hF : Function.Even F) : Function.Odd (deriv F) := by
  intro r
  have he := congrArg (fun f : ℝ → 𝕜 => deriv f r) (funext hF)
  rw [deriv_comp_neg] at he
  exact neg_eq_iff_eq_neg.mp he

theorem odd_deriv_even {𝕜 : Type} [RCLike 𝕜] {F : ℝ → 𝕜}
    (hF : Function.Odd F) : Function.Even (deriv F) := by
  intro r
  have he := congrArg (fun f : ℝ → 𝕜 => deriv f r) (funext hF)
  rw [deriv_comp_neg, deriv.fun_neg] at he
  exact neg_injective he

theorem even_deriv_zero {𝕜 : Type} [RCLike 𝕜] {F : ℝ → 𝕜}
    (hF : Function.Even F) : deriv F 0 = 0 := by
  have he := even_deriv_odd hF 0
  simp only [neg_zero] at he
  exact CharZero.eq_neg_self_iff.mp he

theorem regularRadial_odd {𝕜 : Type} [RCLike 𝕜] (m : ℕ) {F : ℝ → 𝕜}
    (hF : Function.Even F) : Function.Odd (regularRadial m F) := by
  induction m generalizing F with
  | zero =>
    intro r
    change (-r) • F (-r) = -(r • F r)
    rw [hF r, neg_smul]
  | succ m ih =>
    apply ih
    intro r
    dsimp only
    rw [hF r, even_deriv_odd hF r]
    simp

theorem regularRadial_deriv_zero {𝕜 : Type} [RCLike 𝕜] (m : ℕ) {F : ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    deriv (regularRadial m F) 0 = (Nat.doubleFactorial (2 * m + 1) : ℝ) • F 0 := by
  induction m generalizing F with
  | zero =>
    have hd := (hasDerivAt_id (0 : ℝ)).smul
      (hF.differentiable (by simp) 0).hasDerivAt
    have he : ((id : ℝ → ℝ) • F : ℝ → 𝕜) = fun r => r • F r := by ext r; rfl
    rw [he] at hd
    simpa [regularRadial, P201Specs.OddWave.regularRadial, Nat.doubleFactorial] using hd.deriv
  | succ m ih =>
    have hT : ContDiff ℝ (⊤ : ℕ∞)
        (fun r => ((2 * m + 3 : ℕ) : ℝ) • F r + r • deriv F r) :=
      (hF.const_smul _).add (contDiff_id.smul (contDiff_infty_iff_deriv.mp hF).2)
    change deriv (regularRadial m _) 0 = _
    rw [ih hT]
    simp only [zero_smul, add_zero, smul_smul]
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
      Nat.doubleFactorial_add_two, Nat.cast_mul]
    congr 1
    push_cast
    ring

theorem regularRadial_second_zero {𝕜 : Type} [RCLike 𝕜] (m : ℕ) {F : ℝ → 𝕜}
    (hF : Function.Even F) : deriv (deriv (regularRadial m F)) 0 = 0 :=
  even_deriv_zero (odd_deriv_even (regularRadial_odd m hF))

theorem radialIterate_eventuallyEq {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {F G : ℝ → 𝕜} {r : ℝ} (he : F =ᶠ[𝓝 r] G) :
    radialIterate m F =ᶠ[𝓝 r] radialIterate m G := by
  induction m with
  | zero => exact he
  | succ m ih =>
    change ((radialDerivative^[m + 1]) F) =ᶠ[𝓝 r] ((radialDerivative^[m + 1]) G)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change radialDerivative (radialIterate m F) =ᶠ[𝓝 r]
      radialDerivative (radialIterate m G)
    filter_upwards [ih.deriv] with s hs
    change s⁻¹ • deriv (radialIterate m F) s = s⁻¹ • deriv (radialIterate m G) s
    rw [hs]

theorem radialDerivative_power_product {𝕜 : Type} [RCLike 𝕜]
    {F : ℝ → 𝕜} (hF : Differentiable ℝ F) (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    radialDerivative (fun s => s ^ (k + 2) • F s) r =
      r ^ k • (((k + 2 : ℕ) : ℝ) • F r + r • deriv F r) := by
  have hd := ((hasDerivAt_id r).pow (k + 2)).smul (hF r).hasDerivAt
  have he : ((id : ℝ → ℝ) ^ (k + 2) • F : ℝ → 𝕜) =
      fun s => s ^ (k + 2) • F s := by ext s; rfl
  rw [he] at hd
  change r⁻¹ • deriv (fun s => s ^ (k + 2) • F s) r = _
  rw [hd.deriv]
  simp only [mul_one, id_eq, Pi.pow_apply, show k + 2 - 1 = k + 1 by omega]
  have h₁ : r⁻¹ * ((k + 2 : ℕ) : ℝ) * r ^ (k + 1) = r ^ k * (k + 2 : ℕ) := by
    rw [pow_succ]
    field_simp
  have h₂ : r⁻¹ * r ^ (k + 2) = r ^ k * r := by
    rw [pow_add]
    field_simp
  rw [smul_add, smul_smul, smul_smul, ← mul_assoc, h₂, h₁]
  module

theorem regularRadial_eq_radialIterate {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {F : ℝ → 𝕜} (hF : ContDiff ℝ (⊤ : ℕ∞) F) {r : ℝ} (hr : r ≠ 0) :
    regularRadial m F r = radialIterate m (fun s => s ^ (2 * m + 1) • F s) r := by
  induction m generalizing F with
  | zero => simp [regularRadial, P201Specs.OddWave.regularRadial,
      radialIterate, P201Specs.OddWave.radialIterate]
  | succ m ih =>
    let T : ℝ → 𝕜 := fun s => ((2 * m + 3 : ℕ) : ℝ) • F s + s • deriv F s
    have hT : ContDiff ℝ (⊤ : ℕ∞) T :=
      (hF.const_smul _).add (contDiff_id.smul (contDiff_infty_iff_deriv.mp hF).2)
    change regularRadial m T r = _
    rw [ih hT]
    change _ = ((radialDerivative^[m + 1]) (fun s => s ^ (2 * (m + 1) + 1) • F s)) r
    rw [Function.iterate_succ_apply]
    have he : (fun s => s ^ (2 * m + 1) • T s) =ᶠ[𝓝 r]
        radialDerivative (fun s => s ^ (2 * (m + 1) + 1) • F s) := by
      filter_upwards [eventually_ne_nhds hr] with s hs
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        radialDerivative_power_product (hF.differentiable (by simp)) (2 * m + 1) hs]
    exact (radialIterate_eventuallyEq m he).eq_of_nhds

theorem regular_radial : P201Specs.OddWave.RegularRadialStatement := by
  intro 𝕜 _ m F hF he
  exact ⟨regularRadial_contDiff m hF, regularRadial_odd m he,
    fun _ hr => regularRadial_eq_radialIterate m hF hr, regularRadial_zero m F,
    regularRadial_deriv_zero m hF, regularRadial_second_zero m he⟩

theorem contDiff_radial_deriv {E 𝕜 : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [RCLike 𝕜] {F : E → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => F p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hH : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (E × ℝ) × ℝ => F p.1.1 p.2) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (hH.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

theorem regularRadial_joint_contDiff {E 𝕜 : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [RCLike 𝕜] (m : ℕ) {F : E → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => F p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => regularRadial m (F p.1) p.2) := by
  induction m generalizing F with
  | zero => exact contDiff_snd.smul hF
  | succ m ih =>
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ =>
      regularRadial m (fun r => ((2 * m + 3 : ℕ) : ℝ) • F p.1 r + r • deriv (F p.1) r) p.2)
    apply ih (F := fun x r => ((2 * m + 3 : ℕ) : ℝ) • F x r + r • deriv (F x) r)
    exact (hF.const_smul _).add (contDiff_snd.smul (contDiff_radial_deriv hF))

theorem velocityOdd_eq_regularRadial {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {c : ℝ} (hc : c ≠ 0) (h : Space (2 * m + 3) → 𝕜)
    (hs : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (sphericalMean h x)) (t : ℝ) (x : Space (2 * m + 3)) :
    velocityOdd c h t x = (c * (Nat.doubleFactorial (2 * m + 1) : ℝ))⁻¹ •
      regularRadial m (sphericalMean h x) (c * t) := by
  by_cases ht : t = 0
  · subst t
    simp [velocityOdd_zero, regularRadial_zero]
  · change (if t = 0 then 0 else _) = _
    rw [ite_eq_right ht, regularRadial_eq_radialIterate m (hs x) (mul_ne_zero hc ht)]
    simp only [show 2 * m + 3 - 2 = 2 * m + 1 by omega,
      show (2 * m + 3 - 3) / 2 = m by omega]

/-- Smoothness of the source formula is reduced to joint smoothness of the
actual spherical integral; the radial transform has no remaining singularity. -/
theorem velocityOdd_contDiff_of_mean {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {c : ℝ} (hc : c ≠ 0) (h : Space (2 * m + 3) → 𝕜)
    (hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Space (2 * m + 3) × ℝ => sphericalMean h p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Space (2 * m + 3) => velocityOdd c h p.1 p.2) := by
  have hsr (x : Space (2 * m + 3)) :
      ContDiff ℝ (⊤ : ℕ∞) (sphericalMean h x) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  simp_rw [velocityOdd_eq_regularRadial m hc h hsr]
  exact ((regularRadial_joint_contDiff m hs).comp
    (contDiff_snd.prodMk (contDiff_const.mul contDiff_fst))).const_smul _

theorem velocityOdd_initial_of_mean {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {c : ℝ} (hc : c ≠ 0) (h : Space (2 * m + 3) → 𝕜)
    (hs : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (sphericalMean h x))
    (he : ∀ x, Function.Even (sphericalMean h x)) (x : Space (2 * m + 3)) :
    velocityOdd c h 0 x = 0 ∧ deriv (fun t => velocityOdd c h t x) 0 = h x ∧
      deriv (deriv (fun t => velocityOdd c h t x)) 0 = 0 := by
  refine ⟨velocityOdd_zero c h x, ?_, ?_⟩
  · have hv : (fun t => velocityOdd c h t x) =
        fun t => (c * (Nat.doubleFactorial (2 * m + 1) : ℝ))⁻¹ •
          regularRadial m (sphericalMean h x) (c * t) :=
      funext fun t => velocityOdd_eq_regularRadial m hc h hs t x
    rw [hv, deriv_fun_const_smul_field, deriv_comp_mul_left]
    simp only [mul_zero]
    rw [regularRadial_deriv_zero m (hs x), smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero hc (Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (Nat.doubleFactorial_pos _)))), one_smul]
    exact sphericalMean_zero (by omega) h x
  · have hv : (fun t => velocityOdd c h t x) =
        fun t => (c * (Nat.doubleFactorial (2 * m + 1) : ℝ))⁻¹ •
          regularRadial m (sphericalMean h x) (c * t) :=
      funext fun t => velocityOdd_eq_regularRadial m hc h hs t x
    have hd : deriv (fun t => velocityOdd c h t x) =
        fun t => (c * (Nat.doubleFactorial (2 * m + 1) : ℝ))⁻¹ •
          (c • deriv (regularRadial m (sphericalMean h x)) (c * t)) := by
      funext t
      rw [hv, deriv_fun_const_smul_field, deriv_comp_mul_left]
    rw [hd, deriv_fun_const_smul_field, deriv_fun_const_smul_field,
      deriv_comp_mul_left]
    simp [regularRadial_second_zero m (he x)]

/-- Smoothness of the partial derivative with respect to the first variable. -/
theorem contDiff_parameter_fderiv {H A E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : H → A → E}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : H × A => fderiv ℝ (fun x => F x p.2) p.1) := by
  have hH : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (H × A) × H => F p.2 p.1.2) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact hH.fderiv contDiff_fst (by simp)

/-- A finite measure carried by a compact set integrates continuous functions. -/
theorem integrable_of_continuous_compact {A E : Type*}
    [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
    [NormedAddCommGroup E] {μ : Measure A} [IsFiniteMeasure μ]
    {K : Set A} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ, a ∈ K)
    {f : A → E} (hf : Continuous f) : Integrable f μ := by
  have hi := hf.continuousOn.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at hi

/-- Differentiation under a fixed compactly carried finite measure. All bounds
are on a compact neighborhood of the parameter, so no global bound is required. -/
theorem hasFDerivAt_integral_compact {H A E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} [IsFiniteMeasure μ] {K : Set A}
    (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ, a ∈ K) {F : H → A → E}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) (x : H) :
    HasFDerivAt (fun y => ∫ a, F y a ∂μ)
      (∫ a, fderiv ℝ (fun y => F y a) x ∂μ) x := by
  have hd := contDiff_parameter_fderiv hF
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod hK).bddAbove_image hd.continuous.continuousOn.norm
  have hi (y : H) : Integrable (F y) μ :=
    integrable_of_continuous_compact hK hμ
      (hF.continuous.comp (continuous_const.prodMk continuous_id))
  have hdi : Integrable (fun a => fderiv ℝ (fun y => F y a) x) μ :=
    integrable_of_continuous_compact hK hμ
      (hd.continuous.comp (continuous_const.prodMk continuous_id))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := F) (F' := fun y a => fderiv ℝ (fun z => F z a) y)
    (bound := fun _ => C) (s := Metric.ball x 1)
    (Metric.ball_mem_nhds x zero_lt_one)
    (Eventually.of_forall fun y => (hi y).aestronglyMeasurable) (hi x)
    hdi.aestronglyMeasurable
  · filter_upwards [hμ] with a ha
    intro y hy
    exact hC (mem_image_of_mem
      (fun p : H × A => ‖fderiv ℝ (fun z => F z p.2) p.1‖)
      (show (y, a) ∈ Metric.closedBall x 1 ×ˢ K from
        ⟨Metric.ball_subset_closedBall hy, ha⟩))
  · exact integrable_const C
  · exact Eventually.of_forall fun a y _ =>
      ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) y).hasFDerivAt

/-- Smooth integration against a fixed finite measure with compact support. -/
theorem contDiff_integral_compact {H A E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} [IsFiniteMeasure μ] {K : Set A}
    (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ, a ∈ K) {F : H → A → E}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ∫ a, F y a ∂μ) := by
  apply contDiff_infty.mpr
  intro k
  induction k generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    have hd : Differentiable ℝ (fun y => ∫ a, F y a ∂μ) :=
      fun x => (hasFDerivAt_integral_compact hK hμ hF x).differentiableAt
    exact hd.continuous
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_integral_compact hK hμ hF x).differentiableAt, by simp, ?_⟩
    intro v
    have he : fderiv ℝ (fun y => ∫ a, F y a ∂μ) =
        fun y => ∫ a, fderiv ℝ (fun z => F z a) y ∂μ :=
      funext fun y => (hasFDerivAt_integral_compact hK hμ hF y).fderiv
    simp_rw [he]
    have hdi (y : H) : Integrable (fun a => fderiv ℝ (fun z => F z a) y) μ :=
      integrable_of_continuous_compact hK hμ
        ((contDiff_parameter_fderiv hF).continuous.comp (continuous_const.prodMk continuous_id))
    simp_rw [ContinuousLinearMap.integral_apply (hdi _) ]
    exact ih ((contDiff_parameter_fderiv hF).clm_apply contDiff_const)

/-- Joint smoothness of the actual fixed-sphere integral. -/
theorem sphericalMean_contDiff {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => sphericalMean h p.1 p.2) := by
  have hi := contDiff_integral_compact (μ := P201Specs.unitSurface n)
    (isCompact_sphere (0 : Space n) 1) (MeanValues.unitSurface_ae_mem n)
    (F := fun p : Space n × ℝ => fun θ : Space n => h (p.1 + p.2 • θ))
    (hh.comp (contDiff_fst.fst.add (contDiff_fst.snd.smul contDiff_snd)))
  exact hi.const_smul ((P201Specs.omega n)⁻¹)

open scoped Pointwise ENNReal

/-- The polar-cone surface measure is invariant under reflection. -/
theorem unitSurface_neg_invariant (n : ℕ) :
    (P201Specs.unitSurface n).IsNegInvariant := by
  constructor
  change Measure.map (fun x : Space n => -x) (P201Specs.unitSurface n) =
    P201Specs.unitSurface n
  have hc (s : Set (Space n)) (hs : MeasurableSet s) :
      P201Specs.unitSurface n s = (n : ℝ≥0∞) *
        volume (Ioo (0 : ℝ) 1 • (s ∩ Metric.sphere 0 1)) := by
    rw [MeanValues.unitSurface_eq_map_toSphere,
      Measure.map_apply (by fun_prop) hs,
      Measure.toSphere_apply' _ ((measurable_subtype_coe) hs)]
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    simp [Space, P201Specs.Space]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs, hc _ (measurable_neg hs), hc s hs]
  congr 1
  have he : Ioo (0 : ℝ) 1 • ((fun x : Space n => -x) ⁻¹' s ∩ Metric.sphere 0 1) =
      (fun x : Space n => -x) ⁻¹' (Ioo (0 : ℝ) 1 • (s ∩ Metric.sphere 0 1)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, rfl⟩
      exact ⟨r, hr, -y, ⟨hy, by simpa using hys⟩, by simp⟩
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, he⟩
      exact ⟨r, hr, -y, ⟨by simpa using hy, by simpa using hys⟩,
        by simpa using congrArg Neg.neg he⟩
  rw [he]
  exact (volume : Measure (Space n)).measure_preimage_neg _

/-- Reflection of the sphere makes its mean even in the radius. -/
theorem sphericalMean_even {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (h : Space n → 𝕜) (x : Space n) : Function.Even (sphericalMean h x) := by
  haveI := unitSurface_neg_invariant n
  intro r
  change (P201Specs.omega n)⁻¹ • (∫ θ, h (x + (-r) • θ) ∂P201Specs.unitSurface n) =
    (P201Specs.omega n)⁻¹ • (∫ θ, h (x + r • θ) ∂P201Specs.unitSurface n)
  simp_rw [neg_smul, ← smul_neg]
  congr 1
  exact integral_neg_eq_self (fun θ : Space n => h (x + r • θ)) _

theorem spherical_mean_regularity : P201Specs.OddWave.SphericalMeanRegularityStatement := by
  intro n hn 𝕜 _ h hh
  exact ⟨sphericalMean_contDiff hh, fun x => sphericalMean_even h x,
    fun x => sphericalMean_zero (by omega) h x⟩

/-- The directional derivative in a fixed spatial direction. -/
def directional {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : H → E) (v : H) : H → E :=
  fun x => fderiv ℝ f x v

theorem directional_contDiff {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : H → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : H) :
    ContDiff ℝ (⊤ : ℕ∞) (directional f v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem laplacian_eq_sum_directional {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (h : Space n → 𝕜) (x : Space n) :
    laplacian h x = ∑ i : Fin n, directional (directional h (coordinate n i)) (coordinate n i) x := by
  apply Finset.sum_congr rfl
  intro i _
  have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]
  simp only [P201Specs.multiPartial, P102.U4.multiPartial, hs, P102.U4.partialWord]
  rfl

/-- Center differentiation commutes with the fixed-sphere integral. -/
theorem directional_sphericalMean {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (r : ℝ) (v x : Space n) :
    directional (fun y => sphericalMean h y r) v x = sphericalMean (directional h v) x r := by
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Space n × Space n => h (p.1 + r • p.2)) :=
    hh.comp (contDiff_fst.add (contDiff_snd.const_smul r))
  have hd := (hasFDerivAt_integral_compact (μ := P201Specs.unitSurface n)
    (isCompact_sphere (0 : Space n) 1) (MeanValues.unitSurface_ae_mem n)
    (F := fun y θ : Space n => h (y + r • θ)) hF x).const_smul
      ((P201Specs.omega n)⁻¹)
  change (fderiv ℝ ((P201Specs.omega n)⁻¹ •
    (fun y : Space n => ∫ θ, h (y + r • θ) ∂P201Specs.unitSurface n)) x) v = _
  rw [hd.fderiv]
  change (P201Specs.omega n)⁻¹ • ((∫ θ, fderiv ℝ (fun y => h (y + r • θ)) x
    ∂P201Specs.unitSurface n) v) = _
  have hi : Integrable (fun θ => fderiv ℝ (fun y => h (y + r • θ)) x)
      (P201Specs.unitSurface n) :=
    integrable_of_continuous_compact (isCompact_sphere (0 : Space n) 1)
      (MeanValues.unitSurface_ae_mem n)
      ((contDiff_parameter_fderiv
        (F := fun y θ : Space n => h (y + r • θ)) hF).continuous.comp
          (continuous_const.prodMk continuous_id))
  rw [ContinuousLinearMap.integral_apply hi]
  simp only [fderiv_comp_add_right]
  rfl

theorem laplacian_sphericalMean {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (r : ℝ) (x : Space n) :
    laplacian (fun y => sphericalMean h y r) x = sphericalMean (laplacian h) x r := by
  rw [laplacian_eq_sum_directional]
  have he (v : Space n) : directional (fun y => sphericalMean h y r) v =
      fun y => sphericalMean (directional h v) y r :=
    funext fun y => directional_sphericalMean hh r v y
  simp_rw [he]
  simp_rw [directional_sphericalMean (directional_contDiff hh _) r]
  change (∑ i : Fin n, (P201Specs.omega n)⁻¹ •
      ∫ θ, directional (directional h (coordinate n i)) (coordinate n i) (x + r • θ)
        ∂P201Specs.unitSurface n) = _
  rw [← Finset.smul_sum]
  congr 1
  have hi (i : Fin n) : Integrable
      (fun θ : Space n => directional (directional h (coordinate n i))
        (coordinate n i) (x + r • θ)) (P201Specs.unitSurface n) := by
    apply integrable_of_continuous_compact (isCompact_sphere (0 : Space n) 1)
      (MeanValues.unitSurface_ae_mem n)
    exact (directional_contDiff (directional_contDiff hh (coordinate n i))
      (coordinate n i)).continuous.comp (continuous_const.add (continuous_id.const_smul r))
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => (laplacian_eq_sum_directional h (x + r • θ)).symm

theorem laplacian_contDiff {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (laplacian h) := by
  simp_rw [show laplacian h = fun x => ∑ i : Fin n,
    directional (directional h (coordinate n i)) (coordinate n i) x from
      funext (laplacian_eq_sum_directional h)]
  exact ContDiff.sum fun _ _ => directional_contDiff (directional_contDiff hh _) _

/-- The divergence theorem identifies the first radial derivative with the
ball integral of the Laplacian. -/
theorem sphericalMean_flux {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x : Space n)
    {r : ℝ} (hr : 0 < r) :
    r ^ (n - 1) • deriv (sphericalMean h x) r =
      (P201Specs.omega n)⁻¹ • ∫ y in Metric.ball x r, laplacian h y := by
  have hd := MeanValues.spherical_mean_derivative hn (⊤ : Domain n) h
    (hh.of_le (by simp)).contDiffOn x r hr (by simp)
  rw [hd.deriv, smul_smul]
  congr 1
  have hw := (MeanValues.omega_pos hn).ne'
  field_simp

/-- Darboux's equation follows by differentiating the ball flux and commuting
spatial derivatives with the fixed unit-sphere integral. -/
theorem darboux : P201Specs.OddWave.DarbouxStatement := by
  intro n hn 𝕜 _ h hh x r hr
  change laplacian (fun y => sphericalMean h y r) x =
    deriv (deriv (sphericalMean h x)) r +
      (((n - 1 : ℕ) : ℝ) / r) • deriv (sphericalMean h x) r
  have hs : ContDiff ℝ (⊤ : ℕ∞) (sphericalMean h x) :=
    (sphericalMean_contDiff hh).comp (contDiff_const.prodMk contDiff_id)
  have hsr := (contDiff_infty_iff_deriv.mp hs).2
  have hd₁ := ((hasDerivAt_id r).pow (n - 1)).fun_smul
    (hsr.differentiable (by simp) r).hasDerivAt
  have hd₂ := (MeanValues.ballIntegral_hasDerivAt (by omega) (⊤ : Domain n)
    (laplacian h) (laplacian_contDiff hh).continuous.continuousOn x r hr (by simp)).const_smul
      ((P201Specs.omega n)⁻¹)
  have he : (fun s : ℝ => s ^ (n - 1) • deriv (sphericalMean h x) s) =ᶠ[𝓝 r]
      (fun s : ℝ => (P201Specs.omega n)⁻¹ • ∫ y in Metric.ball x s, laplacian h y) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact sphericalMean_flux (by omega) hh x hs
  have hd := hd₁.unique (hd₂.congr_of_eventuallyEq he)
  simp only [id_eq, mul_one] at hd
  have hpow : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.ne'
  have hcoeff : r ^ (n - 1) * (((n - 1 : ℕ) : ℝ) / r) =
      (n - 1 : ℕ) * r ^ (n - 1 - 1) := by
    have he : n - 1 = (n - 1 - 1) + 1 := by omega
    have hp : r ^ (n - 1) = r ^ (n - 1 - 1) * r := by
      conv_lhs => rw [he, pow_succ]
    rw [hp]
    field_simp
  have hd' : r ^ (n - 1) •
      (deriv (deriv (sphericalMean h x)) r +
        (((n - 1 : ℕ) : ℝ) / r) • deriv (sphericalMean h x) r) =
      r ^ (n - 1) • sphericalMean (laplacian h) x r := by
    rw [smul_add, smul_smul, hcoeff]
    convert hd using 1 <;> dsimp [sphericalMean, P201Specs.OddWave.sphericalMean,
      P201Specs.MeanValues.unitSphereMean]
    module
  rw [laplacian_sphericalMean hh]
  have hc := congrArg (fun z : 𝕜 => (r ^ (n - 1))⁻¹ • z) hd'
  simpa only [smul_smul, inv_mul_cancel₀ hpow, one_smul] using hc.symm


theorem directional_add_smooth {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : H → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v x : H) :
    directional (fun y => f y + g y) v x = directional f v x + directional g v x := by
  simp only [directional, fderiv_fun_add (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x), add_apply]

theorem directional_const_smul {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : H → E) (a : ℝ) (v x : H) :
    directional (fun y => a • f y) v x = a • directional f v x := by
  change (fderiv ℝ (a • f) x) v = _
  rw [fderiv_const_smul_field]
  rfl

theorem laplacian_add_smooth {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f g : Space n → 𝕜} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Space n) :
    laplacian (fun y => f y + g y) x = laplacian f x + laplacian g x := by
  simp_rw [laplacian_eq_sum_directional]
  have h (v : Space n) : directional (fun y => f y + g y) v =
      fun y => directional f v y + directional g v y :=
    funext fun y => directional_add_smooth hf hg v y
  simp_rw [h, directional_add_smooth (directional_contDiff hf _) (directional_contDiff hg _)]
  exact Finset.sum_add_distrib

theorem laplacian_const_smul {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space n → 𝕜) (a : ℝ) (x : Space n) :
    laplacian (fun y => a • f y) x = a • laplacian f x := by
  simp_rw [laplacian_eq_sum_directional]
  have h (v : Space n) : directional (fun y => a • f y) v =
      fun y => a • directional f v y := funext fun y => directional_const_smul f a v y
  simp_rw [h, directional_const_smul]
  exact (Finset.smul_sum ..).symm

theorem laplacian_neg {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space n → 𝕜) (x : Space n) :
    laplacian (fun y => -f y) x = -laplacian f x := by
  simpa only [neg_one_smul] using laplacian_const_smul f (-1) x

theorem laplacian_const {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (a : 𝕜) (x : Space n) :
    laplacian (fun _ => a) x = 0 := by
  simp_rw [laplacian_eq_sum_directional]
  change (∑ i : Fin n, (fderiv ℝ (fun y => (fderiv ℝ (fun _ : Space n => a) y) (coordinate n i)) x) (coordinate n i)) = 0
  simp



theorem directional_commute {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : H → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w x : H) :
    directional (directional f v) w x = directional (directional f w) v x := by
  change (fderiv ℝ (fun y => (fderiv ℝ f y) v) x) w =
    (fderiv ℝ (fun y => (fderiv ℝ f y) w) x) v
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hdf.differentiable (by simp) x)
    (differentiableAt_const v),
    fderiv_clm_apply (hdf.differentiable (by simp) x)
    (differentiableAt_const w)]
  simpa using (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq w v

theorem directional_prod_left {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : H × ℝ → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v x : H) (r : ℝ) :
    directional (fun y => f (y, r)) v x = directional f (v, 0) (x, r) := by
  have hmap : HasFDerivAt (fun y : H => (y, r))
      ((ContinuousLinearMap.id ℝ H).prod (0 : H →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const r x)
  have hd := (hf.differentiable (by simp) (x, r)).hasFDerivAt.comp x hmap
  change (fderiv ℝ (fun y => f (y, r)) x) v = _
  simpa only [Function.comp_def, directional, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply] using
    congrArg (fun L => L v) hd.fderiv

theorem deriv_prod_right {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : H × ℝ → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : H) (r : ℝ) :
    deriv (fun s => f (x, s)) r = directional f (0, 1) (x, r) := by
  have hd := (hf.differentiable (by simp) (x, r)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
  exact hd.deriv

theorem laplacian_eq_sum_joint_directional {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {F : Space n → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => F p.1 p.2))
    (x : Space n) (r : ℝ) :
    laplacian (fun y => F y r) x = ∑ i : Fin n,
      directional (directional (fun p : Space n × ℝ => F p.1 p.2)
        (coordinate n i, 0)) (coordinate n i, 0) (x, r) := by
  rw [laplacian_eq_sum_directional]
  apply Finset.sum_congr rfl
  intro i _
  have he : directional (fun y => F y r) (coordinate n i) =
      fun y => directional (fun p : Space n × ℝ => F p.1 p.2) (coordinate n i, 0) (y, r) :=
    funext fun y => directional_prod_left hF _ y r
  rw [he]
  exact directional_prod_left (directional_contDiff hF _) _ x r

theorem laplacian_joint_contDiff {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {F : Space n → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => F p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ =>
      laplacian (fun y => F y p.2) p.1) := by
  simp_rw [laplacian_eq_sum_joint_directional hF]
  exact ContDiff.sum fun _ _ => directional_contDiff (directional_contDiff hF _) _

theorem laplacian_radial_deriv {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {F : Space n → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => F p.1 p.2))
    (x : Space n) (r : ℝ) :
    laplacian (fun y => deriv (F y) r) x =
      deriv (fun s => laplacian (fun y => F y s) x) r := by
  let f : Space n × ℝ → 𝕜 := fun p => F p.1 p.2
  let t : Space n × ℝ := (0, 1)
  have he : (fun p : Space n × ℝ => deriv (F p.1) p.2) = directional f t :=
    funext fun p => deriv_prod_right hF p.1 p.2
  have hFr : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => deriv (F p.1) p.2) := by
    rw [he]
    exact directional_contDiff hF t
  rw [laplacian_eq_sum_joint_directional hFr]
  simp_rw [he]
  have hL : (fun s => laplacian (fun y => F y s) x) =
      fun s => ∑ i : Fin n, directional (directional f (coordinate n i, 0))
        (coordinate n i, 0) (x, s) := funext fun s => laplacian_eq_sum_joint_directional hF x s
  rw [hL, deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i _
    let v : Space n × ℝ := (coordinate n i, 0)
    have hc : directional (directional f t) v = directional (directional f v) t :=
      funext fun p => directional_commute hF t v p
    rw [deriv_prod_right (directional_contDiff (directional_contDiff hF v) v), hc]
    exact directional_commute (directional_contDiff hF v) t v (x, r)
  · intro i _
    exact (((directional_contDiff (directional_contDiff hF (coordinate n i, 0))
      (coordinate n i, 0)).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) r)



/-- Differentiation of the polynomial radial lowering operator. -/
theorem deriv_radialLowering {𝕜 : Type} [RCLike 𝕜] {F : ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (a r : ℝ) :
    deriv (fun s => a • F s + s • deriv F s) r =
      (a + 1) • deriv F r + r • deriv (deriv F) r := by
  have h₁ := hF.differentiable (by simp)
  have h₂ := (contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp)
  have hd := (((h₁ r).hasDerivAt.const_smul a).fun_add
    ((hasDerivAt_id r).fun_smul (h₂ r).hasDerivAt)).deriv
  simp only [Pi.smul_apply, id_eq, one_smul] at hd
  rw [hd]
  module

/-- The second derivative of the polynomial radial lowering operator. -/
theorem second_radialLowering {𝕜 : Type} [RCLike 𝕜] {F : ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (a r : ℝ) :
    deriv (deriv (fun s => a • F s + s • deriv F s)) r =
      (a + 2) • deriv (deriv F) r + r • deriv (deriv (deriv F)) r := by
  have he : deriv (fun s => a • F s + s • deriv F s) =
      fun s => (a + 1) • deriv F s + s • deriv (deriv F) s :=
    funext (deriv_radialLowering hF a)
  rw [he, deriv_radialLowering (contDiff_infty_iff_deriv.mp hF).2]
  rw [show a + 1 + 1 = a + 2 by ring]

theorem second_radialProduct {𝕜 : Type} [RCLike 𝕜] {F : ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (r : ℝ) :
    deriv (deriv (fun s => s • F s)) r =
      (2 : ℝ) • deriv F r + r • deriv (deriv F) r := by
  have hd : deriv (fun s => s • F s) =
      fun s => (1 : ℝ) • F s + s • deriv F s := by
    funext s
    have he := ((hasDerivAt_id s).fun_smul
      (hF.differentiable (by simp) s).hasDerivAt).deriv
    simp only [id_eq, one_smul] at he ⊢
    rw [he]
    module
  rw [hd, deriv_radialLowering hF]
  norm_num

/-- Multiplying Darboux's equation by the radius before differentiation avoids
any differentiation of inverse powers. -/
theorem darboux_lowering {𝕜 : Type} [RCLike 𝕜] {F L : ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hL : Differentiable ℝ L) (a : ℝ)
    (hD : ∀ r : ℝ, 0 < r → L r = deriv (deriv F) r +
      ((a + 1) / r) • deriv F r) {r : ℝ} (hr : 0 < r) :
    a • L r + r • deriv L r =
      deriv (deriv (fun s => a • F s + s • deriv F s)) r +
        ((a - 1) / r) • deriv (fun s => a • F s + s • deriv F s) r := by
  have hF₁ := (contDiff_infty_iff_deriv.mp hF).2
  have hF₂ := (contDiff_infty_iff_deriv.mp hF₁).2
  have he : (fun s => s • L s) =ᶠ[𝓝 r]
      (fun s => s • deriv (deriv F) s + (a + 1) • deriv F s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    rw [hD s hs, smul_add, smul_smul, mul_div_cancel₀ _ hs.ne']
  have hd := he.deriv_eq
  have hdL := ((hasDerivAt_id r).fun_smul (hL r).hasDerivAt).deriv
  have hdF := (((hasDerivAt_id r).fun_smul
    (hF₂.differentiable (by simp) r).hasDerivAt).fun_add
    ((hF₁.differentiable (by simp) r).hasDerivAt.const_smul (a + 1))).deriv
  simp only [Pi.smul_apply, id_eq, one_smul] at hdL hdF
  rw [hdL, hdF] at hd
  have hd' : r • deriv L r =
      r • deriv (deriv (deriv F)) r + (a + 2) • deriv (deriv F) r - L r := by
    apply eq_sub_iff_add_eq.mpr
    calc
      _ = r • deriv (deriv (deriv F)) r + deriv (deriv F) r +
          (a + 1) • deriv (deriv F) r := hd
      _ = _ := by module
  rw [hd', hD r hr, second_radialLowering hF, deriv_radialLowering hF]
  match_scalars <;> field_simp <;> ring

/-- The regular radial transform changes Darboux's equation into the wave
identity, on positive radii. -/
theorem regularRadial_wave_positive {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {F : Space n → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => F p.1 p.2))
    (hD : ∀ (x : Space n) (r : ℝ), 0 < r →
      laplacian (fun y => F y r) x = deriv (deriv (F x)) r +
        (((2 * m + 2 : ℕ) : ℝ) / r) • deriv (F x) r)
    (x : Space n) (r : ℝ) (hr : 0 < r) :
    deriv (deriv (regularRadial m (F x))) r =
      laplacian (fun y => regularRadial m (F y) r) x := by
  induction m generalizing F with
  | zero =>
    change deriv (deriv (fun s => s • F x s)) r =
      laplacian (fun y => r • F y r) x
    have hxr : ContDiff ℝ (⊤ : ℕ∞) (F x) :=
      hF.comp (contDiff_const.prodMk contDiff_id)
    rw [second_radialProduct hxr,
      laplacian_const_smul, hD x r hr]
    norm_num only [Nat.cast_ofNat, Nat.mul_zero, Nat.zero_add]
    match_scalars <;> field_simp <;> ring
  | succ m ih =>
    let a : ℝ := (2 * m + 3 : ℕ)
    let T : Space n → ℝ → 𝕜 := fun y s => a • F y s + s • deriv (F y) s
    have hT : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => T p.1 p.2) :=
      (hF.const_smul a).add (contDiff_snd.smul (contDiff_radial_deriv hF))
    change deriv (deriv (regularRadial m (T x))) r =
      laplacian (fun y => regularRadial m (T y) r) x
    apply ih hT
    intro y s hs
    have hxs : ContDiff ℝ (⊤ : ℕ∞) (fun z => F z s) :=
      hF.comp (contDiff_id.prodMk contDiff_const)
    have hdxs : ContDiff ℝ (⊤ : ℕ∞) (fun z => deriv (F z) s) :=
      (contDiff_radial_deriv hF).comp (contDiff_id.prodMk contDiff_const)
    have hL : Differentiable ℝ (fun s => laplacian (fun z => F z s) y) :=
      ((laplacian_joint_contDiff hF).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have heL : laplacian (fun z => T z s) y =
        a • laplacian (fun z => F z s) y +
          s • deriv (fun q => laplacian (fun z => F z q) y) s := by
      dsimp only [T]
      rw [laplacian_add_smooth (hxs.const_smul a) (hdxs.const_smul s),
        laplacian_const_smul, laplacian_const_smul, laplacian_radial_deriv hF]
    rw [heL]
    have hFy : ContDiff ℝ (⊤ : ℕ∞) (F y) :=
      hF.comp (contDiff_const.prodMk contDiff_id)
    have ha : a - 1 = ((2 * m + 2 : ℕ) : ℝ) := by
      dsimp [a]
      push_cast
      ring
    have hb : a + 1 = ((2 * (m + 1) + 2 : ℕ) : ℝ) := by
      dsimp [a]
      push_cast
      ring
    have hd := darboux_lowering hFy hL a
      (fun q hq => by rw [hb]; exact hD y q hq) hs
    simpa only [T, ha] using hd



/-- The smooth odd radial transform satisfies its equation at negative radii
and at the removable point whenever it satisfies it at positive radii. -/
theorem regularRadial_wave_of_positive {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (m : ℕ) {F : Space n → ℝ → 𝕜}
    (he : ∀ x, Function.Even (F x))
    (hp : ∀ (x : Space n) (r : ℝ), 0 < r →
      deriv (deriv (regularRadial m (F x))) r =
        laplacian (fun y => regularRadial m (F y) r) x)
    (x : Space n) (r : ℝ) :
    deriv (deriv (regularRadial m (F x))) r =
      laplacian (fun y => regularRadial m (F y) r) x := by
  rcases lt_trichotomy 0 r with hr | hr | hr
  · exact hp x r hr
  · subst r
    rw [regularRadial_second_zero m (he x)]
    simp_rw [regularRadial_zero]
    exact (laplacian_const 0 x).symm
  · have hodd := even_deriv_odd (odd_deriv_even (regularRadial_odd m (he x))) (-r)
    have hneg : (fun y => regularRadial m (F y) r) =
        fun y => -regularRadial m (F y) (-r) := by
      funext y
      simpa only [neg_neg] using regularRadial_odd m (he y) (-r)
    rw [neg_neg] at hodd
    rw [hodd, hp x (-r) (neg_pos.mpr hr), hneg]
    exact (laplacian_neg _ _).symm

/-- Rescaling the globally regular radial wave gives the original velocity formula. -/
theorem velocityOdd_wave_of_mean {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {c : ℝ} (hc : c ≠ 0) (h : Space (2 * m + 3) → 𝕜)
    (hs : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (sphericalMean h x))
    (hp : ∀ (x : Space (2 * m + 3)) (r : ℝ), 0 < r →
      deriv (deriv (regularRadial m (sphericalMean h x))) r =
        laplacian (fun y => regularRadial m (sphericalMean h y) r) x)
    (t : ℝ) (x : Space (2 * m + 3)) :
    deriv (deriv (fun s => velocityOdd c h s x)) t =
      c ^ 2 • laplacian (velocityOdd c h t) x := by
  let a : ℝ := (c * (Nat.doubleFactorial (2 * m + 1) : ℝ))⁻¹
  have hv : (fun s => velocityOdd c h s x) =
      fun s => a • regularRadial m (sphericalMean h x) (c * s) :=
    funext fun s => velocityOdd_eq_regularRadial m hc h hs s x
  have hd : deriv (fun s => velocityOdd c h s x) =
      fun s => a • (c • deriv (regularRadial m (sphericalMean h x)) (c * s)) := by
    funext s
    rw [hv, deriv_fun_const_smul_field, deriv_comp_mul_left]
  rw [hd, deriv_fun_const_smul_field, deriv_fun_const_smul_field, deriv_comp_mul_left,
    regularRadial_wave_of_positive m (fun y => sphericalMean_even h y) hp]
  have hvx : velocityOdd c h t =
      fun y => a • regularRadial m (sphericalMean h y) (c * t) :=
    funext fun y => velocityOdd_eq_regularRadial m hc h hs t y
  rw [hvx, laplacian_const_smul]
  simp only [smul_smul, pow_two]
  congr 1
  ring

/-- The odd-dimensional velocity propagator solves the wave equation,
with its smooth extension and the prescribed initial jets. -/
theorem velocity_odd : P201Specs.OddWave.VelocityOddStatement := by
  intro n hn hnodd
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = 2 * m + 3 := by
    obtain ⟨k, hk⟩ := hnodd
    exact ⟨k - 1, by omega⟩
  intro 𝕜 _ c hc h hh
  have hs := sphericalMean_contDiff hh
  have hsr (x : Space (2 * m + 3)) :
      ContDiff ℝ (⊤ : ℕ∞) (sphericalMean h x) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  have hp (x : Space (2 * m + 3)) (r : ℝ) (hr : 0 < r) :
      deriv (deriv (regularRadial m (sphericalMean h x))) r =
        laplacian (fun y => regularRadial m (sphericalMean h y) r) x := by
    refine regularRadial_wave_positive m hs ?_ x r hr
    intro y s hspos
    simpa only [show 2 * m + 3 - 1 = 2 * m + 2 by omega] using
      (darboux (by omega) h hh y s hspos)
  exact ⟨velocityOdd_contDiff_of_mean m hc.ne' h hs,
    fun t x => velocityOdd_wave_of_mean m hc.ne' h hsr hp t x,
    velocityOdd_initial_of_mean m hc.ne' h hsr (fun x => sphericalMean_even h x)⟩

end P201.OddWave
