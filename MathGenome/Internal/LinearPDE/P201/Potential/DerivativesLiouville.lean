import MathGenome.Internal.LinearPDE.P201.Potential.MeanValues
import MathGenome.Internal.LinearPDE.P201Specs.Potential.DerivativesLiouville
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology
namespace P201.DerivativesLiouville

/-- An entire nonnegative harmonic function is constant. The proof compares
integrals over nested balls, so it does not require a derivative bound. -/
theorem nonnegative_harmonic_constant {n : ℕ} (hn : 1 ≤ n)
    (v : Space n → ℝ) (hv : MeanValues.IsHarmonic ⊤ v) (hpos : ∀ x, 0 ≤ v x) :
    ∀ a b, v a ≤ v b := by
  have hc : Continuous v := continuousOn_univ.mp hv.1.continuousOn
  have hint (a : Space n) {r : ℝ} (hr : 0 < r) :
      (∫ x in ball a r, v x) = (omega n / n) * r ^ n * v a := by
    have hm := (MeanValues.mean_values hn ⊤ v hv a r hr (subset_univ _)).2
    have hvol := ballVolumeNormalization hn a r hr.le
    have hvolpos : 0 < volume.real (ball a r) :=
      ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume a hr)) measure_ball_lt_top.ne
    change v a = (volume.real (ball a r))⁻¹ • _ at hm
    rw [smul_eq_mul] at hm
    have hi : (∫ x in ball a r, v x) = volume.real (ball a r) * v a := by
      rw [hm, ← mul_assoc, mul_inv_cancel₀ hvolpos.ne', one_mul]
    rw [hi, hvol]
    ring
  intro a b
  have hcomp (r : ℝ) (hr : 0 < r) :
      v a ≤ (1 + dist a b / r) ^ n * v b := by
    have hrd : 0 < r + dist a b := add_pos_of_pos_of_nonneg hr dist_nonneg
    have hsub : ball a r ⊆ ball b (r + dist a b) := by
      intro x hx
      apply mem_ball.mpr
      calc
        dist x b ≤ dist x a + dist a b := dist_triangle _ _ _
        _ < r + dist a b := by have hh := mem_ball.mp hx; linarith
    have hi : (∫ x in ball a r, v x) ≤ ∫ x in ball b (r + dist a b), v x :=
      setIntegral_mono_set ((hc.continuousOn.integrableOn_compact
        (isCompact_closedBall b (r + dist a b))).mono_set ball_subset_closedBall)
        (by filter_upwards [] with x using hpos x) (Eventually.of_forall hsub)
    rw [hint a hr, hint b hrd] at hi
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hcoef : 0 < omega n / n := div_pos (MeanValues.omega_pos hn) hnpos
    have heq : (r + dist a b) ^ n = r ^ n * (1 + dist a b / r) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [heq] at hi
    have hi' : (omega n / n * r ^ n) * v a ≤
        (omega n / n * r ^ n) * ((1 + dist a b / r) ^ n * v b) := by
      convert hi using 1; ring
    exact (mul_le_mul_iff_right₀ (mul_pos hcoef (pow_pos hr n))).mp hi'
  have hlim : Tendsto (fun r : ℝ => (1 + dist a b / r) ^ n * v b) atTop (𝓝 (v b)) := by
    have ht : Tendsto (fun r : ℝ => dist a b / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add ht).pow n).mul_const (v b)
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun r hr => hcomp r (by linarith)⟩)

/-- One-sided Liouville, in every dimension n ≥ 1. -/
theorem liouville : P201Specs.DerivativesLiouville.LiouvilleStatement := by
  intro n hn u hu hb
  have hh := (MeanValues.harmonic_bridge ⊤ u).mp hu
  rcases hb with ⟨M, hM⟩ | ⟨m, hm⟩
  · let v : Space n → ℝ := fun x => M - u x
    have hv : MeanValues.IsHarmonic ⊤ v :=
      (MeanValues.harmonic_bridge ⊤ v).mpr
        ((InnerProductSpace.harmonicOnNhd_const M).sub hh)
    have hvpos : ∀ x, 0 ≤ v x := fun x => sub_nonneg.mpr (hM x)
    refine ⟨u 0, fun x => ?_⟩
    have h₁ := nonnegative_harmonic_constant hn v hv hvpos x 0
    have h₂ := nonnegative_harmonic_constant hn v hv hvpos 0 x
    dsimp [v] at h₁ h₂
    linarith
  · let v : Space n → ℝ := fun x => u x - m
    have hv : MeanValues.IsHarmonic ⊤ v :=
      (MeanValues.harmonic_bridge ⊤ v).mpr
        (hh.sub (InnerProductSpace.harmonicOnNhd_const m))
    have hvpos : ∀ x, 0 ≤ v x := fun x => sub_nonneg.mpr (hm x)
    refine ⟨u 0, fun x => ?_⟩
    have h₁ := nonnegative_harmonic_constant hn v hv hvpos x 0
    have h₂ := nonnegative_harmonic_constant hn v hv hvpos 0 x
    dsimp [v] at h₁ h₂
    linarith

open scoped Convolution
open P102.U4 (partialWord testPartialWord)

/-- The coordinate derivatives of a convolution fall on its smooth compact kernel. -/
theorem partialWord_convolution {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space n → 𝕜) (hf : LocallyIntegrable f volume)
    (φ : Test ℝ (⊤ : Domain n)) (l : List (Fin n)) :
    partialWord (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip] (φ : Space n → ℝ)) l =
      f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip] (partialWord φ l) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    ext x
    let ψ := testPartialWord ⊤ l φ
    have hψ : (ψ : Space n → ℝ) = partialWord φ l := P102.U4.testPartialWord_coe _ _ _
    change fderiv ℝ (partialWord (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip]
      (φ : Space n → ℝ)) l) x (coordinate n i) = _
    rw [ih, ← hψ]
    rw [(ψ.hasCompactSupport.hasFDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ).flip hf (ψ.contDiff.of_le (by simp)) x).fderiv]
    rw [convolution_precompR_apply _ hf (ψ.hasCompactSupport.fderiv ℝ)
      (ψ.contDiff.continuous_fderiv (by simp))]
    congr 1
    rw [hψ]
    rfl

/-- Coordinate words commute with a constant real dilation. -/
theorem partialWord_dilate {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (l : List (Fin n)) :
    partialWord (fun x => f (c • x)) l =
      fun x => c ^ l.length * partialWord f l (c • x) := by
  induction l with
  | nil => simp [partialWord]
  | cons i l ih =>
    ext x
    change fderiv ℝ (partialWord (fun x => f (c • x)) l) x (coordinate n i) = _
    rw [ih]
    have hd := ((P102.U4.partialWord_contDiff hf l).differentiable (by simp) (c • x)).hasFDerivAt
    have hc := (hd.comp x ((hasFDerivAt_id x).const_smul c)).const_smul (c ^ l.length)
    change fderiv ℝ (fun x => c ^ l.length • partialWord f l (c • x)) x _ = _
    have heq : fderiv ℝ (fun x => c ^ l.length • partialWord f l (c • x)) x =
        (c ^ l.length) • (fderiv ℝ (partialWord f l) (c • x)).comp
          (c • ContinuousLinearMap.id ℝ (Space n)) := hc.fderiv
    rw [heq]
    simp [partialWord, coordinate, P201Specs.coordinate, pow_succ, smul_smul]

/-- A fixed smooth radial compact kernel; it is not normalized yet. -/
def baseKernel (n : ℕ) : Test ℝ (⊤ : Domain n) where
  toFun := MeanValues.radialKernel (1 / 2)
  contDiff' := MeanValues.radialKernel_contDiff _
  hasCompactSupport' := MeanValues.radialKernel_hasCompactSupport (by norm_num)
  tsupport_subset' := subset_univ _

/-- Scale the fixed kernel without changing its profile. -/
def scaledKernel (n : ℕ) (r : ℝ) (hr : 0 < r) : Test ℝ (⊤ : Domain n) where
  toFun x := baseKernel n (r⁻¹ • x)
  contDiff' := (baseKernel n).contDiff.comp (contDiff_id.const_smul _)
  hasCompactSupport' := (baseKernel n).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  tsupport_subset' := subset_univ _

theorem scaledKernel_integral {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (∫ x, scaledKernel n r hr x) = r ^ n * ∫ x, baseKernel n x := by
  change (∫ x, baseKernel n (r⁻¹ • x)) = _
  simpa only [P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
    Measure.integral_comp_inv_smul_of_nonneg volume (baseKernel n) hr.le

theorem scaledKernel_neg {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Space n) :
    scaledKernel n r hr (-x) = scaledKernel n r hr x := by
  simp [scaledKernel, baseKernel, MeanValues.radialKernel]

theorem scaledKernel_smul {n : ℕ} {r : ℝ} (hr : 0 < r) (s : ℝ)
    {θ : Space n} (hθ : θ ∈ sphere 0 1) :
    scaledKernel n r hr (s • θ) = expNegInvGlue ((1 / 2 : ℝ)^2 - (s / r)^2) := by
  have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
  simp [scaledKernel, baseKernel, MeanValues.radialKernel, norm_smul, hθn,
    Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, div_eq_mul_inv, mul_comm]

/-- Every derivative of the scaled kernel has the expected uniform scaling bound. -/
theorem scaledKernel_derivative_bound {n : ℕ} (l : List (Fin n)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (r : ℝ) (hr : 0 < r) (x : Space n),
      ‖partialWord (scaledKernel n r hr) l x‖ ≤ B / r ^ l.length := by
  let ψ := testPartialWord ⊤ l (baseKernel n)
  obtain ⟨B, hB⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun r hr x => ?_⟩
  have hval := congrFun (partialWord_dilate (baseKernel n).contDiff r⁻¹ l) x
  change partialWord (scaledKernel n r hr) l x = _ at hval
  rw [hval, norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _)]
  have hb : ‖partialWord (baseKernel n) l (r⁻¹ • x)‖ ≤ max B 1 := by
    rw [← P102.U4.testPartialWord_coe]
    exact (hB _).trans (le_max_left _ _)
  calc
    _ ≤ r⁻¹ ^ l.length * max B 1 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [inv_pow, div_eq_mul_inv, mul_comm]

/-- Radial kernels reproduce sphere means, with precisely the scaled fixed profile. -/
theorem scaledKernel_convolution_eq {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] {f : Space n → 𝕜}
    (hf : LocallyIntegrable f volume) (a : Space n) {r : ℝ} (hr : 0 < r)
    (hm : ∀ s : ℝ, 0 < s → s < r / 2 →
      (∫ θ, f (a + s • θ) ∂unitSurface n) = omega n • f a) :
    ((scaledKernel n r hr : Space n → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) a =
      (∫ t, scaledKernel n r hr t) • f a := by
  let K := scaledKernel n r hr
  have hKneg (t : Space n) : K (-t) = K t := scaledKernel_neg hr t
  have hi := K.hasCompactSupport.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)
    K.continuous hf a
  have hip : Integrable (fun t => K t • f (a + t)) volume := by
    simpa only [ContinuousLinearMap.lsmul_apply, hKneg, sub_neg_eq_add]
      using hi.integrable.comp_neg
  rw [convolution_def]
  change (∫ t, K t • f (a - t)) = _
  rw [← integral_neg_eq_self]
  simp only [hKneg, sub_neg_eq_add]
  rw [MeanValues.integral_polar hn hip,
    MeanValues.integral_polar hn (K.continuous.integrable_of_hasCompactSupport K.hasCompactSupport),
    ← integral_smul_const]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  have hek : ∀ᵐ θ ∂unitSurface n,
      K (s • θ) = expNegInvGlue ((1 / 2 : ℝ)^2 - (s / r)^2) := by
    filter_upwards [MeanValues.unitSurface_ae_mem n] with θ hθ
    exact scaledKernel_smul hr s hθ
  rw [integral_congr_ae (hek.mono (fun θ hθ => congrArg (fun k => k • f (a + s • θ)) hθ)),
    integral_smul, integral_congr_ae hek, integral_const]
  by_cases hsr : s < r / 2
  · rw [hm s hs hsr]
    simp only [Measure.real, omega, P201Specs.omega, smul_smul, smul_eq_mul]
    congr 1
    ring
  · have hsdiv : 1 / 2 ≤ s / r := (le_div_iff₀ hr).mpr (by linarith)
    have hk : expNegInvGlue ((1 / 2 : ℝ)^2 - (s / r)^2) = 0 :=
      expNegInvGlue.zero_of_nonpos (by nlinarith)
    simp only [hk, zero_smul, smul_zero]

/-- Near the center the cut-off harmonic function is reproduced by the fixed-profile kernel. -/
theorem harmonic_scaledKernel_representation {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜)
    (hu : MeanValues.IsHarmonic Ω u) (a : Space n) {r : ℝ} (hr : 0 < r)
    (hball : closedBall a r ⊆ (Ω : Set _)) :
    let f := (ball a r).indicator u
    let m := ∫ t, scaledKernel n r hr t
    u =ᶠ[𝓝 a] m⁻¹ • (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip]
      (scaledKernel n r hr : Space n → ℝ)) := by
  dsimp only
  let f := (ball a r).indicator u
  let K := scaledKernel n r hr
  let m := ∫ t, K t
  have hfi : Integrable f volume :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (((hu.1.continuousOn.mono hball).integrableOn_compact
        (isCompact_closedBall a r)).mono_set ball_subset_closedBall)
  have hm : m ≠ 0 := by
    rw [show m = ∫ t, scaledKernel n r hr t from rfl, scaledKernel_integral hr]
    exact mul_ne_zero (pow_ne_zero _ hr.ne')
      (MeanValues.radialKernel_integral_pos (n := n) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  filter_upwards [ball_mem_nhds a (half_pos hr)] with y hy
  have hyf : f y = u y := indicator_of_mem
    (ball_subset_ball (half_le_self hr.le) hy) u
  have hmean (s : ℝ) (hs0 : 0 < s) (hsr : s < r / 2) :
      (∫ θ, f (y + s • θ) ∂unitSurface n) = omega n • f y := by
    have hsmall : closedBall y s ⊆ (Ω : Set _) := by
      apply subset_trans _ hball
      apply closedBall_subset_closedBall'
      have hdist : dist y a < r / 2 := hy
      linarith
    have htheta : (∫ θ, f (y + s • θ) ∂unitSurface n) =
        ∫ θ, u (y + s • θ) ∂unitSurface n := by
      apply integral_congr_ae
      filter_upwards [MeanValues.unitSurface_ae_mem n] with θ hθ
      have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
      apply indicator_of_mem
      apply mem_ball.mpr
      calc
        dist (y + s • θ) a ≤ dist (y + s • θ) y + dist y a := dist_triangle _ _ _
        _ < r := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            hθn, mul_one, abs_of_pos hs0]
          have hdist : dist y a < r / 2 := hy
          linarith
    rw [htheta, hyf]
    have hv := (MeanValues.mean_values hn Ω u hu y s hs0 hsmall).1
    rw [MeanValues.sphere_mean_normalization hn u y s hs0] at hv
    calc
      _ = omega n • MeanValues.unitSphereMean u y s := by
        simp only [MeanValues.unitSphereMean, P201Specs.MeanValues.unitSphereMean,
          smul_smul, mul_inv_cancel₀ (MeanValues.omega_pos hn).ne', one_smul]
      _ = _ := congrArg (omega n • ·) hv.symm
  have hv := scaledKernel_convolution_eq hn hfi.locallyIntegrable y hr hmean
  change u y = m⁻¹ • (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip] (K : Space n → ℝ)) y
  rw [← convolution_flip]
  change u y = m⁻¹ • ((K : Space n → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) y
  rw [hv, ← hyf, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- The interior estimate for arbitrary coordinate words. The constant is uniform
in the scalar field as well as the harmonic function and geometric data. -/
theorem interior_word_estimate {n : ℕ} (hn : 1 ≤ n) (l : List (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜),
      MeanValues.IsHarmonic Ω u → ∀ (a : Space n) (r : ℝ), 0 < r →
      closedBall a r ⊆ (Ω : Set _) →
      ‖partialWord u l a‖ ≤ C / r ^ (n + l.length) * ∫ y in ball a r, ‖u y‖ := by
  obtain ⟨B, hBpos, hB⟩ := scaledKernel_derivative_bound l
  let m₀ := ∫ t, baseKernel n t
  have hm₀ : 0 < m₀ := MeanValues.radialKernel_integral_pos (n := n) (by norm_num)
  refine ⟨B / m₀, div_pos hBpos hm₀, ?_⟩
  intro 𝕜 _ Ω u hu a r hr hball
  let f := (ball a r).indicator u
  let K := scaledKernel n r hr
  let m := ∫ t, K t
  let φ : Test ℝ (⊤ : Domain n) := m⁻¹ • K
  have hfi : Integrable f volume :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (((hu.1.continuousOn.mono hball).integrableOn_compact
        (isCompact_closedBall a r)).mono_set ball_subset_closedBall)
  have hm : m = r ^ n * m₀ := scaledKernel_integral hr
  have hmpos : 0 < m := by rw [hm]; exact mul_pos (pow_pos hr n) hm₀
  have heq : u =ᶠ[𝓝 a]
      (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip] (φ : Space n → ℝ)) := by
    simpa only [φ, FunLike.coe_smul, convolution_smul] using
      harmonic_scaledKernel_representation hn Ω u hu a hr hball
  have hder : partialWord u l a =
      (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip] (partialWord φ l)) a := by
    rw [← partialWord_convolution f hfi.locallyIntegrable φ l]
    exact (P102.U4.partialWord_eventuallyEq heq l).eq_of_nhds
  have hφ (x : Space n) : partialWord φ l x = m⁻¹ * partialWord K l x := by
    rw [← P102.U4.testPartialWord_coe]
    change testPartialWord ⊤ l (m⁻¹ • K) x = _
    rw [map_smul]
    change m⁻¹ * testPartialWord ⊤ l K x = _
    rw [P102.U4.testPartialWord_coe]
  have hbound (x : Space n) :
      ‖partialWord φ l x‖ ≤ (B / m₀) / r ^ (n + l.length) := by
    rw [hφ, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmpos)]
    calc
      _ ≤ m⁻¹ * (B / r ^ l.length) := mul_le_mul_of_nonneg_left (hB r hr x) (by positivity)
      _ = _ := by rw [hm, pow_add]; field_simp
  rw [hder, convolution_def]
  change ‖∫ t, partialWord φ l (a - t) • f t‖ ≤ _
  calc
    _ ≤ ∫ t, ((B / m₀) / r ^ (n + l.length)) * ‖f t‖ := by
      apply norm_integral_le_of_norm_le (hfi.norm.const_mul _)
      filter_upwards [] with t
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hbound (a - t)) (norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      have he : (fun t => ‖f t‖) = (ball a r).indicator (fun t => ‖u t‖) := by
        ext t
        by_cases ht : t ∈ ball a r <;> simp [f, ht]
      rw [he, integral_indicator measurableSet_ball]

/-- Proposition `prop:pde-harmonic-derivatives`, quantitative part. -/
theorem interior_derivative_estimate :
    P201Specs.DerivativesLiouville.InteriorDerivativeEstimateStatement := by
  intro n hn α
  obtain ⟨C, hC, hest⟩ := interior_word_estimate hn (α.sort (· ≤ ·))
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ Ω u hu a r hr hball
  simpa only [multiPartial, P201Specs.multiPartial, P102.U4.multiPartial,
    Multiset.length_sort] using hest Ω u hu a r hr hball

end P201.DerivativesLiouville
