import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.JacobiSufficiency
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.SecondVariation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.JacobiCoercivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace VariationalNotes.Classical.JacobiSufficiency

/-- The graph evaluation is jointly continuous in the C¹ curve and time.
The C¹ norm is the shared product sup norm, so both jet evaluations are
continuous without any extra regularity assumption on the curve family. -/
theorem continuous_graphPoint (I : Interval) (m : ℕ) :
    Continuous (fun p : C1Curve I m × I.Points => graphPoint p.1 p.2) := by
  have hs : Continuous (fun p : C1Curve I m × I.Points => p.1.state p.2) := by
    exact continuous_eval.comp
      ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hv : Continuous (fun p : C1Curve I m × I.Points => p.1.velocity p.2) := by
    exact continuous_eval.comp
      ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  exact (continuous_subtype_val.comp continuous_snd).prodMk (hs.prodMk hv)

/-- Compactness makes admissibility uniform over all small C¹ perturbations. -/
theorem graph_add_eventually {I : Interval} {m : ℕ} (u : C1Curve I m)
    {U : Set (ℝ × State m × State m)} (hU : IsOpen U)
    (hu : ∀ t : I.Points, graphPoint u t ∈ U) :
    ∀ᶠ η : C1Curve I m in 𝓝 0, ∀ t : I.Points, graphPoint (u + η) t ∈ U := by
  have hAdd : Continuous (fun η : C1Curve I m => u + η) := by
    apply Continuous.subtype_mk
    exact continuous_const.add continuous_subtype_val
  have hc : Continuous (fun p : C1Curve I m × I.Points => graphPoint (u + p.1) p.2) :=
    (continuous_graphPoint I m).comp ((hAdd.comp continuous_fst).prodMk continuous_snd)
  have he := (isCompact_univ : IsCompact (univ : Set I.Points)).eventually_forall_of_forall_eventually
    (x₀ := (0 : C1Curve I m))
    (P := fun η t => graphPoint (u + η) t ∈ U) (by
      intro t _
      exact hc.continuousAt.eventually (hU.mem_nhds (by simpa using hu t)))
  simpa using he

/-- Uniform oscillation for a continuous family over a compact parameter set. -/
theorem compact_uniform_oscillation {A X D F : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace D] [NormedAddCommGroup F]
    (G : A × X → D) (G₀ : X → D) (H : D → F) (a : A)
    (hG : Continuous G) (hG₀ : Continuous G₀)
    (heq : ∀ x, G (a, x) = G₀ x)
    (hH : ∀ x, ContinuousAt H (G₀ x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v in 𝓝 a, ∀ x, ‖H (G (v, x)) - H (G₀ x)‖ < ε := by
  have hu := (isCompact_univ : IsCompact (univ : Set X)).eventually_forall_of_forall_eventually
    (x₀ := a) (P := fun v x => ‖H (G (v, x)) - H (G₀ x)‖ < ε) (by
      intro x _
      have h₁ : ContinuousAt (fun p : A × X => H (G p)) (a, x) :=
        ((heq x).symm ▸ hH x).comp hG.continuousAt
      have h₂ : ContinuousAt (fun p : A × X => H (G₀ p.2)) (a, x) :=
        (hH x).comp (f := fun p : A × X => G₀ p.2) (x := (a, x))
          (hG₀.comp continuous_snd).continuousAt
      have hc := (h₁.sub h₂).norm
      exact hc.eventually (gt_mem_nhds (by simpa [heq x] using hε)))
  simpa using hu

/-- Uniform Hessian oscillation along the whole compact reference graph.
This is an operator-norm estimate, hence can be applied to arbitrary
state-velocity directions with their squared pointwise norm. -/
theorem hessian_add_eventually {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ η : C1Curve I m in 𝓝 0, ∀ t : I.Points,
      ‖fderiv ℝ (fderiv ℝ L.value) (graphPoint (u + η) t) -
        fderiv ℝ (fderiv ℝ L.value) (graphPoint u t)‖ < ε := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  have hL' : ContDiffOn ℝ 1 (fderiv ℝ L.value) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ L.value)) U :=
    hL'.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hAdd : Continuous (fun η : C1Curve I m => u + η) := by
    apply Continuous.subtype_mk
    exact continuous_const.add continuous_subtype_val
  have hG : Continuous (fun p : C1Curve I m × I.Points => graphPoint (u + p.1) p.2) :=
    (continuous_graphPoint I m).comp ((hAdd.comp continuous_fst).prodMk continuous_snd)
  have hG₀ : Continuous (fun t : I.Points => graphPoint u t) :=
    (continuous_graphPoint I m).comp (continuous_const.prodMk continuous_id)
  convert! compact_uniform_oscillation _ _ (fderiv ℝ (fderiv ℝ L.value))
    (0 : C1Curve I m) hG hG₀ (by intro t; simp)
    (fun t => (hH _ (hu t)).continuousAt (hU.mem_nhds (hu t))) hε using 1

/-- Two applications of the mean value inequality give a second-order
remainder controlled by the oscillation of the second derivative. The
constant is deliberately nonoptimal; it tends to zero with the oscillation. -/
theorem second_order_remainder_bound {f f₁ f₂ : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (h₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ s) s)
    (h₂ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ s) s)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |f₂ s - f₂ 0| ≤ C) :
    |f 1 - f 0 - f₁ 0 - (1 / 2 : ℝ) * f₂ 0| ≤ C := by
  let g₁ : ℝ → ℝ := fun s => f₁ s - f₁ 0 - s * f₂ 0
  have hg₁ : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt g₁ (f₂ s - f₂ 0) (Icc (0 : ℝ) 1) s := by
    intro s hs
    convert! (((h₂ s hs).sub_const (f₁ 0)).sub
      ((hasDerivAt_id s).mul_const (f₂ 0))).hasDerivWithinAt using 1; simp
  have hb₁ : ∀ s ∈ Icc (0 : ℝ) 1, |g₁ s| ≤ C := by
    intro s hs
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hg₁
      (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s (Ico_subset_Icc_self hs)) s hs
    have hmul : C * s ≤ C := mul_le_of_le_one_right hC hs.2
    have h' : |g₁ s| ≤ C * s := by simpa [g₁, Real.norm_eq_abs] using h
    exact h'.trans hmul
  let g : ℝ → ℝ := fun s => f s - f 0 - s * f₁ 0 - s ^ 2 / 2 * f₂ 0
  have hg : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt g (g₁ s) (Icc (0 : ℝ) 1) s := by
    intro s hs
    have hd := (((h₁ s hs).sub_const (f 0)).sub
      ((hasDerivAt_id s).mul_const (f₁ 0))).sub
        ((((hasDerivAt_id s).pow 2).div_const 2).mul_const (f₂ 0))
    convert! hd.hasDerivWithinAt using 1; simp [g₁]
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hg
    (fun s hs => by simpa only [Real.norm_eq_abs] using hb₁ s (Ico_subset_Icc_self hs))
  simpa [g, Real.norm_eq_abs, div_eq_mul_inv, mul_assoc] using h

/-- A uniform bound on Hessian oscillation controls the pointwise Taylor
remainder quadratically in the state-velocity increment. -/
theorem affine_taylor_remainder_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (x d : E) {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (x + s • d))
    (h₂ : ∀ s ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fderiv ℝ f) (x + s • d))
    (hH : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ f) (x + s • d) - fderiv ℝ (fderiv ℝ f) x‖ ≤ ε) :
    |f (x + d) - f x - fderiv ℝ f x d -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x d d| ≤ ε * ‖d‖ ^ 2 := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • d) d s := by
    intro s
    convert! (hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const d) using 1; simp
  have ha := second_order_remainder_bound
    (C := ε * ‖d‖ ^ 2) (f := fun s => f (x + s • d))
    (f₁ := fun s => fderiv ℝ f (x + s • d) d)
    (f₂ := fun s => fderiv ℝ (fderiv ℝ f) (x + s • d) d d)
    (mul_nonneg hε (sq_nonneg _))
    (fun s hs => (h₁ s hs).hasFDerivAt.comp_hasDerivAt s (hp s))
    (fun s hs => by
      simpa using ((h₂ s hs).hasFDerivAt.comp_hasDerivAt s (hp s)).clm_apply
        (hasDerivAt_const s d))
    (by
      intro s hs
      let A := fderiv ℝ (fderiv ℝ f) (x + s • d) - fderiv ℝ (fderiv ℝ f) x
      have he : fderiv ℝ (fderiv ℝ f) (x + s • d) d d -
          fderiv ℝ (fderiv ℝ f) (x + (0 : ℝ) • d) d d = A d d := by
        simp [A]
      rw [he, ← Real.norm_eq_abs]
      calc
        ‖A d d‖ ≤ ‖A d‖ * ‖d‖ := (A d).le_opNorm d
        _ ≤ (‖A‖ * ‖d‖) * ‖d‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm d) (norm_nonneg _)
        _ ≤ (ε * ‖d‖) * ‖d‖ := by
          gcongr
          exact hH s hs
        _ = ε * ‖d‖ ^ 2 := by ring)
  simpa using ha



/-- Uniform pointwise Taylor control on the entire interval. The radius is
independent of both time and the direction; this is stronger than applying
a directional Taylor expansion separately to each variation. -/
theorem uniform_pointwise_taylor {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ η : C1Curve I m, ‖η‖ < ρ → ∀ t : I.Points,
      let d : ℝ × State m × State m := (0, η.state t, η.velocity t)
      |L.value (graphPoint (u + η) t) - L.value (graphPoint u t) -
        fderiv ℝ L.value (graphPoint u t) d -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ L.value) (graphPoint u t) d d| ≤
          ε * ‖d‖ ^ 2 := by
  have hH := hessian_add_eventually L u hreg hε
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  have hG := graph_add_eventually u hU hu
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (hG.and hH)
  refine ⟨ρ, hρ, ?_⟩
  intro η hη t
  let d : ℝ × State m × State m := (0, η.state t, η.velocity t)
  have he : ∀ s : ℝ, graphPoint u t + s • d = graphPoint (u + s • η) t := by
    intro s
    apply Prod.ext
    · simp [graphPoint, d]
    · rfl
  have hsmall : ∀ s ∈ Icc (0 : ℝ) 1, s • η ∈ Metric.ball (0 : C1Curve I m) ρ := by
    intro s hs
    rw [Metric.mem_ball]
    change dist (s • η.val) 0 < ρ
    rw [dist_zero_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hs.2) hη
  have hL' : ContDiffOn ℝ 1 (fderiv ℝ L.value) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  have hbound := affine_taylor_remainder_bound L.value (graphPoint u t) d hε.le
    (by
      intro s hs
      rw [he]
      have hp := (hsub (hsmall s hs)).1 t
      exact (hL.differentiableOn (by norm_num) _ hp).differentiableAt (hU.mem_nhds hp))
    (by
      intro s hs
      rw [he]
      have hp := (hsub (hsmall s hs)).1 t
      exact (hL'.differentiableOn (by norm_num) _ hp).differentiableAt (hU.mem_nhds hp))
    (by
      intro s hs
      rw [he]
      exact ((hsub (hsmall s hs)).2 t).le)
  have he1 : graphPoint u t + d = graphPoint (u + η) t := by
    simpa only [one_smul] using he 1
  rw [he1] at hbound
  exact hbound



/-- The ambient graph uses a maximum norm, which is controlled by the
Euclidean sum of the squares of the two variation fields. -/
theorem direction_norm_sq_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (z : E) (v : F) :
    ‖((0 : ℝ), z, v)‖ ^ 2 ≤ ‖z‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [Prod.norm_def, Prod.norm_def, norm_zero,
    max_eq_right (le_trans (norm_nonneg z) (le_max_left _ _))]
  rcases le_total ‖z‖ ‖v‖ with h | h
  · rw [max_eq_right h]
    linarith [sq_nonneg ‖z‖]
  · rw [max_eq_left h]
    linarith [sq_nonneg ‖v‖]

/-- Uniform Taylor expansion of the actual action. The linear term is kept
explicit, so this lemma needs neither minimality nor stationarity. Its
remainder is controlled by the full classical H¹ energy, with an arbitrarily
small constant on a single C¹ ball. -/
theorem uniform_action_taylor {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ η : C1Curve I m, ‖η‖ < ρ →
      |action L (u + η) - action L u -
          (∫ t in I.a..I.b, fderiv ℝ L.value
            (t, stateField I m u t, velocityField I m u t) (affineGraphDirection η t)) -
          (1 / 2 : ℝ) * secondVariationForm L u η| ≤
        ε * ∫ t in I.a..I.b,
          ‖stateField I m η t‖ ^ 2 + ‖velocityField I m η t‖ ^ 2 := by
  obtain ⟨ρ₁, hρ₁, hpoint⟩ := uniform_pointwise_taylor L u hreg hε
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.mem_nhds_iff.mp (graph_add_eventually u hU hu)
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro η hη
  have hsmall : η ∈ Metric.ball (0 : C1Curve I m) ρ₂ := by
    rw [Metric.mem_ball]
    change dist η.val 0 < ρ₂
    rw [dist_zero_right]
    exact lt_of_lt_of_le hη (min_le_right _ _)
  have hpert := hsub hsmall
  let X : ℝ → ℝ × State m × State m :=
    fun t => (t, stateField I m u t, velocityField I m u t)
  let W : ℝ → ℝ × State m × State m := affineGraphDirection η
  let A : ℝ → ℝ := fun t => L.value (t, stateField I m (u + η) t,
    velocityField I m (u + η) t)
  let B : ℝ → ℝ := fun t => L.value (X t)
  let D : ℝ → ℝ := fun t => fderiv ℝ L.value (X t) (W t)
  let H : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ L.value) (X t) (W t) (W t)
  let N : ℝ → ℝ := fun t => ‖stateField I m η t‖ ^ 2 + ‖velocityField I m η t‖ ^ 2
  have hx : ContinuousOn X (Icc I.a I.b) := graphField_continuousOn I m u
  have hw : ContinuousOn W (Icc I.a I.b) :=
    continuousOn_const.prodMk ((stateField_continuousOn I m η).prodMk
      (velocityField_continuousOn I m η))
  have hmaps : MapsTo X (Icc I.a I.b) U := by
    intro t ht
    simpa only [X, graphPoint, stateField, velocityField, extendState, dite_eq_left ht] using hu ⟨t, ht⟩
  have hmapsp : MapsTo (fun t => (t, stateField I m (u + η) t,
      velocityField I m (u + η) t)) (Icc I.a I.b) U := by
    intro t ht
    simpa only [graphPoint, stateField, velocityField, extendState, dite_eq_left ht] using hpert ⟨t, ht⟩
  have ha : ContinuousOn A (Icc I.a I.b) :=
    hL.continuousOn.comp (graphField_continuousOn I m (u + η)) hmapsp
  have hb : ContinuousOn B (Icc I.a I.b) := hL.continuousOn.comp hx hmaps
  have hL' : ContDiffOn ℝ 1 (fderiv ℝ L.value) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  have hd : ContinuousOn D (Icc I.a I.b) :=
    ((hL.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp hx hmaps).clm_apply hw
  have hh : ContinuousOn H (Icc I.a I.b) :=
    (((hL'.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp hx hmaps).clm_apply hw).clm_apply hw
  have hn : ContinuousOn N (Icc I.a I.b) :=
    ((stateField_continuousOn I m η).norm.pow 2).add
      ((velocityField_continuousOn I m η).norm.pow 2)
  have hiA : IntervalIntegrable A volume I.a I.b := ha.intervalIntegrable_of_Icc I.increasing.le
  have hiB : IntervalIntegrable B volume I.a I.b := hb.intervalIntegrable_of_Icc I.increasing.le
  have hiD : IntervalIntegrable D volume I.a I.b := hd.intervalIntegrable_of_Icc I.increasing.le
  have hiH : IntervalIntegrable H volume I.a I.b := hh.intervalIntegrable_of_Icc I.increasing.le
  have hq : (∫ t in I.a..I.b, H t) = secondVariationForm L u η := by
    unfold secondVariationForm
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    have hc := (hL _ (hu ⟨t, ht⟩)).contDiffAt (hU.mem_nhds (hu ⟨t, ht⟩))
    have he := hessian_direction_eq_blocks L (graphPoint u ⟨t, ht⟩)
      (η.state ⟨t, ht⟩) (η.velocity ⟨t, ht⟩) (hc.isSymmSndFDerivAt (by norm_num))
    simpa only [H, X, W, affineGraphDirection, graphPoint, stateField, velocityField,
      extendState, dite_eq_left ht] using he
  have hbound : ∀ t ∈ Icc I.a I.b,
      ‖A t - B t - D t - (1 / 2 : ℝ) * H t‖ ≤ ε * N t := by
    intro t ht
    have hp := hpoint η (lt_of_lt_of_le hη (min_le_left _ _)) ⟨t, ht⟩
    have hnorm := direction_norm_sq_le (η.state ⟨t, ht⟩) (η.velocity ⟨t, ht⟩)
    have h := hp.trans (mul_le_mul_of_nonneg_left hnorm hε.le)
    simpa only [A, B, D, H, X, W, N, affineGraphDirection, graphPoint, stateField,
      velocityField, extendState, dite_eq_left ht, Real.norm_eq_abs] using h
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) I.increasing.le
    (f := fun t => A t - B t - D t - (1 / 2 : ℝ) * H t)
    (g := fun t => ε * N t)
    (Eventually.of_forall (fun t ht => hbound t (Ioc_subset_Icc_self ht)))
    ((hn.const_mul ε).intervalIntegrable_of_Icc I.increasing.le)
  rw [intervalIntegral.integral_sub ((hiA.sub hiB).sub hiD) (hiH.const_mul (1 / 2)),
    intervalIntegral.integral_sub (hiA.sub hiB) hiD,
    intervalIntegral.integral_sub hiA hiB,
    intervalIntegral.integral_const_mul, hq, intervalIntegral.integral_const_mul] at hi
  exact hi



/-- Interior-test stationarity gives the distributional Euler–Lagrange
identity without assuming that u is already a minimum. -/
theorem stationary_weakDerivative {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1)
    (hstat : stateStationary L u) :
    WeakDerivativeInterval m I.a I.b (momentumField L u) (stateGradientField L u) := by
  intro φ hφ hc hs
  let η : C1Curve I m := interiorTestCurve φ hφ
  have hzero : HasDerivAt (fun s : ℝ => action L (u + s • η)) 0 0 := by
    convert! hstat φ ⟨hφ, hc, hs⟩ using 1
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    simp only [stateField, velocityField, extendState, dite_eq_left ht,
      η, interiorTestCurve, C1Curve.state, C1Curve.velocity]
    rfl
  have hd := classicalActionDerivative I m L u η hreg
  have hid := hd.unique hzero
  rw [intervalIntegral.integral_of_le I.increasing.le, integral_Ioc_eq_integral_Ioo] at hid
  have heq : (∫ t in Ioo I.a I.b,
      inner ℝ (momentumField L u t) (deriv φ t) + inner ℝ (stateGradientField L u t) (φ t)) =
      ∫ t in Ioo I.a I.b, variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only [variationDensity, stateField, velocityField, extendState,
      dite_eq_left (Ioo_subset_Icc_self ht), η, interiorTestCurve,
      C1Curve.state, C1Curve.velocity]
    exact add_comm _ _
  exact heq.trans hid

/-- The first variation vanishes for every endpoint-zero C¹ variation.
This proves the bridge from the source's interior-test definition of
stationarity; it is not an extra hypothesis in the sufficient condition. -/
theorem stationary_endpoint_variation {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1)
    (hstat : stateStationary L u) (η : C1Curve I m) (hη : η ∈ endpointZero I m) :
    (∫ t in I.a..I.b, variationDensity (momentumField L u) (stateGradientField L u)
      (stateField I m η) (velocityField I m η) t) = 0 := by
  have hw := stationary_weakDerivative L u hreg hstat
  obtain ⟨hp, hq⟩ := gradientFields_continuousOn L u hreg
  have hpc := hp.mono Ioo_subset_Icc_self
  have hqc := hq.mono Ioo_subset_Icc_self
  have hel := distributionalPrimitiveContinuous m I.a I.b I.increasing
    (momentumField L u) (stateGradientField L u)
    (hpc.locallyIntegrableOn measurableSet_Ioo) (hqc.locallyIntegrableOn measurableSet_Ioo)
    hw hpc hqc
  have hcont : ContinuousOn (fun t => inner ℝ (momentumField L u t) (stateField I m η t))
      (Icc I.a I.b) := hp.inner (stateField_continuousOn I m η)
  have hint : IntervalIntegrable
      (variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η)) volume I.a I.b :=
    ((hq.inner (stateField_continuousOn I m η)).add
      (hp.inner (velocityField_continuousOn I m η))).intervalIntegrable_of_Icc I.increasing.le
  have hder : ∀ t ∈ Ioo I.a I.b,
      HasDerivAt (fun t => inner ℝ (momentumField L u t) (stateField I m η t))
        (variationDensity (momentumField L u) (stateGradientField L u)
          (stateField I m η) (velocityField I m η) t) t := by
    intro t ht
    have hηd := (VariationSpaces.curve_derivative I m η ⟨t, Ioo_subset_Icc_self ht⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    have h := (hel.2 t ht).inner ℝ hηd
    convert! h using 1
    simp only [variationDensity, velocityField, extendState, dite_eq_left (Ioo_subset_Icc_self ht)]
    exact add_comm _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le I.increasing.le hcont hder hint]
  have ha : stateField I m η I.a = 0 := by
    convert! hη.1 using 1
    simp only [stateField, extendState, dite_eq_left (show I.a ∈ Icc I.a I.b from
      ⟨le_rfl, I.increasing.le⟩)]
    rfl
  have hb : stateField I m η I.b = 0 := by
    convert! hη.2 using 1
    simp only [stateField, extendState, dite_eq_left (show I.b ∈ Icc I.a I.b from
      ⟨I.increasing.le, le_rfl⟩)]
    rfl
  rw [ha, hb]
  simp



/-- At a stationary curve the uniform expansion has zero linear term for
all endpoint-zero C¹ variations. The remainder is small relative to the
full H¹ energy, not merely relative to the C¹ norm. -/
theorem stationary_uniform_action_taylor {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 2)
    (hstat : stateStationary L u) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ η : C1Curve I m, η ∈ endpointZero I m → ‖η‖ < ρ →
      |action L (u + η) - action L u - (1 / 2 : ℝ) * secondVariationForm L u η| ≤
        ε * ∫ t in I.a..I.b,
          ‖stateField I m η t‖ ^ 2 + ‖velocityField I m η t‖ ^ 2 := by
  obtain ⟨ρ, hρ, hTaylor⟩ := uniform_action_taylor L u hreg hε
  refine ⟨ρ, hρ, ?_⟩
  intro η hη hsmall
  have hreg₁ : regularNearGraph L u 1 := by
    obtain ⟨U, hU, hu, hsub, hL⟩ := hreg
    exact ⟨U, hU, hu, hsub, hL.of_le (by norm_num)⟩
  have hd := classicalActionDerivative I m L u η hreg₁
  rw [stationary_endpoint_variation L u hreg₁ hstat η hη] at hd
  have he := (action_hasDerivAt_total L u η hreg₁).unique hd
  have hlin : (∫ t in I.a..I.b, fderiv ℝ L.value
      (t, stateField I m u t, velocityField I m u t) (affineGraphDirection η t)) = 0 := by
    simpa only [affineGraphField, zero_smul, add_zero] using he
  simpa only [hlin, sub_zero] using hTaylor η hsmall



/-- The full H¹ energy of a classical variation, before its identification
with an equivalence class in the shared weak-derivative graph. -/
def classicalH1Energy {I : Interval} {m : ℕ} (η : C1Curve I m) : ℝ :=
  ∫ t in I.a..I.b, ‖stateField I m η t‖ ^ 2 + ‖velocityField I m η t‖ ^ 2

theorem classicalH1Energy_pos {I : Interval} {m : ℕ} (η : C1Curve I m)
    (hη : η ≠ 0) : 0 < classicalH1Energy η := by
  have hex : ∃ t : I.Points, η.state t ≠ 0 ∨ η.velocity t ≠ 0 := by
    by_contra h
    push Not at h
    apply hη
    apply Subtype.ext
    apply Prod.ext
    · apply ContinuousMap.ext
      intro t
      exact (h t).1
    · apply ContinuousMap.ext
      intro t
      exact (h t).2
  apply intervalIntegral.integral_pos I.increasing
    (((stateField_continuousOn I m η).norm.pow 2).add
      ((velocityField_continuousOn I m η).norm.pow 2))
    (fun t _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, t.property, ?_⟩
  have htmem : (t : ℝ) ∈ Icc I.a I.b := t.property
  simp only [Pi.add_apply, Pi.pow_apply, stateField, velocityField, extendState]
  rw [dite_eq_left htmem, dite_eq_left htmem]
  rcases ht with ht | ht
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr ht)) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr ht))

/-- Absorption of the uniform Taylor remainder. This lemma isolates the
analytic sufficiency step; the coercive lower bound supplied to it must
still be proved from the Jacobi hypotheses in the main theorem. -/
theorem classical_growth_of_coercivity {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 2)
    (hstat : stateStationary L u) {κ : ℝ} (hκ : 0 < κ)
    (hQ : ∀ η : C1Curve I m, η ∈ endpointZero I m →
      κ * classicalH1Energy η ≤ secondVariationForm L u η) :
    ∃ ρ > 0, ∀ η : C1Curve I m, η ∈ endpointZero I m → ‖η‖ < ρ →
      action L u + (κ / 4) * classicalH1Energy η ≤ action L (u + η) := by
  obtain ⟨ρ, hρ, hTaylor⟩ := stationary_uniform_action_taylor L u hreg hstat
    (ε := κ / 4) (by positivity)
  refine ⟨ρ, hρ, ?_⟩
  intro η hη hsmall
  have hrem := (abs_le.mp (hTaylor η hη hsmall)).1
  have hcoer := hQ η hη
  change -(κ / 4 * classicalH1Energy η) ≤ _ at hrem
  nlinarith

/-- Strict weak minimality follows once the classical full-H¹ coercivity
bound is available. All endpoint and admissibility conditions are the
shared ones, and the radius is a C¹ radius. -/
theorem strict_minimum_of_classical_coercivity {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1) (hreg : regularNearGraph L u 2)
    (hstat : stateStationary L u) {κ : ℝ} (hκ : 0 < κ)
    (hQ : ∀ η : C1Curve I 1, η ∈ endpointZero I 1 →
      κ * classicalH1Energy η ≤ secondVariationForm L u η) :
    StrictWeakLocalMinimum L u := by
  obtain ⟨ρ, hρ, hgrowth⟩ := classical_growth_of_coercivity L u hreg hstat hκ hQ
  refine ⟨⟨?_, rfl, rfl⟩, ρ, hρ, ?_⟩
  · obtain ⟨U, _, hu, hsub, _⟩ := hreg
    exact fun t => hsub (hu t)
  · intro v hv hdist hne
    have hη : v - u ∈ endpointZero I 1 := by
      constructor
      · change v.state I.left - u.state I.left = 0
        exact sub_eq_zero.mpr hv.2.1
      · change v.state I.right - u.state I.right = 0
        exact sub_eq_zero.mpr hv.2.2
    have hηne : v - u ≠ 0 := sub_ne_zero.mpr hne
    have h := hgrowth (v - u) hη hdist
    have hpos := mul_pos (show 0 < κ / 4 by positivity) (classicalH1Energy_pos (v - u) hηne)
    have he : u + (v - u) = v := by abel
    rw [he] at h
    linarith

/-- The full norm of any Sobolev representative is the classical energy
used in the uniform Taylor estimate. -/
theorem classicalH1Energy_eq_norm_sq {I : Interval} (η : C1Curve I 1)
    (h : JacobiCoercivity.Variation I) (hrep : JacobiCoercivity.Represents η h) :
    classicalH1Energy η = ‖h‖ ^ 2 := by
  rw [JacobiCoercivity.full_norm_sq_of_represents η h hrep]
  unfold classicalH1Energy
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [JacobiCoercivity.scalar_norm_sq, JacobiCoercivity.scalar_norm_sq]

/-- Absorb the uniform remainder into the full Sobolev coercive bound.
The representation and its norm are those of the preceding theorem. -/
theorem sufficiency_of_coercivity {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1) (hreg : regularNearGraph L u 2)
    (hstat : stateStationary L u) (hcoer : CoercivityAt L u) :
    QuadraticGrowth L u ∧ StrictWeakLocalMinimum L u := by
  obtain ⟨_, hrep, κ, hκ, hbound⟩ := hcoer
  have hQ : ∀ η : C1Curve I 1, η ∈ endpointZero I 1 →
      κ * classicalH1Energy η ≤ secondVariationForm L u η := by
    intro η hη
    obtain ⟨h, hh, hform⟩ := hrep η hη
    rw [classicalH1Energy_eq_norm_sq η h hh, ← hform]
    exact hbound h
  refine ⟨?_, strict_minimum_of_classical_coercivity L u hreg hstat hκ hQ⟩
  obtain ⟨ρ, hρ, hgrowth⟩ := classical_growth_of_coercivity L u hreg hstat hκ hQ
  refine ⟨κ / 4, by positivity, ρ, hρ, ?_⟩
  intro η hη hsmall _hadmissible
  obtain ⟨h, hh, _⟩ := hrep η hη
  refine ⟨h, hh, ?_⟩
  rw [← classicalH1Energy_eq_norm_sq η h hh]
  exact hgrowth η hη hsmall

/-- The complete strengthened Legendre–Jacobi sufficient condition,
including coercivity on every H¹₀ class, quantitative C¹-local growth,
and strict weak minimality in the fixed-endpoint admissible class. -/
theorem jacobi_sufficiency :
    Specs.VariationalNotes.Classical.JacobiSufficiency.CompleteSufficientCondition := by
  intro I L u hu hstat hreg hp Y₀ hY₀ hinit hnz
  have hcoer : CoercivityAt L u :=
    JacobiCoercivity.coercive_secondVariation I L u hu hstat hreg hp Y₀ hY₀ hinit hnz
  have hreg₂ : regularNearGraph L u 2 := by
    obtain ⟨U, hU, hgraph, hsub, hL⟩ := hreg
    exact ⟨U, hU, hgraph, hsub, hL.of_le (by norm_num)⟩
  exact ⟨hcoer, sufficiency_of_coercivity L u hreg₂ hstat hcoer⟩

end VariationalNotes.Classical.JacobiSufficiency
