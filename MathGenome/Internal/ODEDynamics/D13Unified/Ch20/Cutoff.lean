import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Cutoff
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.LinearGrowth
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open Set Filter Metric
open scoped Topology NNReal ContDiff

namespace D13Unified.Ch20.Cutoff
open Specs.D13Unified.Ch20.Cutoff
universe u

theorem controlled_derivatives : controlledDerivativesExpected.{u} := by
  intro E _ _ k r hr hc j hj
  have hj' : (j : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hj
  have hcont := hr.continuous_iteratedFDeriv hj'
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hc.iteratedFDeriv j)
  exact ⟨⟨max 0 C, le_max_left _ _, fun x => (hC x).trans (le_max_right _ _)⟩,
    (hc.iteratedFDeriv j).uniformContinuous_of_continuous hcont⟩

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Localizing a flat germ preserves its regularity and makes its global
Lipschitz constant arbitrarily small. No regularity outside `U` is used. -/
lemma localize_flat (U : Set E) (g : E → E) (k : ℕ∞)
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hk : 1 ≤ k)
    (hg : ContDiffOn ℝ k g U) (hg0 : g 0 = 0)
    (hd0 : HasFDerivAt g (0 : E →L[ℝ] E) 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : E → E, ContDiff ℝ k r ∧ HasCompactSupport r ∧
      r 0 = 0 ∧ HasFDerivAt r (0 : E →L[ℝ] E) 0 ∧
      (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) ∧
      ∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ U ∧ EqOn r g V := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hχdiff : ContDiff ℝ 1 (χ : E → ℝ) := χ.contDiff
  obtain ⟨C, hC⟩ := hχdiff.continuous_fderiv (by norm_num) |>.bounded_above_of_compact_support
    (χ.hasCompactSupport.fderiv ℝ)
  let K : ℝ≥0 := ⟨max 0 C, le_max_left _ _⟩
  have hχlip : LipschitzWith K (χ : E → ℝ) :=
    lipschitzWith_of_nnnorm_fderiv_le (hχdiff.differentiable (by norm_num))
      (fun x => by exact_mod_cast (hC x).trans (le_max_right 0 C))
  let ε : ℝ := δ / (1 + 3 * (K : ℝ))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hk' : (1 : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hk
  have hdcont : ContinuousAt (fderiv ℝ g) 0 :=
    (hg.contDiffAt (hU.mem_nhds h0)).continuousAt_fderiv (ne_of_gt (lt_of_lt_of_le zero_lt_one hk'))
  have hdsmall : ∀ᶠ x in 𝓝 (0 : E), ‖fderiv ℝ g x‖ < ε := by
    have := hdcont.norm.tendsto.eventually (gt_mem_nhds (show ‖fderiv ℝ g 0‖ < ε by
      rw [hd0.fderiv, norm_zero]; exact hε))
    exact this
  obtain ⟨a, ha, hasmall⟩ := Metric.eventually_nhds_iff.mp
    (hdsmall.and (hU.mem_nhds h0))
  let ρ := a / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hball : ball (0 : E) (3 * ρ) ⊆ U := by
    intro x hx
    exact (hasmall (by
      rw [mem_ball, dist_zero_right] at hx
      rw [dist_zero_right]
      dsimp [ρ] at hx
      linarith)).2
  have hgdiff : ∀ x ∈ ball (0 : E) (3 * ρ), DifferentiableAt ℝ g x := by
    intro x hx
    exact (hg.contDiffAt (hU.mem_nhds (hball hx))).differentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one hk'))
  have hdbound : ∀ x ∈ ball (0 : E) (3 * ρ), ‖fderiv ℝ g x‖ ≤ ε := by
    intro x hx
    exact (hasmall (by
      rw [mem_ball, dist_zero_right] at hx
      rw [dist_zero_right]
      dsimp [ρ] at hx
      linarith)).1.le
  have hgbound : ∀ x ∈ ball (0 : E) (3 * ρ), ‖g x‖ ≤ ε * ‖x‖ := by
    intro x hx
    have := (convex_ball (0 : E) (3 * ρ)).norm_image_sub_le_of_norm_fderiv_le
      hgdiff hdbound (mem_ball_self (by positivity)) hx
    simpa only [hg0, sub_zero] using this
  let ψ : ContDiffBump (0 : E) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  have hψscale : (ψ : E → ℝ) = fun x => χ (ρ⁻¹ • x) := by
    funext x
    simp [ContDiffBump.apply, ψ, χ, hρ.ne']
  have hψlip : LipschitzWith (K * ‖ρ⁻¹‖₊) (ψ : E → ℝ) := by
    rw [hψscale]
    exact hχlip.comp (lipschitzWith_smul (ρ⁻¹))
  have hψderiv : ∀ x, ‖fderiv ℝ (ψ : E → ℝ) x‖ ≤ (K : ℝ) / ρ := by
    intro x
    have := norm_fderiv_le_of_lipschitz ℝ hψlip (x₀ := x)
    simpa only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_inv,
      abs_of_pos hρ, div_eq_mul_inv] using this
  let r : E → E := fun x => ψ x • g x
  have hsupport : tsupport r ⊆ closedBall (0 : E) (2 * ρ) := by
    exact (tsupport_smul_subset_left (ψ : E → ℝ) g).trans (by rw [ψ.tsupport_eq])
  have houtside : ∀ x ∉ ball (0 : E) (3 * ρ), r =ᶠ[𝓝 x] 0 := by
    intro x hx
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    exact hx (closedBall_subset_ball (by linarith [hρ]) (hsupport h))
  have hr : ContDiff ℝ k r := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (0 : E) (3 * ρ)
    · exact ψ.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hball hx)))
    · exact contDiffAt_const.congr_of_eventuallyEq (houtside x hx)
  have hrd : Differentiable ℝ r := hr.differentiable (ne_of_gt (lt_of_lt_of_le zero_lt_one hk'))
  have hrbound : ∀ x, ‖fderiv ℝ r x‖ ≤ δ := by
    intro x
    by_cases hx : x ∈ ball (0 : E) (3 * ρ)
    · have hψd : DifferentiableAt ℝ (ψ : E → ℝ) x :=
        (ψ.contDiff (n := 1)).differentiable_one x
      rw [fderiv_fun_smul hψd (hgdiff x hx)]
      calc
        _ ≤ ‖ψ x • fderiv ℝ g x‖ + ‖(fderiv ℝ (ψ : E → ℝ) x).smulRight (g x)‖ :=
          norm_add_le _ _
        _ = |ψ x| * ‖fderiv ℝ g x‖ + ‖fderiv ℝ (ψ : E → ℝ) x‖ * ‖g x‖ := by
          rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
        _ ≤ 1 * ε + ((K : ℝ) / ρ) * (ε * (3 * ρ)) := by
          gcongr
          · rw [abs_of_nonneg ψ.nonneg]; exact ψ.le_one
          · exact hdbound x hx
          · exact hψderiv x
          · exact (hgbound x hx).trans (mul_le_mul_of_nonneg_left
              (by simpa only [mem_ball, dist_zero_right] using (mem_ball.mp hx).le) hε.le)
        _ = δ := by dsimp [ε]; field_simp
    · rw [(houtside x hx).fderiv_eq]
      simpa using hδ.le
  have hrlip : LipschitzWith ⟨δ, hδ.le⟩ r :=
    lipschitzWith_of_nnnorm_fderiv_le hrd (fun x => by exact_mod_cast hrbound x)
  have heq : r =ᶠ[𝓝 (0 : E)] g := by
    filter_upwards [ψ.eventuallyEq_one] with x hx
    dsimp [r]; rw [hx]; exact one_smul ℝ (g x)
  refine ⟨r, hr, ψ.hasCompactSupport.smul_right, (heq.eq_of_nhds).trans hg0,
    hd0.congr_of_eventuallyEq heq, hrlip.norm_sub_le, ball 0 ρ,
    isOpen_ball, mem_ball_self hρ, ?_, ?_⟩
  · exact (ball_subset_ball (by nlinarith [hρ])).trans hball
  · intro x hx
    dsimp [r]
    rw [ψ.one_of_mem_closedBall (mem_closedBall.mpr (le_of_lt hx))]
    exact one_smul ℝ (g x)

/-- A globally Lipschitz autonomous field has solutions for both signs of
time, by the accepted maximal-existence and linear-growth results. -/
lemma global_trajectories (v : E → E) (K : ℝ≥0) (hv : LipschitzWith K v) :
    ∀ ξ : E, ∃ x : ℝ → E, x 0 = ξ ∧ ∀ t, HasDerivAt x (v (x t)) t := by
  let F : ODE E := {
    domain := univ
    isOpen_domain := isOpen_univ
    field := fun p => v p.val.2
    continuous_field := hv.continuous.comp (continuous_snd.comp continuous_subtype_val) }
  have heval (t : ℝ) (x : E) : F.eval t x = v x := by
    simp [ODE.eval, F]
  have hF : Specs.D13Unified.Ch03.LocalLipschitz.locallyLipschitzInStateValue F := by
    intro s ξ _
    refine ⟨1, 1, K, zero_lt_one, zero_lt_one, K.coe_nonneg, subset_univ _, ?_⟩
    intro t _ x _ y _
    simpa only [heval] using hv.norm_sub_le x y
  have hgrowth : ∀ B : ℝ, 0 < B → ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ t : ℝ, |t| ≤ B → ∀ x : E, ‖F.eval t x‖ ≤ a + b * ‖x‖ := by
    intro B _
    refine ⟨‖v 0‖, K, norm_nonneg _, K.coe_nonneg, ?_⟩
    intro t _ x
    rw [heval]
    calc
      ‖v x‖ ≤ ‖v 0‖ + ‖v x - v 0‖ := by
        simpa only [add_sub_cancel] using norm_add_le (v 0) (v x - v 0)
      _ ≤ ‖v 0‖ + (K : ℝ) * ‖x‖ :=
        add_le_add_right (by simpa only [sub_zero] using hv.norm_sub_le x 0) _
  intro ξ
  obtain ⟨x, _, hx0, hmax, _⟩ :=
    Ch04.MaximalSolution.maximal_solution F hF 0 ξ (mem_univ _)
  have hglobal := Ch04.LinearGrowth.global_existence F hF rfl hgrowth x hmax
  refine ⟨x.representative, hx0, fun t => ?_⟩
  simpa only [heval] using x.isSolution.2.2 t (by rw [hglobal]; trivial)

/-- Joint continuity follows from the exponential bound on the distance
between trajectories; the construction does not assume a solution map. -/
theorem complete_flow : completeFlowExpected.{u} := by
  intro E _ _ _ v K hv
  choose φ hφ0 hφderiv using global_trajectories v K hv
  have hφcont (x : E) : Continuous (φ x) :=
    continuous_iff_continuousAt.mpr (fun t => (hφderiv x t).continuousAt)
  have hdistpos (x y : E) {t : ℝ} (ht : 0 ≤ t) :
      dist (φ x t) (φ y t) ≤ dist x y * Real.exp ((K : ℝ) * t) := by
    simpa only [hφ0, sub_zero] using dist_le_of_trajectories_ODE
      (fun _ => hv) (hφcont x).continuousOn
      (fun s _ => (hφderiv x s).hasDerivWithinAt)
      (hφcont y).continuousOn (fun s _ => (hφderiv y s).hasDerivWithinAt)
      (by simp only [hφ0, le_refl]) t ⟨ht, le_rfl⟩
  have hrev (x : E) (t : ℝ) : HasDerivAt (fun s => φ x (-s))
      (-v (φ x (-t))) t := by
    simpa only [Function.comp_def, neg_one_smul] using
      (hφderiv x (-t)).scomp t (hasDerivAt_neg t)
  have hdist (x y : E) (t : ℝ) :
      dist (φ x t) (φ y t) ≤ dist x y * Real.exp ((K : ℝ) * |t|) := by
    rcases le_total 0 t with ht | ht
    · simpa only [abs_of_nonneg ht] using hdistpos x y ht
    · have h := dist_le_of_trajectories_ODE (v := fun _ z => -v z)
        (a := 0) (δ := dist x y)
        (fun _ => hv.neg) ((hφcont x).comp continuous_neg).continuousOn
        (fun s _ => (hrev x s).hasDerivWithinAt)
        ((hφcont y).comp continuous_neg).continuousOn
        (fun s _ => (hrev y s).hasDerivWithinAt)
        (by simp only [Function.comp_def, neg_zero, hφ0, le_refl]) (-t) ⟨neg_nonneg.mpr ht, le_rfl⟩
      simpa only [Function.comp_def, neg_neg, sub_zero, abs_of_nonpos ht] using h
  refine ⟨fun t x => φ x t, ?_, hφ0, ?_, hφderiv⟩
  · apply continuous_iff_continuousAt.mpr
    rintro ⟨t, x⟩
    have hbound : ∀ p : ℝ × E,
        ‖φ p.2 p.1 - φ x p.1‖ ≤ dist p.2 x * Real.exp ((K : ℝ) * |p.1|) := by
      intro p
      simpa only [dist_eq_norm] using hdist p.2 x p.1
    have hlim : Tendsto (fun p : ℝ × E => ‖φ p.2 p.1 - φ x p.1‖)
        (𝓝 (t, x)) (𝓝 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _) hbound
      convert (show Continuous (fun p : ℝ × E =>
        dist p.2 x * Real.exp ((K : ℝ) * |p.1|)) by fun_prop).continuousAt.tendsto using 1
      simp
    have hsmall := tendsto_zero_iff_norm_tendsto_zero.mpr hlim
    have hlarge : Tendsto (fun p : ℝ × E => φ x p.1)
        (𝓝 (t, x)) (𝓝 (φ x t)) :=
      ((hφcont x).comp continuous_fst).continuousAt.tendsto
    change Tendsto (fun p : ℝ × E => φ p.2 p.1) (𝓝 (t, x)) (𝓝 (φ x t))
    simpa only [sub_add_cancel, zero_add] using hsmall.add hlarge
  · intro t s x
    have hshift (τ : ℝ) : HasDerivAt (fun a => φ x (a + s)) (v (φ x (τ + s))) τ := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hφderiv x (τ + s)).scomp τ ((hasDerivAt_id τ).add_const s)
    have heq := ODE_solution_unique_univ (v := fun _ => v) (s := fun _ => univ)
      (fun _ => hv.lipschitzOnWith)
      (fun τ => ⟨hshift τ, mem_univ _⟩)
      (fun τ => ⟨hφderiv (φ x s) τ, mem_univ _⟩)
      (t₀ := 0) (by simp only [zero_add, hφ0])
    exact congrFun heq t

theorem cutoff : cutoffExpected.{u} := by
  intro E _ _ _ U f A k hU h0 hk hf hf0 hA δ hδ
  let g : E → E := fun x => f x - A x
  have hg : ContDiffOn ℝ k g U := hf.sub A.contDiff.contDiffOn
  have hg0 : g 0 = 0 := by simp [g, hf0]
  have hdg0 : HasFDerivAt g (0 : E →L[ℝ] E) 0 := by
    simpa only [g, sub_self] using hA.fun_sub (A.hasFDerivAt (x := 0))
  obtain ⟨r, hr, hrc, hr0, hdr0, hrlip, V, hV, hV0, hVU, heq⟩ :=
    localize_flat U g k hU h0 hk hg hg0 hdg0 δ hδ
  have hrlip' : LipschitzWith ⟨δ, hδ.le⟩ r :=
    lipschitzWith_iff_norm_sub_le.mpr hrlip
  refine ⟨r, hr, hrc, hr0, hdr0, hrlip, ⟨V, hV, hV0, hVU, ?_⟩,
    controlled_derivatives k r hr hrc, ?_⟩
  · intro x hx
    rw [heq hx]
    dsimp [g]; abel
  · exact complete_flow _ _ (A.lipschitzWith.add hrlip')

end D13Unified.Ch20.Cutoff
