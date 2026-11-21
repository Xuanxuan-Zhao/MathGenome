import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.TriangularGraphRegularity
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.LinearGrowth
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.C1Dependence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace D13Unified.Ch16.TriangularGraphRegularity
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Ch06.StateDerivative

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

lemma slow_mem (d : Data E H) (x : E) : x ∈ d.slow.domain := by
  rw [d.full_domain]; trivial

lemma slow_contDiff (d : Data E H) : ContDiff ℝ 1 d.slow.eval := by
  simpa [d.full_domain, contDiffOn_univ, AutonomousODE.eval] using d.slow_c1

/-- Linear growth closes the actual canonical maximal interval in both directions. -/
lemma slow_complete (d : Data E H) (x : E) :
    (flowInterval d.slow x).carrier = univ := by
  have hlip := d.slow.locallyLipschitzInState_of_contDiffOn d.slow_c1
  obtain ⟨hx, h0, hi, hmax, _⟩ := ODE.canonical_solution d.slow.toODE hlip 0 x (slow_mem d x)
  apply Ch04.LinearGrowth.global_existence d.slow.toODE hlip
    (by ext q; change q.2 ∈ d.slow.domain ↔ True; rw [d.full_domain]; simp) _ (⟨_, _, hx⟩ : Solution d.slow.toODE) hmax
  intro T hT
  refine ⟨0, d.L, le_rfl, d.L.coe_nonneg, fun t ht y => ?_⟩
  simpa [AutonomousODE.toODE_eval, AutonomousODE.eval, d.slow_zero] using
    d.slow_lipschitz.norm_sub_le y 0

lemma slow_initial (d : Data E H) (x : E) : slowFlow d 0 x = x :=
  (flow_ivp d.slow d.slow_c1 (slow_mem d x)).2.2

lemma slow_hasDerivAt (d : Data E H) (x : E) (t : ℝ) :
    HasDerivAt (fun r => slowFlow d r x) (d.slow.eval (slowFlow d t x)) t := by
  have ht : t ∈ (flowInterval d.slow x).carrier := by rw [slow_complete d]; trivial
  exact (flow_ivp d.slow d.slow_c1 (slow_mem d x)).1.2.2 t ht

lemma slow_joint_c1 (d : Data E H) :
    ContDiff ℝ 1 (fun q : ℝ × E => slowFlow d q.1 q.2) := by
  have hall : flowDomain d.slow = univ := by
    ext q
    simp [flowDomain, slow_complete d, d.full_domain]
  simpa [hall, contDiffOn_univ, slowFlow] using
    Ch06.C1Dependence.autonomous_joint_c1 d.slow d.slow_c1

lemma slow_continuous (d : Data E H) (x : E) : Continuous (fun t => slowFlow d t x) :=
  (slow_joint_c1 d).continuous.comp (continuous_id.prodMk continuous_const)

lemma slow_difference (d : Data E H) (x y : ℝ → E)
    (hx : Continuous x) (hy : Continuous y)
    (hdx : ∀ t, HasDerivAt x (d.slow.eval (x t)) t)
    (hdy : ∀ t, HasDerivAt y (d.slow.eval (y t)) t) (t : ℝ) :
    ‖x t - y t‖ ≤ Real.exp (d.L * |t|) * ‖x 0 - y 0‖ := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := Ch05.PerturbationResidual.curve_comparison
    (a := min 0 t) (b := max 0 t) (s := 0) (L := d.L) (δ := 0)
    (x := x) (y := y)
    ⟨min_le_left _ _, le_max_left _ _⟩ d.L.coe_nonneg le_rfl
    hx.continuousOn hy.continuousOn
    ((slow_contDiff d).continuous.comp hx).continuousOn
    ((slow_contDiff d).continuous.comp hy).continuousOn
    (fun r hr => (hdx r).hasDerivWithinAt) (fun r hr => (hdy r).hasDerivWithinAt)
    (fun r hr => by simpa [AutonomousODE.eval] using d.slow_lipschitz.norm_sub_le (x r) (y r))
    ⟨min_le_right _ _, le_max_right _ _⟩
  simpa using h

lemma slow_lipschitz (d : Data E H) (t : ℝ) :
    LipschitzWith ⟨Real.exp (d.L * |t|), (Real.exp_pos _).le⟩ (slowFlow d t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := slow_difference d (fun r => slowFlow d r x) (fun r => slowFlow d r y)
    (slow_continuous d x) (slow_continuous d y)
    (slow_hasDerivAt d x) (slow_hasDerivAt d y) t
  simp only [dist_eq_norm]
  simp only [slow_initial] at h
  exact h

lemma slow_derivative_bound (d : Data E H) (t : ℝ) (x : E) :
    ‖fderiv ℝ (slowFlow d t) x‖ ≤ Real.exp (d.L * |t|) :=
  norm_fderiv_le_of_lipschitz ℝ (slow_lipschitz d t)

lemma slow_zero (d : Data E H) (t : ℝ) : slowFlow d t 0 = 0 := by
  have hd (r : ℝ) : HasDerivAt (fun _ : ℝ => (0 : E)) (d.slow.eval 0) r := by
    simpa [AutonomousODE.eval, d.slow_zero] using hasDerivAt_const r (0 : E)
  have h := slow_difference d (fun r => slowFlow d r 0) (fun _ => 0)
    (slow_continuous d 0) continuous_const (slow_hasDerivAt d 0) hd t
  simpa [slow_initial, norm_le_zero_iff] using h

theorem completeness : Specs.D13Unified.Ch16.TriangularGraphRegularity.Completeness.{u,v} := by
  intro E _ _ _ H _ _ _ d
  exact ⟨slow_complete d, slow_initial d, slow_hasDerivAt d, slow_joint_c1 d,
    slow_derivative_bound d, slow_zero d⟩

lemma M_nonneg (d : Data E H) : 0 ≤ d.M := by
  have h : ‖kernel d 0‖ ≤ d.M := by simpa [kernel] using d.decay 0 le_rfl
  exact (norm_nonneg _).trans h

lemma beta_pos (d : Data E H) : 0 < d.β := lt_of_le_of_lt d.L.coe_nonneg d.gap

lemma kernel_continuous (d : Data E H) : Continuous (kernel d) := by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  letI := NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)
  exact NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)

lemma integrand_continuous (d : Data E H) (x : E) : Continuous (integrand d x) := by
  exact (kernel_continuous d).clm_apply
    (d.g_c1.continuous.comp ((slow_continuous d x).comp continuous_neg))

/-- A scalar majorant independent of the initial slow state. -/
def valueBound (d : Data E H) (s : ℝ) : ℝ :=
  d.M * (d.C : ℝ) * Real.exp (-d.β * s)

lemma integrand_bound (d : Data E H) (x : E) (s : ℝ) (hs : 0 ≤ s) :
    ‖integrand d x s‖ ≤ valueBound d s := by
  calc
    ‖integrand d x s‖ ≤ ‖kernel d s‖ * ‖d.g (slowFlow d (-s) x)‖ :=
      (kernel d s).le_opNorm _
    _ ≤ (d.M * Real.exp (-d.β * s)) * d.C :=
      mul_le_mul (d.decay s hs) (d.g_bound _) (norm_nonneg _) (mul_nonneg (M_nonneg d) (Real.exp_pos _).le)
    _ = valueBound d s := by dsimp [valueBound]; ring

lemma valueBound_integrable (d : Data E H) : IntegrableOn (valueBound d) (Ici 0) := by
  exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (beta_pos d)) 0)).const_mul (d.M * d.C)

lemma integrand_integrable (d : Data E H) (x : E) :
    IntegrableOn (integrand d x) (Ici 0) := by
  apply (valueBound_integrable d).mono' ((integrand_continuous d x).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  exact integrand_bound d x s hs

/-- An integrable common majorant bounds all tails, so convergence is uniform
on the entire slow state space. No uniform convergence of the slow flow is used. -/
theorem integral_convergence :
    Specs.D13Unified.Ch16.TriangularGraphRegularity.IntegralConvergence.{u,v} := by
  intro E _ _ _ H _ _ _ d
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  refine ⟨fun x => ⟨integrand_integrable d x, (integrand_integrable d x).norm⟩, ?_⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have htail : Tendsto (fun T : ℝ => ∫ s in Ici T, valueBound d s) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ), (tendsto_order.mp htail).2 ε hε] with T hT hsmall
  intro x
  have hsub : Ici T ⊆ Ici (0 : ℝ) := Ici_subset_Ici.mpr hT
  have hi := intervalIntegral.integral_Ici_sub_Ici'
    (integrand_integrable d x) ((integrand_integrable d x).mono_set hsub)
  rw [dist_eq_norm]
  change ‖(∫ s in Ici (0 : ℝ), integrand d x s) - ∫ s in (0 : ℝ)..T, integrand d x s‖ < ε
  rw [← hi, sub_sub_cancel]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le ((valueBound_integrable d).mono_set hsub) ?_) hsmall
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  exact integrand_bound d x s (hT.trans hs)

lemma slow_variation_continuous (d : Data E H) :
    Continuous (fun q : ℝ × E => fderiv ℝ (slowFlow d q.1) q.2) := by
  have hall : flowDomain d.slow = univ := by
    ext q; simp [flowDomain, slow_complete d, d.full_domain]
  rw [← continuousOn_univ, ← hall]
  exact (maximal_domain_derivative d.slow d.slow_c1).2.1

lemma integrand_hasFDerivAt (d : Data E H) (x : E) (s : ℝ) :
    HasFDerivAt (fun y => integrand d y s) (derivativeIntegrand d x s) x := by
  have hφ : Differentiable ℝ (slowFlow d (-s)) :=
    ((slow_joint_c1 d).comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)
  exact (kernel d s).hasFDerivAt.comp x
    ((d.g_c1.differentiable (by norm_num) _).hasFDerivAt.comp x (hφ x).hasFDerivAt)

lemma derivativeIntegrand_continuous (d : Data E H) :
    Continuous (fun q : ℝ × E => derivativeIntegrand d q.2 q.1) := by
  have hk : Continuous (fun q : ℝ × E => kernel d q.1) := (kernel_continuous d).comp continuous_fst
  have hg : Continuous (fun q : ℝ × E => fderiv ℝ d.g (slowFlow d (-q.1) q.2)) :=
    (d.g_c1.continuous_fderiv (by norm_num)).comp
      ((slow_joint_c1 d).continuous.comp (continuous_fst.neg.prodMk continuous_snd))
  have hφ : Continuous (fun q : ℝ × E => fderiv ℝ (slowFlow d (-q.1)) q.2) :=
    (slow_variation_continuous d).comp (continuous_fst.neg.prodMk continuous_snd)
  exact hk.clm_comp (hg.clm_comp hφ)

lemma derivative_integrand_bound (d : Data E H) (x : E) (s : ℝ) (hs : 0 ≤ s) :
    ‖derivativeIntegrand d x s‖ ≤ derivativeBound d s := by
  have he : Real.exp (-d.β * s) * Real.exp (d.L * s) =
      Real.exp (-(d.β - d.L) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    ‖derivativeIntegrand d x s‖ ≤ ‖kernel d s‖ *
        (‖fderiv ℝ d.g (slowFlow d (-s) x)‖ * ‖fderiv ℝ (slowFlow d (-s)) x‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (d.M * Real.exp (-d.β * s)) * (d.D * Real.exp (d.L * |-s|)) :=
      mul_le_mul (d.decay s hs)
        (mul_le_mul (d.dg_bound _) (slow_derivative_bound d (-s) x)
          (norm_nonneg _) d.D.coe_nonneg)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (M_nonneg d) (Real.exp_pos _).le)
    _ = derivativeBound d s := by
      simp only [abs_neg, abs_of_nonneg hs]
      dsimp [derivativeBound]
      calc
        _ = d.M * d.D * (Real.exp (-d.β * s) * Real.exp (d.L * s)) := by ring
        _ = _ := by rw [he]

lemma derivativeBound_integrable (d : Data E H) :
    IntegrableOn (derivativeBound d) (Ici 0) := by
  exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sub_pos.mpr d.gap)) 0)).const_mul (d.M * d.D)

lemma derivative_integrand_integrable (d : Data E H) (x : E) :
    IntegrableOn (derivativeIntegrand d x) (Ici 0) := by
  have hc : Continuous (derivativeIntegrand d x) :=
    (derivativeIntegrand_continuous d).comp (continuous_id.prodMk continuous_const)
  apply (derivativeBound_integrable d).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  exact derivative_integrand_bound d x s hs

/-- Dominated differentiation uses one neighborhood for all nonnegative times,
and the gap makes the derivative majorant integrable on the half-line. -/
lemma graph_hasFDerivAt (d : Data E H) (x : E) :
    HasFDerivAt (graph d) (graphDerivative d x) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (bound := derivativeBound d) univ_mem
  · exact Eventually.of_forall fun y => (integrand_continuous d y).aestronglyMeasurable
  · exact integrand_integrable d x
  · exact (derivative_integrand_integrable d x).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact fun y hy => derivative_integrand_bound d y s hs
  · exact derivativeBound_integrable d
  · exact Eventually.of_forall fun s y hy => integrand_hasFDerivAt d y s

lemma graphDerivative_continuous (d : Data E H) : Continuous (graphDerivative d) := by
  apply continuous_of_dominated (bound := derivativeBound d)
  · exact fun x => (derivative_integrand_integrable d x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact derivative_integrand_bound d x s hs
  · exact derivativeBound_integrable d
  · exact Eventually.of_forall fun s =>
      ((derivativeIntegrand_continuous d).comp (continuous_const.prodMk continuous_id))

lemma graph_contDiff (d : Data E H) : ContDiff ℝ 1 (graph d) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (graph_hasFDerivAt d x).differentiableAt, ?_⟩
  have heq : fderiv ℝ (graph d) = graphDerivative d :=
    funext fun x => (graph_hasFDerivAt d x).fderiv
  rw [heq]
  exact graphDerivative_continuous d

theorem regularity : Specs.D13Unified.Ch16.TriangularGraphRegularity.Regularity.{u,v} := by
  intro E _ _ _ H _ _ _ d
  exact ⟨derivativeBound_integrable d, derivative_integrand_bound d,
    derivative_integrand_integrable d, graph_hasFDerivAt d,
    graphDerivative_continuous d, graph_contDiff d⟩

lemma graph_zero (d : Data E H) : graph d 0 = 0 := by
  simp [graph, integrand, slow_zero, d.g_zero]

lemma graphDerivative_zero (d : Data E H) : graphDerivative d 0 = 0 := by
  simp [graphDerivative, derivativeIntegrand, slow_zero, d.dg_zero]

theorem at_origin : Specs.D13Unified.Ch16.TriangularGraphRegularity.AtOrigin.{u,v} := by
  intro E _ _ _ H _ _ _ d
  exact ⟨graph_zero d, (graph_hasFDerivAt d 0).fderiv.trans (graphDerivative_zero d)⟩

end D13Unified.Ch16.TriangularGraphRegularity
