import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.TriangularCenter
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.TriangularGraphRegularity
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.InvariantGraph
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace D13Unified.Ch16.TriangularCenter
open TriangularGraphRegularity
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

lemma slow_add (d : Data E H) (s t : ℝ) (x : E) :
    slowFlow d s (slowFlow d t x) = slowFlow d (s + t) x := by
  have h := slow_difference d (fun r => slowFlow d r (slowFlow d t x))
    (fun r => slowFlow d (r + t) x) (slow_continuous d _)
    ((slow_continuous d x).comp (continuous_id.add continuous_const))
    (slow_hasDerivAt d _) (fun r => (slow_hasDerivAt d x (r + t)).comp_add_const r t) s
  simpa [slow_initial, norm_le_zero_iff, sub_eq_zero] using h

lemma kernel_add (d : Data E H) (s t : ℝ) :
    kernel d (s + t) = kernel d s * kernel d t := by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  letI := NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)
  simp only [kernel, neg_add, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl d.B).smul_left (-s)).smul_right (-t))

lemma integrand_tail_integrable (d : Data E H) (x : E) (a : ℝ) :
    IntegrableOn (integrand d x) (Ici a) := by
  apply integrableOn_Ici_iff_integrableAtFilter_atTop.mpr
  exact ⟨⟨Ici 0, Ici_mem_atTop 0, integrand_integrable d x⟩,
    (integrand_continuous d x).locallyIntegrable.locallyIntegrableOn (Ici a)⟩

lemma integral_translate (f : ℝ → H) (a t : ℝ) :
    (∫ s in Ici a, f (s + t)) = ∫ s in Ici (a + t), f s := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) t).setIntegral_preimage_emb
    (MeasurableEquiv.addRight t).measurableEmbedding f (Ici (a + t))
  have hs : (fun s : ℝ => s + t) ⁻¹' Ici (a + t) = Ici a := by
    ext s; simp
  rwa [hs] at h

/-- Shift the convergent tail; no boundedness of the backward slow orbit is needed. -/
lemma graph_flow (d : Data E H) (x : E) (t : ℝ) :
    graph d (slowFlow d t x) =
      kernel d t (∫ s in Ici (-t), integrand d x s) := by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  have he (s : ℝ) : integrand d (slowFlow d t x) s =
      kernel d t (integrand d x (s - t)) := by
    dsimp [integrand]
    rw [slow_add, ← mul_apply_eq_comp, ← kernel_add]
    congr 2 <;> congr 1 <;> ring
  change (∫ s in Ici 0, integrand d (slowFlow d t x) s) = _
  simp_rw [he, sub_eq_add_neg]
  rw [integral_translate (fun s => kernel d t (integrand d x s)) 0 (-t), zero_add]
  exact (kernel d t).integral_comp_comm (integrand_tail_integrable d x (-t))

lemma kernel_hasDerivAt (d : Data E H) (t : ℝ) :
    HasDerivAt (kernel d) (-d.B * kernel d t) t := by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  convert hasDerivAt_exp_smul_const' (-d.B) t using 1
  · funext s; simp [kernel]
  · simp [kernel]

lemma tail_hasDerivAt (d : Data E H) (x : E) (a : ℝ) :
    HasDerivAt (fun b => ∫ s in Ici b, integrand d x s) (-integrand d x a) a := by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  have he (b : ℝ) : (∫ s in Ici b, integrand d x s) =
      graph d x - ∫ s in (0 : ℝ)..b, integrand d x s := by
    have h := intervalIntegral.integral_Ici_sub_Ici'
      (integrand_integrable d x) (integrand_tail_integrable d x b)
    change graph d x - _ = _ at h
    rw [← h]; abel
  simp_rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right
    ((integrand_continuous d x).intervalIntegrable 0 a)
    (integrand_continuous d x).aestronglyMeasurable.stronglyMeasurableAtFilter
    (integrand_continuous d x).continuousAt).const_sub (graph d x)

lemma tangent (d : Data E H) (x : E) :
    fderiv ℝ (graph d) x (d.slow.eval x) = -d.B (graph d x) + d.g x := by
  have htail : HasDerivAt (fun t => ∫ s in Ici (-t), integrand d x s) (d.g x) 0 := by
    have h := (tail_hasDerivAt d x 0).scomp_of_eq 0 (hasDerivAt_neg 0) (by simp)
    simpa only [Function.comp_def, neg_smul, one_smul, neg_neg, integrand,
      slow_initial, kernel, neg_zero, zero_smul, NormedSpace.exp_zero,
      one_apply_eq_self] using h
  have hd := (kernel_hasDerivAt d 0).clm_apply htail
  have hd' : HasDerivAt (fun t => graph d (slowFlow d t x))
      (-d.B (graph d x) + d.g x) 0 := by
    simp only [← graph_flow] at hd
    simpa [kernel, graph] using hd
  have hgraph : HasFDerivAt (graph d) (fderiv ℝ (graph d) x) (slowFlow d 0 x) := by
    simpa only [slow_initial] using (graph_hasFDerivAt d x).differentiableAt.hasFDerivAt
  have hc := hgraph.comp_hasDerivAt 0 (slow_hasDerivAt d x 0)
  simp only [slow_initial] at hc
  exact hc.unique hd'

/-- Integrating factor for the homogeneous fast equation on an actual interval. -/
lemma homogeneous_formula (d : Data E H) (I : OpenTimeInterval) (w : ℝ → H)
    (hw : ∀ t ∈ I.carrier, HasDerivAt w (-d.B (w t)) t)
    {s t : ℝ} (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    w t = kernel d (t - s) (w s) := by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  let v : ℝ → H := fun r => kernel d (-r) (w r)
  have hv (r : ℝ) (hr : r ∈ I.carrier) : HasDerivAt v 0 r := by
    have hd := (hasDerivAt_exp_smul_const d.B r).clm_apply (hw r hr)
    simpa [v, kernel, mul_apply_eq_comp] using hd
  have heq : v t = v s := I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun r hr => (hv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hv r hr).deriv) ht hs
  have h := congrArg (kernel d t) heq
  dsimp [v] at h
  have hk (a b : ℝ) (y : H) : kernel d a (kernel d b y) = kernel d (a + b) y := by
    rw [kernel_add]; rfl
  rw [hk, hk, add_neg_cancel] at h
  simpa [sub_eq_add_neg, kernel] using h

lemma residual_hasDerivAt (d : Data E H) (I : OpenTimeInterval) (z : ℝ → E × H)
    (hz : IsClassicalSolutionOn (fullODE d) I z) (t : ℝ) (ht : t ∈ I.carrier) :
    HasDerivAt (fun r => (z r).2 - graph d (z r).1)
      (-d.B ((z t).2 - graph d (z t).1)) t := by
  have hd : HasDerivAt z (field d (z t)) t := by
    simpa [fullODE, InvariantGraph.odeOn_eval] using hz.2.2 t ht
  have hx : HasDerivAt (fun r => (z r).1) (d.slow.eval (z t).1) t :=
    (ContinuousLinearMap.fst ℝ E H).hasFDerivAt.comp_hasDerivAt t hd
  have hy : HasDerivAt (fun r => (z r).2) (-d.B (z t).2 + d.g (z t).1) t :=
    (ContinuousLinearMap.snd ℝ E H).hasFDerivAt.comp_hasDerivAt t hd
  have hg := (graph_hasFDerivAt d (z t).1).differentiableAt.hasFDerivAt.comp_hasDerivAt t hx
  rw [tangent] at hg
  convert hy.sub hg using 1
  · rfl
  · simp only [map_sub]; abel

theorem regularity_and_tangency :
    Specs.D13Unified.Ch16.TriangularCenter.RegularityAndTangency.{u,v} := by
  intro E _ _ _ H _ _ _ d
  exact ⟨graph_contDiff d, graph_zero d,
    (graph_hasFDerivAt d 0).fderiv.trans (graphDerivative_zero d), tangent d⟩

theorem lifted_solutions : Specs.D13Unified.Ch16.TriangularCenter.LiftedSolutions.{u,v} := by
  intro E _ _ _ H _ _ _ d x
  have hc : ContDiff ℝ 1 (fun t => slowFlow d t x) :=
    (slow_joint_c1 d).comp (contDiff_id.prodMk contDiff_const)
  refine ⟨hc.prodMk ((graph_contDiff d).comp hc), ?_⟩
  intro t
  have hg := (graph_hasFDerivAt d (slowFlow d t x)).differentiableAt.hasFDerivAt.comp_hasDerivAt t (slow_hasDerivAt d x t)
  rw [tangent] at hg
  exact (slow_hasDerivAt d x t).prodMk hg

lemma kernel_contDiff (d : Data E H) : ContDiff ℝ 1 (kernel d) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (kernel_hasDerivAt d t).differentiableAt, ?_⟩
  have heq : deriv (kernel d) = fun t => -d.B * kernel d t :=
    funext fun t => (kernel_hasDerivAt d t).deriv
  rw [heq]
  exact continuous_const.mul (kernel_continuous d)

theorem complete_solutions : Specs.D13Unified.Ch16.TriangularCenter.CompleteSolutions.{u,v} := by
  intro E _ _ _ H _ _ _ d x y
  have hs : ContDiff ℝ 1 (fun t => slowFlow d t x) :=
    (slow_joint_c1 d).comp (contDiff_id.prodMk contDiff_const)
  refine ⟨hs.prodMk (((graph_contDiff d).comp hs).add
    ((kernel_contDiff d).clm_apply contDiff_const)), ?_, ?_⟩
  · simp [slow_initial, kernel]
  · intro t
    have hg := (graph_hasFDerivAt d (slowFlow d t x)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (slow_hasDerivAt d x t)
    rw [tangent] at hg
    have hk := (kernel_hasDerivAt d t).clm_apply (hasDerivAt_const t (y - graph d x))
    have hd := (slow_hasDerivAt d x t).prodMk (hg.add hk)
    convert hd using 1
    · rfl
    · ext <;> simp [field, mul_apply_eq_comp, map_add] <;> abel

theorem invariant_graph : Specs.D13Unified.Ch16.TriangularCenter.Invariance.{u,v} := by
  intro E _ _ _ H _ _ _ d I z s hz hs hinit t ht
  have h := homogeneous_formula d I (fun r => (z r).2 - graph d (z r).1)
    (residual_hasDerivAt d I z hz) hs ht
  simpa [hinit, sub_eq_zero] using h

theorem tracking : Specs.D13Unified.Ch16.TriangularCenter.Tracking.{u,v} := by
  intro E _ _ _ H _ _ _ d I z hz h0 t ht ht0
  have h := homogeneous_formula d I (fun r => (z r).2 - graph d (z r).1)
    (residual_hasDerivAt d I z hz) h0 ht
  simp only [sub_zero] at h
  refine ⟨h, ?_⟩
  rw [h]
  exact ((kernel d t).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (d.decay t ht0) (norm_nonneg _))

end D13Unified.Ch16.TriangularCenter
