import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.StableManifold
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.StableGraphs
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.Dichotomy
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.Continuation
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped ContDiff NNReal

namespace D13Unified.Ch20.StableManifold
open D13Unified.Ch07
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronFixedPoints
open Specs.D13Unified.Ch20.PerronRegularity
open Specs.D13Unified.Ch20.StableGraphs

universe u v
variable {n : Type u} [Fintype n] [DecidableEq n]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace BoundedGreen
open Specs.D13Unified.Ch20.PerronWeightedIntegrals
open D13Unified.Ch20.PerronWeightedIntegrals
/-- The stable Green estimate also applies at zero decay weight. -/
lemma stable_estimate_nonneg
    [CompleteSpace E] (A P : E →L[ℝ] E) (K α β M : ℝ)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hβα : β < α)
    (hd : StableDecay A P K α) (g : ℝ → E) (hg : WeightedBound β M g)
    (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (kernel A P g t) (Icc 0 t) ∧
    Real.exp (β * t) * ‖stableIntegral A P g t‖ ≤ K * M / (α - β) := by
  have hrate : 0 < α - β := sub_pos.mpr hβα
  have hC : 0 ≤ K * M * Real.exp (-α*t) := by have := hg.2.1; positivity
  have hcont := (kernel_continuousOn A P hg.1 t).mono
    (show Icc 0 t ⊆ Ici 0 from fun s hs => hs.1)
  have hi : IntegrableOn (kernel A P g t) (Icc 0 t) := hcont.integrableOn_Icc
  refine ⟨hi, ?_⟩
  have hmajor : IntegrableOn (fun s => (K*M*Real.exp (-α*t))*Real.exp ((α-β)*s)) (Iic t) :=
    (integrableOn_exp_mul_Iic hrate t).const_mul _
  have hbound : ‖stableIntegral A P g t‖ ≤
      (K*M*Real.exp (-α*t)) * (Real.exp ((α-β)*t) / (α-β)) := by
    calc
      ‖stableIntegral A P g t‖ ≤
          ∫ s in Icc 0 t, (K*M*Real.exp (-α*t))*Real.exp ((α-β)*s) := by
        apply norm_integral_le_of_norm_le
          (hmajor.mono_set (fun _ hs => hs.2))
        exact (ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall (fun s hs => stable_kernel_bound A P (by linarith) hd hg hs.1 hs.2))
      _ ≤ ∫ s in Iic t, (K*M*Real.exp (-α*t))*Real.exp ((α-β)*s) := by
        apply setIntegral_mono_set hmajor
        · exact Filter.Eventually.of_forall (fun s => mul_nonneg hC (Real.exp_pos _).le)
        · exact Filter.Eventually.of_forall (fun s hs => hs.2)
      _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hrate]
  calc
    Real.exp (β*t)*‖stableIntegral A P g t‖ ≤
        Real.exp (β*t)*((K*M*Real.exp (-α*t))*(Real.exp ((α-β)*t)/(α-β))) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (K*M/(α-β))*(Real.exp (β*t)*Real.exp (-α*t)*Real.exp ((α-β)*t)) := by ring
    _ = K*M/(α-β) := by
      rw [← Real.exp_add, ← Real.exp_add, show β*t + -α*t + (α-β)*t = 0 by ring]
      simp

/-- Absolute integrability of the unstable tail does not require decay of g. -/
lemma unstable_estimate_nonneg
    [CompleteSpace E] (A P : E →L[ℝ] E) (K α β M : ℝ)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hβα : β < α)
    (hd : UnstableDecay A P K α) (g : ℝ → E) (hg : WeightedBound β M g)
    (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (kernel A P g t) (Ici t) ∧
    Real.exp (β * t) * ‖unstableIntegral A P g t‖ ≤ K * M / (α + β) := by
  have hrate : -(α+β) < 0 := by linarith
  have hC : 0 ≤ K*M*Real.exp (α*t) := by have := hg.2.1; positivity
  have hmajor : IntegrableOn (fun s => (K*M*Real.exp (α*t))*Real.exp ((-(α+β))*s)) (Ici t) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hrate t)).const_mul _
  have hbound : ∀ᵐ s ∂volume.restrict (Ici t), ‖kernel A P g t s‖ ≤
      (K*M*Real.exp (α*t))*Real.exp ((-(α+β))*s) :=
    (ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall (fun s hs => unstable_kernel_bound A P (by linarith) hd hg ht hs))
  have hmeas : AEStronglyMeasurable (kernel A P g t) (volume.restrict (Ici t)) := ((kernel_continuousOn A P hg.1 t).mono
    (show Ici t ⊆ Ici 0 from fun s hs => ht.trans hs)).aestronglyMeasurable measurableSet_Ici
  have hi : IntegrableOn (kernel A P g t) (Ici t) := hmajor.mono' hmeas hbound
  refine ⟨hi, ?_⟩
  have hn : ‖unstableIntegral A P g t‖ ≤
      (K*M*Real.exp (α*t)) * (Real.exp ((-(α+β))*t) / (α+β)) := by
    calc
      ‖unstableIntegral A P g t‖ ≤
          ∫ s in Ici t, (K*M*Real.exp (α*t))*Real.exp ((-(α+β))*s) :=
        norm_integral_le_of_norm_le hmajor hbound
      _ = _ := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hrate]
        simp only [neg_div_neg_eq]
  calc
    Real.exp (β*t)*‖unstableIntegral A P g t‖ ≤
        Real.exp (β*t)*((K*M*Real.exp (α*t))*(Real.exp ((-(α+β))*t)/(α+β))) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = (K*M/(α+β))*(Real.exp (β*t)*Real.exp (α*t)*Real.exp ((-(α+β))*t)) := by ring
    _ = K*M/(α+β) := by
      rw [← Real.exp_add, ← Real.exp_add, show β*t + α*t + (-(α+β))*t = 0 by ring]
      simp


end BoundedGreen


/-- The unweighted half-line Green inverse, including its ODE and stable
initial projection. The forcing is merely bounded and continuous. -/
lemma bounded_green
    (L Ps Pu : E →L[ℝ] E) (K α M : ℝ) (hK : 1 ≤ K) (hα : 0 < α)
    (hs : Specs.D13Unified.Ch20.PerronWeightedIntegrals.StableDecay L Ps K α)
    (hu : Specs.D13Unified.Ch20.PerronWeightedIntegrals.UnstableDecay L Pu K α)
    (hSum : Ps + Pu = 1) (hCross : Ps * Pu = 0)
    (hcS : Commute Ps L) (hcU : Commute Pu L)
    (g : ℝ → E)
    (hg : Specs.D13Unified.Ch20.PerronWeightedIntegrals.WeightedBound 0 M g) :
    ∃ v : WeightedPath 0 E,
      (∀ t, 0 ≤ t → v.atReal t = PerronIntegralODE.perronPath L Ps Pu g 0 t) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt v.atReal (L (v.atReal t) + g t) (Ici 0) t) ∧
      Ps (v.atReal 0) = 0 ∧ ‖v‖ ≤ 2 * K * M / α := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hstable := fun t ht => BoundedGreen.stable_estimate_nonneg
    L Ps K α 0 M hK le_rfl hα hs g hg t ht
  have hunstable := fun t ht => BoundedGreen.unstable_estimate_nonneg
    L Pu K α 0 M hK le_rfl hα hu g hg t ht
  have htail : IntegrableOn (fun s => PerronIntegralODE.evolution L (-s) (Pu (g s)))
      (Ici 0) := by
    have hh := (hunstable 0 le_rfl).1
    change IntegrableOn (fun s => PerronIntegralODE.evolution L (0-s) (Pu (g s))) (Ici 0) at hh
    simpa only [zero_sub] using hh
  have hv := PerronIntegralODE.perron_integral_ode L Ps Pu hSum hCross hcS hcU
    g hg.1 htail 0 (by simp)
  have hbound (t : ℝ) (ht : 0 ≤ t) :
      ‖PerronIntegralODE.perronPath L Ps Pu g 0 t‖ ≤ 2 * K * M / α := by
    have hs0 := (hstable t ht).2
    have hu0 := (hunstable t ht).2
    simp only [zero_mul, Real.exp_zero, one_mul, sub_zero, add_zero] at hs0 hu0
    have heq : PerronIntegralODE.perronPath L Ps Pu g 0 t =
        Specs.D13Unified.Ch20.PerronWeightedIntegrals.stableIntegral L Ps g t -
        Specs.D13Unified.Ch20.PerronWeightedIntegrals.unstableIntegral L Pu g t := by
      rw [PerronWeightedIntegrals.stable_interval_eq L Ps g t ht]
      simp [PerronIntegralODE.perronPath, PerronIntegralODE.stableIntegral,
        PerronIntegralODE.unstableIntegral,
        Specs.D13Unified.Ch20.PerronWeightedIntegrals.unstableIntegral,
        Specs.D13Unified.Ch20.PerronWeightedIntegrals.kernel]
      rfl
    rw [heq]
    exact (norm_sub_le _ _).trans ((add_le_add hs0 hu0).trans_eq (by ring))
  let v := WeightedPath.ofPath 0
    (fun t : HalfLine => PerronIntegralODE.perronPath L Ps Pu g 0 t)
    (continuousOn_iff_continuous_domRestrict.mp hv.2.1)
    (2 * K * M / α) (by intro t; simpa using hbound t t.property)
  have heq (t : ℝ) (ht : 0 ≤ t) :
      v.atReal t = PerronIntegralODE.perronPath L Ps Pu g 0 t := by
    rw [WeightedPath.atReal_nonneg _ ht]
    exact congrFun (WeightedPath.eval_ofPath _ _ _ _) ⟨t, ht⟩
  refine ⟨v, heq, ?_, ?_, ?_⟩
  · intro t ht
    have hh := hv.2.2.1 t ht
    rw [← heq t ht] at hh
    exact hh.congr_of_mem (fun s hs => heq s hs) ht
  · rw [heq 0 le_rfl]
    exact hv.2.2.2
  · apply (WeightedPath.norm_le_iff v (by have := hg.2.1; positivity)).mpr
    intro t
    rw [← WeightedPath.atReal_nonneg _ t.property, heq t t.property]
    simpa using hbound t t.property

/-- A bounded solution with zero stable initial projection equals its Green
integral. No exponential decay is assumed in this representation. -/
lemma bounded_solution_bound
    (L Ps Pu : E →L[ℝ] E) (K α M : ℝ) (hK : 1 ≤ K) (hα : 0 < α)
    (hs : Specs.D13Unified.Ch20.PerronWeightedIntegrals.StableDecay L Ps K α)
    (hu : Specs.D13Unified.Ch20.PerronWeightedIntegrals.UnstableDecay L Pu K α)
    (hSum : Ps + Pu = 1) (hCross : Ps * Pu = 0)
    (hcS : Commute Ps L) (hcU : Commute Pu L)
    (g : ℝ → E)
    (hg : Specs.D13Unified.Ch20.PerronWeightedIntegrals.WeightedBound 0 M g)
    (w : WeightedPath 0 E)
    (hw : ∀ t, 0 ≤ t → HasDerivWithinAt w.atReal (L (w.atReal t) + g t) (Ici 0) t)
    (h0 : Ps (w.atReal 0) = 0) : ‖w‖ ≤ 2 * K * M / α := by
  obtain ⟨v, _, hv, hv0, hvbound⟩ := bounded_green
    L Ps Pu K α M hK hα hs hu hSum hCross hcS hcU g hg
  have hz : w - v = 0 := by
    apply StableGraphs.homogeneous_halfLine_zero L Ps Pu K α 0 hα le_rfl hSum hcU hu
    · intro t ht
      have hh := (hw t ht).sub (hv t ht)
      simp only [add_sub_add_right_eq_sub, ← map_sub] at hh
      rw [← StableGraphs.weightedPath_atReal_sub] at hh
      exact hh.congr_of_mem (fun s _ => StableGraphs.weightedPath_atReal_sub w v s) ht
    · rw [StableGraphs.weightedPath_atReal_sub, map_sub, h0, hv0, sub_self]
  exact (sub_eq_zero.mp hz) ▸ hvbound

/-- Uniqueness among bounded half-line solutions at a prescribed stable
projection. Boundedness, rather than an assumed decay rate, is the hypothesis. -/
lemma bounded_solution_unique
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hδ : 0 ≤ δ) (hq : 2 * K * δ / α < 1)
    (r : E → E) (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (w v : WeightedPath 0 E)
    (hw : ∀ t, 0 ≤ t → HasDerivWithinAt w.atReal
      (matrixOperatorEquiv b A (w.atReal t) + r (w.atReal t)) (Ici 0) t)
    (hv : ∀ t, 0 ≤ t → HasDerivWithinAt v.atReal
      (matrixOperatorEquiv b A (v.atReal t) + r (v.atReal t)) (Ici 0) t)
    (h0 : projection b A true (w.atReal 0) = projection b A true (v.atReal 0)) : w = v := by
  let d := w - v
  let g := fun t => r (w.atReal t) - r (v.atReal t)
  have hrc : Continuous r :=
    (LipschitzWith.of_dist_le_mul (K := (⟨δ, hδ⟩ : ℝ≥0)) (fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip x y)).continuous
  have hg : Specs.D13Unified.Ch20.PerronWeightedIntegrals.WeightedBound 0
      (δ * ‖d‖) g := by
    refine ⟨(hrc.comp_continuousOn w.atReal_continuousOn).sub
      (hrc.comp_continuousOn v.atReal_continuousOn), by positivity, ?_⟩
    intro t ht
    simp only [zero_mul, Real.exp_zero, one_mul]
    calc
      ‖g t‖ ≤ δ * ‖d.atReal t‖ := by
        simpa only [g, d, StableGraphs.weightedPath_atReal_sub] using
          hlip (w.atReal t) (v.atReal t)
      _ ≤ δ * ‖d‖ := mul_le_mul_of_nonneg_left
        (by simpa only [WeightedPath.atReal_nonneg _ ht] using
          WeightedPath.eval_norm_le_norm (β := 0) le_rfl d ⟨t, ht⟩) hδ
  obtain ⟨hs, hu⟩ := PerronFixedPoints.operator_decay b A K α hd
  obtain ⟨hSum, hCross, hcS, hcU⟩ := PerronFixedPoints.operator_projection_laws b A hA
  have hb := bounded_solution_bound (matrixOperatorEquiv b A)
    (projection b A true) (projection b A false) K α (δ * ‖d‖)
    hK hα hs hu hSum hCross hcS hcU g hg d
    (by
      intro t ht
      have hh := (hw t ht).sub (hv t ht)
      rw [show (matrixOperatorEquiv b A (w.atReal t) + r (w.atReal t)) -
          (matrixOperatorEquiv b A (v.atReal t) + r (v.atReal t)) =
          matrixOperatorEquiv b A (d.atReal t) + g t by
        simp only [d, g, StableGraphs.weightedPath_atReal_sub, map_sub]; abel] at hh
      exact hh.congr_of_mem (fun s _ => StableGraphs.weightedPath_atReal_sub w v s) ht)
    (by simp only [d, StableGraphs.weightedPath_atReal_sub, map_sub, h0, sub_self])
  have hz : ‖d‖ = 0 := by
    have hb' : ‖d‖ ≤ (2 * K * δ / α) * ‖d‖ := hb.trans_eq (by ring)
    nlinarith [norm_nonneg d]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Encode a continuous bounded half-line curve, with no decay hypothesis. -/
def boundedPath (x : ℝ → E) (hx : ContinuousOn x (Ici 0)) (M : ℝ)
    (hb : ∀ t, 0 ≤ t → ‖x t‖ ≤ M) : WeightedPath 0 E :=
  WeightedPath.ofPath 0 (fun t : HalfLine => x t)
    (continuousOn_iff_continuous_domRestrict.mp hx) M (by intro t; simpa using hb t t.property)

lemma boundedPath_atReal (x : ℝ → E) (hx : ContinuousOn x (Ici 0)) (M : ℝ)
    (hb : ∀ t, 0 ≤ t → ‖x t‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    (boundedPath x hx M hb).atReal t = x t := by
  rw [WeightedPath.atReal_nonneg _ ht]
  exact congrFun (WeightedPath.eval_ofPath _ _ _ _) ⟨t, ht⟩

/-- Every bounded extension trajectory starts on the constructed stable
 graph, even when no decay estimate for that trajectory is supplied. -/
lemma bounded_trajectory_on_graph
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hδ : 0 ≤ δ) (hq : 2 * K * δ / α < 1)
    (r : E → E) (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (φ : ℝ → E → E) (hφ : CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ)
    (h : stableParameters b A → unstableParameters b A) (C β : ℝ)
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hb : ∀ ξ t, 0 ≤ t → ‖φ t (graphMap h ξ)‖ ≤ C * ‖(ξ : E)‖ * Real.exp (-β * t))
    (x : ℝ → E) (hc : ContinuousOn x (Ici 0))
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x
      (matrixOperatorEquiv b A (x t) + r (x t)) (Ici 0) t)
    (hbounded : ∃ M, ∀ t, 0 ≤ t → ‖x t‖ ≤ M) :
    x 0 ∈ Set.range (graphMap h) := by
  obtain ⟨M, hM⟩ := hbounded
  let ξ := StableGraphs.stableParameterProjection b A hA (x 0)
  let w := boundedPath x hc M hM
  have hvc : ContinuousOn (fun t => φ t (graphMap h ξ)) (Ici 0) :=
    (hφ.1.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hvb (t : ℝ) (ht : 0 ≤ t) : ‖φ t (graphMap h ξ)‖ ≤ C * ‖(ξ : E)‖ := by
    apply (hb ξ t ht).trans
    exact mul_le_of_le_one_right (mul_nonneg hC (norm_nonneg _))
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) ht))
  let v := boundedPath (fun t => φ t (graphMap h ξ)) hvc (C * ‖(ξ : E)‖) hvb
  have hew (t : ℝ) (ht : 0 ≤ t) : w.atReal t = x t := boundedPath_atReal _ _ _ _ ht
  have hev (t : ℝ) (ht : 0 ≤ t) : v.atReal t = φ t (graphMap h ξ) := boundedPath_atReal _ _ _ _ ht
  have heq : w = v := bounded_solution_unique b A hA K α δ hK hα hd hδ hq r hlip w v
    (by
      intro t ht
      rw [hew t ht]
      exact (hx t ht).congr_of_mem (fun s hs => hew s hs) ht)
    (by
      intro t ht
      rw [hev t ht]
      exact (hφ.2.2.2 (graphMap h ξ) t).hasDerivWithinAt.congr_of_mem
        (fun s hs => hev s hs) ht)
    (by
      rw [hew 0 le_rfl, hev 0 le_rfl, hφ.2.1]
      have hh := congrArg (fun z : stableParameters b A => (z : E))
        ((StableGraphs.stableParameterProjection b A hA).map_add (ξ : E) (h ξ : E))
      simp only [StableGraphs.stableParameterProjection_left,
        StableGraphs.stableParameterProjection_unstable, add_zero,
        StableGraphs.stableParameterProjection_coe] at hh
      exact hh.symm)
  refine ⟨ξ, ?_⟩
  have hh := congrArg (fun z : WeightedPath 0 E => z.atReal 0) heq
  rw [hew 0 le_rfl, hev 0 le_rfl, hφ.2.1] at hh
  exact hh.symm

open D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch01.SolutionConcepts

/-- On any segment where the extension stays in its agreement ball, its
 trajectory belongs to the original canonical maximal solution. A connected
 component of the open survival set supplies the actual open solution interval. -/
lemma flow_matches_on_segment
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (p : E) (L : E →L[ℝ] E) (r : E → E) (ρ : ℝ)
    (hloc : ∀ x, ‖x‖ < ρ → p + x ∈ F.domain ∧ L x + r x = F.eval (p + x))
    (φ : ℝ → E → E) (hφ : CompleteFlow (fun x => L x + r x) φ)
    (x : E) (t : ℝ) (hb : ∀ s ∈ uIcc 0 t, ‖φ s x‖ < ρ) :
    (t, p + x) ∈ flowDomain F ∧ flow F t (p + x) = p + φ t x := by
  let D : Set ℝ := {s | ‖φ s x‖ < ρ}
  have hcurve : Continuous (fun s => p + φ s x) :=
    continuous_const.add (hφ.1.comp (continuous_id.prodMk continuous_const))
  have hD : IsOpen D := isOpen_lt
    ((hφ.1.comp (continuous_id.prodMk continuous_const)).norm) continuous_const
  have hD0 : 0 ∈ D := hb 0 left_mem_uIcc
  have hJ0 : 0 ∈ connectedComponentIn D 0 := mem_connectedComponentIn hD0
  let J : OpenTimeInterval :=
    ⟨⟨connectedComponentIn D 0, ⟨0, hJ0⟩,
      isPreconnected_connectedComponentIn.ordConnected⟩, hD.connectedComponentIn⟩
  have hJt : t ∈ J.carrier :=
    isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hb right_mem_uIcc
  have hJb (s : ℝ) (hs : s ∈ J.carrier) : ‖φ s x‖ < ρ :=
    connectedComponentIn_subset D 0 hs
  have hinit : p + x ∈ F.domain := by
    have hh := (hloc (φ 0 x) hD0).1
    simpa only [hφ.2.1] using hh
  have hsol : classicalIVPOnValue F.toODE J (fun s => p + φ s x) 0 (p + x) := by
    refine ⟨(classical_iff_solutionOn F.toODE J _).mpr ⟨hcurve.continuousOn,
      fun s hs => (hloc _ (hJb s hs)).1, ?_⟩, hJ0, by change p + φ 0 x = p + x; rw [hφ.2.1]⟩
    intro s hs
    have hd := (hφ.2.2.2 x s).const_add p
    dsimp only at hd
    rw [(hloc _ (hJb s hs)).2] at hd
    simpa only [AutonomousODE.toODE_eval] using hd.hasDerivWithinAt
  have hcan := ODE.canonical_solution F.toODE
    (F.locallyLipschitzInState_of_contDiffOn hF) 0 (p + x) hinit
  have hcover := hcan.2.2.2.2.2.1 J _ hsol
  change J.carrier ⊆ (flowInterval F (p + x)).carrier ∧
    EqOn (fun s => flow F s (p + x)) (fun s => p + φ s x) J.carrier at hcover
  exact ⟨⟨hinit, hcover.1 hJt⟩, hcover.2 hJt⟩

/-- Localization is independent of the orientation of time. Its inputs are
 proved global graph properties; it assumes no local trajectory certificate. -/
lemma localize_graph
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (p : E) (L : E →L[ℝ] E) (r : E → E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x-y‖)
    (ρ ε C β σ : ℝ) (hε : 0 < ε) (hC : 0 < C) (hβ : 0 ≤ β)
    (hsmall : C * ε ≤ ρ) (hσ : σ = 1 ∨ σ = -1)
    (hloc : ∀ x, ‖x‖ < ρ → p + x ∈ F.domain ∧ L x + r x = F.eval (p + x))
    (φ ψ : ℝ → E → E) (hφ : CompleteFlow (fun x => L x + r x) φ)
    (hψ : CompleteFlow (fun x => σ • (L x + r x)) ψ)
    (htime : ∀ t x, ψ t x = φ (σ * t) x)
    {S T : Submodule ℝ E} (h : S → T)
    (hinv : ∀ ξ t, 0 ≤ t → ψ t (graphMap h ξ) ∈ Set.range (graphMap h))
    (hbound : ∀ ξ t, 0 ≤ t → ‖ψ t (graphMap h ξ)‖ ≤ C * ‖(ξ : E)‖ * Real.exp (-β * t))
    (hchar : ∀ x : ℝ → E, ContinuousOn x (Ici 0) →
      (∀ t, 0 ≤ t → HasDerivWithinAt x (σ • (L (x t) + r (x t))) (Ici 0) t) →
      (∃ M, ∀ t, 0 ≤ t → ‖x t‖ ≤ M) → x 0 ∈ Set.range (graphMap h)) :
    Specs.D13Unified.Ch20.StableManifold.LocalizedGraph F p σ ψ h ρ ε C β := by
  have hcenter {I : Set ℝ} (x : ℝ → E)
      (hx : ∀ t ∈ I, HasDerivWithinAt x (σ • F.eval (x t)) I t)
      (hb : ∀ t ∈ I, ‖x t - p‖ < ρ) :
      ∀ t ∈ I, HasDerivWithinAt (fun s => x s - p)
        (σ • (L (x t - p) + r (x t - p))) I t := by
    intro t ht
    have hh := (hx t ht).sub_const p
    rw [show L (x t - p) + r (x t - p) = F.eval (x t) by
      simpa only [add_sub_cancel] using (hloc (x t - p) (hb t ht)).2]
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · intro x hc hx hb
    exact hchar (fun t => x t - p) (hc.sub continuousOn_const)
      (hcenter x hx hb) ⟨ρ, fun t ht => (hb t ht).le⟩
  · intro ξ hξ t ht
    have hall (s : ℝ) (hs : 0 ≤ s) : ‖ψ s (graphMap h ξ)‖ < ρ := by
      calc
        ‖ψ s (graphMap h ξ)‖ ≤ C * ‖(ξ : E)‖ * Real.exp (-β * s) := hbound ξ s hs
        _ ≤ C * ‖(ξ : E)‖ := mul_le_of_le_one_right (by positivity)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hs))
        _ < C * ε := mul_lt_mul_of_pos_left hξ hC
        _ ≤ ρ := hsmall
    have hseg : ∀ s ∈ uIcc 0 (σ * t), ‖φ s (graphMap h ξ)‖ < ρ := by
      intro s hs
      rcases hσ with rfl | rfl
      · simp only [one_mul, uIcc_of_le ht] at hs
        simpa only [htime, one_mul] using hall s hs.1
      · simp only [neg_one_mul, uIcc_of_ge (neg_nonpos.mpr ht)] at hs
        have hh := hall (-s) (neg_nonneg.mpr hs.2)
        simpa only [htime, neg_one_mul, neg_neg] using hh
    obtain ⟨hdom, heq⟩ := flow_matches_on_segment F hF p L r ρ hloc φ hφ _ (σ*t) hseg
    refine ⟨hall t ht, hdom, heq.trans (by rw [htime]), ?_⟩
    rw [heq, ← htime, add_sub_cancel_left]
    exact hbound ξ t ht
  · intro x t ht hc hx hb hstart
    let Kr : ℝ≥0 := ⟨δ, hδ⟩
    have hrlip : LipschitzWith Kr r := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip a b
    have hV : LipschitzWith (‖L‖₊ + Kr) (fun x => σ • (L x + r x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      have hh := (L.lipschitzWith.add hrlip).dist_le_mul a b
      rcases hσ with rfl | rfl
      · simpa only [one_smul] using hh
      · simpa only [neg_one_smul, dist_neg_neg] using hh
    have heq := ODE_solution_unique (v := fun _ x => σ • (L x + r x))
      (a := 0) (b := t) (f := fun s => x s - p)
      (g := fun s => ψ s (x 0-p)) (fun _ => hV) (hc.sub continuousOn_const)
      (fun s hs => (hcenter x hx hb s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
      ((hψ.1.comp (continuous_id.prodMk continuous_const)).continuousOn)
      (fun s _ => (hψ.2.2.2 (x 0-p) s).hasDerivWithinAt) (hψ.2.1 (x 0-p)).symm
    obtain ⟨ξ, hξ⟩ := hstart
    have hh := heq ⟨ht, le_rfl⟩
    change x t - p = ψ t (x 0 - p) at hh
    rw [hh, ← hξ]
    exact hinv ξ t ht

/-- The full local stable and unstable manifold theorem. The small extension
 is selected after the dichotomy; its unweighted contraction proves the
 bounded-orbit characterization and its weighted bound proves local survival. -/
theorem stable_manifold :
    Specs.D13Unified.Ch20.StableManifold.stableManifoldExpected.{u, v} := by
  intro n _ _ E _ _ _ b F p A k hp hk hf hfp hdf hA
  obtain ⟨K, α, hK, hα, hd⟩ := D13Unified.Ch20.exponential_dichotomy b A hA
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let β : ℝ := α / 2
  let δ : ℝ := α / (16 * K)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β < α := by dsimp [β]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrate : contractionRate K α β δ = 1/6 := by
    have hm : α - β = α/2 := by dsimp [β]; ring
    have hp : α + β = 3*α/2 := by dsimp [β]; ring
    rw [contractionRate, hm, hp]
    dsimp only [δ]
    field_simp
    <;> ring
  have hq : contractionRate K α β δ < 1 := by rw [hrate]; norm_num
  have hq0 : 2*K*δ/α < 1 := by
    have heq : 2*K*δ/α = 1/8 := by
      dsimp only [δ]
      field_simp
      <;> ring
    rw [heq]
    norm_num
  obtain ⟨r, φ, hs, hu, hrc, hrcompact, hr0, hdr0, hlip,
    ⟨V, hV, hV0, hVU, hlocV⟩, hφ, hsg, hug, hsinv, huinv, hsbound, hubound⟩ :=
    StableGraphs.stable_graphs_exists b F.domain F.eval p A k F.isOpen_domain hp hk hf hfp hdf hA
      K α β δ hK hα hd hβ hβα hδ hq
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.mp hV 0 hV0
  have hloc (x : E) (hx : ‖x‖ < ρ) :
      p + x ∈ F.domain ∧ matrixOperatorEquiv b A x + r x = F.eval (p+x) := by
    have hxV : x ∈ V := hρV (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
    exact ⟨hVU x hxV, hlocV x hxV⟩
  let C := K / (1 - contractionRate K α β δ)
  have hC : 0 < C := div_pos hKpos (sub_pos.mpr hq)
  let ε := ρ / (2*C)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : C*ε ≤ ρ := by
    dsimp only [ε]
    have heq : C * (ρ/(2*C)) = ρ/2 := by field_simp <;> ring
    rw [heq]
    linarith
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hf.of_le (by exact_mod_cast hk)
  have hψ : CompleteFlow (fun x => (-1 : ℝ) • (matrixOperatorEquiv b A x + r x))
      (fun t x => φ (-t) x) := by
    have heq : (fun x => (-1 : ℝ) • (matrixOperatorEquiv b A x + r x)) =
        -(fun x => matrixOperatorEquiv b A x + r x) := by
      funext x
      simp only [neg_one_smul, Pi.neg_apply]
    rw [heq]
    exact StableGraphs.completeFlow_reverse hφ
  have hφneg : CompleteFlow (fun x => matrixOperatorEquiv b (-A) x + (-r) x)
      (fun t x => φ (-t) x) := by
    have heq : (fun x => matrixOperatorEquiv b (-A) x + (-r) x) =
        -(fun x => matrixOperatorEquiv b A x + r x) := by
      funext x
      simp only [map_neg, neg_apply, Pi.neg_apply, neg_add]
    rw [heq]
    exact StableGraphs.completeFlow_reverse hφ
  have hlipneg : ∀ x y, ‖(-r) x - (-r) y‖ ≤ δ*‖x-y‖ := by
    intro x y
    simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using hlip x y
  have hsinv' : ∀ ξ t, 0 ≤ t → φ (-t) (graphMap hu ξ) ∈ Set.range (graphMap hu) :=
    fun ξ t ht => huinv ξ (-t) (neg_nonpos.mpr ht)
  have hubound' : ∀ ξ t, 0 ≤ t → ‖φ (-t) (graphMap hu ξ)‖ ≤
      C*‖(ξ : E)‖*Real.exp (-β*t) := by
    intro ξ t ht
    simpa only [mul_neg, neg_mul] using hubound ξ (-t) (neg_nonpos.mpr ht)
  have hlocalS := localize_graph F hF1 p (matrixOperatorEquiv b A) r δ hδ.le hlip
    ρ ε C β 1 hε hC hβ.le hsmall (Or.inl rfl) hloc φ φ hφ
    (by simpa only [one_smul] using hφ) (by intros; simp only [one_mul])
    hs hsinv hsbound (by
      intro x hc hx hb
      exact bounded_trajectory_on_graph b A hA K α δ hK hα hd hδ.le hq0
        r hlip φ hφ hs C β hC.le hβ.le hsbound x hc
        (by simpa only [one_smul] using hx) hb)
  have hlocalU := localize_graph F hF1 p (matrixOperatorEquiv b A) r δ hδ.le hlip
    ρ ε C β (-1) hε hC hβ.le hsmall (Or.inr rfl) hloc φ (fun t x => φ (-t) x) hφ
    hψ (by intros; simp only [neg_one_mul]) hu hsinv' hubound' (by
      intro x hc hx hb
      have hh := bounded_trajectory_on_graph b (-A) (StableGraphs.hyperbolic_neg A hA)
        K α δ hK hα (StableGraphs.dichotomyBounds_neg b A K α hd) hδ.le hq0
        (-r) hlipneg (fun t x => φ (-t) x) hφneg
      rw [StableGraphs.stableParameters_neg, StableGraphs.unstableParameters_neg] at hh
      apply hh hu C β hC.le hβ.le hubound' x hc _ hb
      simpa only [map_neg, neg_apply, Pi.neg_apply, neg_add, neg_one_smul] using hx)
  exact ⟨K, α, β, δ, ρ, ε, C, hK, hα, hd, hβ, hβα, hδ, hq,
    hρ, hε, hC, rfl, r, φ, hs, hu, hrc, hrcompact, hr0, hdr0, hlip, hloc, hφ,
    hsg, hug, hsinv, huinv, hsbound, hubound, hlocalS, hlocalU⟩

end D13Unified.Ch20.StableManifold
