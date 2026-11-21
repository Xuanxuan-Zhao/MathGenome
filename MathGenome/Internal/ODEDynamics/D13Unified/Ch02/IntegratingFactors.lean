import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.IntegratingFactors
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ExactRectangle
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ScalarLinear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination

noncomputable section
open Set
namespace D13Unified.IntegratingFactors
open Specs.D13Unified.Ch02.ExactRectangle
open Specs.D13Unified.Ch02.IntegratingFactors

theorem equation_iff : equationIffExpected := by
  intro P Q μ p v hμ
  rw [show μ p * P p + (μ p * Q p) * v = μ p * (P p + Q p * v) by ring]
  exact mul_eq_zero.trans (or_iff_right hμ)

theorem exact_equation : exactEquationExpected := by
  intro I J P Q μ hP hQ hμ
  have hMP := hμ.1.mul hP
  have hMQ := hμ.1.mul hQ
  refine ⟨hMP, hMQ, fun s hs ξ hξ => ⟨?_, ?_⟩⟩
  · exact ExactRectangle.potential_partials I J _ _ hMP hMQ hμ.2.2 s hs ξ hξ
  · intro K x hK hx hg
    have heq := forall₂_congr fun t ht =>
      equation_iff P Q μ (t, x t) (derivWithin x K.carrier t) (hμ.2.1 _ (hg t ht))
    refine ⟨heq, ?_⟩
    rw [← heq]
    exact ExactRectangle.potential_graph_on_interval_iff I J _ _ hMP hMQ
      hμ.2.2 s hs ξ hξ K x hK hx hg

/-- Classical graphs retain their actual open domains and ordinary derivatives. -/
theorem classical_graph_iff : classicalGraphExpected := by
  intro I J P Q μ hP hQ hμ s hs ξ hξ K x hx hg
  have heq := forall₂_congr fun t ht =>
    equation_iff P Q μ (t, x t) (deriv x t) (hμ.2.1 _ (hg t ht))
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact ExactRectangle.potential_graph_iff I J _ _ (hμ.1.mul hP) (hμ.1.mul hQ)
    hμ.2.2 s hs ξ hξ K x hx hg

/-- Continuity of the coefficient suffices for C¹ of its primitive, with no
regularity required outside the actual interval. -/
lemma primitive_contDiffOn (I : OpenTimeInterval) {h : ℝ → ℝ}
    (hh : ContinuousOn h I.carrier) {s : ℝ} (hs : s ∈ I.carrier) :
    ContDiffOn ℝ 1 (ScalarLinear.primitive h s) I.carrier := by
  rw [contDiffOn_one_iff_derivWithin I.isOpen.uniqueDiffOn]
  refine ⟨fun t ht => (ScalarLinear.primitive_deriv I.toTimeInterval hh hs ht).differentiableWithinAt,
    hh.congr ?_⟩
  intro t ht
  exact (ScalarLinear.primitive_deriv I.toTimeInterval hh hs ht).derivWithin
    (I.isOpen.uniqueDiffOn t ht)

lemma exponentialPrimitive_hasDerivAt (I : OpenTimeInterval) {h : ℝ → ℝ}
    (hh : ContinuousOn h I.carrier) {s t : ℝ} (hs : s ∈ I.carrier)
    (ht : t ∈ I.carrier) :
    HasDerivAt (exponentialPrimitive h s) (exponentialPrimitive h s t * h t) t := by
  exact ((ScalarLinear.primitive_deriv I.toTimeInterval hh hs ht).hasDerivAt
    (I.isOpen.mem_nhds ht)).exp

lemma exponentialPrimitive_contDiffOn (I : OpenTimeInterval) {h : ℝ → ℝ}
    (hh : ContinuousOn h I.carrier) {s : ℝ} (hs : s ∈ I.carrier) :
    ContDiffOn ℝ 1 (exponentialPrimitive h s) I.carrier :=
  (primitive_contDiffOn I hh hs).exp

theorem time_factor : timeFactorExpected := by
  intro I J P Q h hP hQ hQ0 hratio s hs
  obtain ⟨ξ, hξ⟩ := J.nonempty
  have hc : ContinuousOn (fun p => (statePartial P p - timePartial Q p) / Q p)
      (I.carrier ×ˢ J.carrier) :=
    ((ExactRectangle.statePartial_continuousOn hP).sub
      (ExactRectangle.timePartial_continuousOn hQ)).div hQ.continuousOn hQ0
  have hh : ContinuousOn h I.carrier :=
    (ExactRectangle.continuousOn_time_slice hc hξ).congr
      (fun t ht => (hratio (t, ξ) ⟨ht, hξ⟩).symm)
  have hm : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => exponentialPrimitive h s p.1)
      (I.carrier ×ˢ J.carrier) :=
    (exponentialPrimitive_contDiffOn I hh hs).comp contDiffOn_fst (fun _ hp => hp.1)
  refine ⟨hm, fun p _ => Real.exp_ne_zero _, ?_⟩
  rintro ⟨t, x⟩ hp
  have hstate := (ExactRectangle.hasDerivAt_state (hm.mul hP) hp.1 hp.2).unique
    ((hasDerivAt_const x (exponentialPrimitive h s t)).mul
      (ExactRectangle.hasDerivAt_state hP hp.1 hp.2))
  have htime := (ExactRectangle.hasDerivAt_time (hm.mul hQ) hp.1 hp.2).unique
    ((exponentialPrimitive_hasDerivAt I hh hs hp.1).mul
      (ExactRectangle.hasDerivAt_time hQ hp.1 hp.2))
  simp only [zero_mul, zero_add] at hstate
  rw [hstate, htime]
  have hr := (div_eq_iff (hQ0 (t, x) hp)).mp (hratio (t, x) hp)
  dsimp only at hr ⊢
  linear_combination exponentialPrimitive h s t * hr

theorem state_factor : stateFactorExpected := by
  intro I J P Q k hP hQ hP0 hratio ξ hξ
  obtain ⟨s, hs⟩ := I.nonempty
  have hc : ContinuousOn (fun p => (timePartial Q p - statePartial P p) / P p)
      (I.carrier ×ˢ J.carrier) :=
    ((ExactRectangle.timePartial_continuousOn hQ).sub
      (ExactRectangle.statePartial_continuousOn hP)).div hP.continuousOn hP0
  have hk : ContinuousOn k J.carrier :=
    (ExactRectangle.continuousOn_state_slice hc hs).congr
      (fun x hx => (hratio (s, x) ⟨hs, hx⟩).symm)
  have hm : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => exponentialPrimitive k ξ p.2)
      (I.carrier ×ˢ J.carrier) :=
    (exponentialPrimitive_contDiffOn J hk hξ).comp contDiffOn_snd (fun _ hp => hp.2)
  refine ⟨hm, fun p _ => Real.exp_ne_zero _, ?_⟩
  rintro ⟨t, x⟩ hp
  have hstate := (ExactRectangle.hasDerivAt_state (hm.mul hP) hp.1 hp.2).unique
    ((exponentialPrimitive_hasDerivAt J hk hξ hp.2).mul
      (ExactRectangle.hasDerivAt_state hP hp.1 hp.2))
  have htime := (ExactRectangle.hasDerivAt_time (hm.mul hQ) hp.1 hp.2).unique
    ((hasDerivAt_const t (exponentialPrimitive k ξ x)).mul
      (ExactRectangle.hasDerivAt_time hQ hp.1 hp.2))
  simp only [zero_mul, zero_add] at htime
  rw [hstate, htime]
  have hr := (div_eq_iff (hP0 (t, x) hp)).mp (hratio (t, x) hp)
  dsimp only at hr ⊢
  linear_combination -exponentialPrimitive k ξ x * hr

end D13Unified.IntegratingFactors
