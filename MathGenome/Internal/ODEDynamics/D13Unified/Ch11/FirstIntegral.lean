import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.FirstIntegral
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import Mathlib.Analysis.Calculus.MeanValue

/-! First integrals on the actual maximal intervals, paper.tex d13:11:first-integral. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch11.FirstIntegral
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch11.FirstIntegral
open Ch06.StateDerivative
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chain rule on a solution's open interval; off-domain representatives do not
enter the derivative calculation. -/
lemma derivative_along_solution (F : AutonomousODE E) (H : E → ℝ)
    (hH : ContDiffOn ℝ 1 H F.domain) (I : OpenTimeInterval) (x : ℝ → E)
    (hx : classicalSolutionOnValue F.toODE I x) {t : ℝ} (ht : t ∈ I.carrier) :
    HasDerivAt (fun r => H (x r)) ((fderiv ℝ H (x t)) (F.eval (x t))) t := by
  have hmem : x t ∈ F.domain := hx.2.1 t ht
  have hdiff : DifferentiableAt ℝ H (x t) :=
    (hH.differentiableOn_one (x t) hmem).differentiableAt
      (F.isOpen_domain.mem_nhds hmem)
  simpa only [AutonomousODE.toODE_eval, Function.comp_def] using!
    hdiff.hasFDerivAt.comp_hasDerivAt t (hx.2.2 t ht)

/-- A zero derivative on the whole connected open interval gives equality for
any two of its times, regardless of their order or sign. -/
theorem conservation : Conservation.{u} := by
  intro E _ _ _ F _ H hH hzero I x hx s hs t ht
  have hd (r : ℝ) (hr : r ∈ I.carrier) :
      HasDerivAt (fun v => H (x v)) 0 r := by
    have h := derivative_along_solution F H hH I x hx hr
    exact h.congr_deriv (hzero (x r) (hx.2.1 r hr))
  exact I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) ht hs

theorem flow_first_integral_iff : FlowEquivalence.{u} := by
  intro E _ _ _ F hF H hH
  constructor
  · intro hc x hx
    have hX := flow_ivp F hF hx
    have hd := derivative_along_solution F H hH (flowInterval F x)
      (fun t => flow F t x) hX.1 hX.2.1
    have he : (fun t => H (flow F t x)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => H x) := by
      filter_upwards [(flowInterval F x).isOpen.mem_nhds hX.2.1] with t ht
      exact hc x hx t ht
    have hz : HasDerivAt (fun t => H (flow F t x)) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (H x)).congr_of_eventuallyEq he
    simpa only [hX.2.2] using! hd.unique hz
  · intro hzero x hx t ht
    have hX := flow_ivp F hF hx
    simpa only [hX.2.2] using
      conservation F hF H hH hzero (flowInterval F x)
        (fun r => flow F r x) hX.1 0 hX.2.1 t ht

theorem first_integral_iff : MaximalEquivalence.{u} := by
  intro E _ _ _ F hF H hH
  constructor
  · intro hc
    apply (flow_first_integral_iff F hF H hH).mp
    intro x hx t ht
    obtain ⟨hsol, h0, hvalue, hmax, _⟩ := ODE.canonical_solution F.toODE
      (F.locallyLipschitzInState_of_contDiffOn hF) 0 x hx
    let X : Solution F.toODE := ⟨flowInterval F x, fun r => flow F r x, hsol⟩
    have h := hc X hmax 0 h0 t ht
    change H (flow F t x) = H (flow F 0 x) at h
    have hvalue' : flow F 0 x = x := hvalue
    simpa only [hvalue'] using h
  · intro hzero x _ s hs t ht
    exact conservation F hF H hH hzero x.interval x.representative x.isSolution s hs t ht

end D13Unified.Ch11.FirstIntegral
