import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.IntegralFormulation

/-! Differential and oriented integral formulations on arbitrary real intervals.
The FTC filter used below stays within the actual interval; no continuity of
the zero extension of the vector field outside its domain is asserted.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace D13Unified

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- FTC-1 relative to an arbitrary real interval, including included endpoints
and the degenerate interval. -/
theorem hasDerivWithinAt_integral_on_interval [CompleteSpace E]
    {J : Set ℝ} (hJ : OrdConnected J) {g : ℝ → E}
    (hg : ContinuousOn g J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    HasDerivWithinAt (fun u => ∫ r in s..u, g r) (g t) J t := by
  have : OrdConnected J := hJ
  have : (𝓝[J] t).IsMeasurablyGenerated :=
    hJ.measurableSet.nhdsWithin_isMeasurablyGenerated t
  have : TendstoIxxClass Icc (𝓝[J] t) (𝓝[J] t) :=
    tendstoIxxClass_inf
  have : TendstoIxxClass Ioc (𝓝[J] t) (𝓝[J] t) :=
    tendstoIxxClass_of_subset (fun _ _ => Ioc_subset_Icc_self)
  have : intervalIntegral.FTCFilter t (𝓝[J] t) (𝓝[J] t) :=
    { pure_le := pure_le_nhdsWithin ht
      le_nhds := nhdsWithin_le_nhds }
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hg.mono (hJ.uIcc_subset hs ht)).intervalIntegrable)
    (hg.stronglyMeasurableAtFilter_nhdsWithin hJ.measurableSet t) (hg t ht)

/-- FTC-2 with the derivative specified relative to the actual interval. -/
theorem integral_eq_sub_on_interval [CompleteSpace E]
    {J : Set ℝ} (hJ : OrdConnected J) {x g : ℝ → E}
    (hx : ContinuousOn x J) (hg : ContinuousOn g J)
    (hd : ∀ t ∈ J, HasDerivWithinAt x (g t) J t)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    ∫ r in s..t, g r = x t - x s := by
  have hsub := hJ.uIcc_subset hs ht
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right (hx.mono hsub) _
    ((hg.mono hsub).intervalIntegrable)
  intro r hr
  have hrJ : r ∈ J := hsub (mem_Icc_of_Ioo hr)
  have hlocal : J ∈ 𝓝 r :=
    mem_of_superset (Ioo_mem_nhds hr.1 hr.2)
      (Ioo_subset_Icc_self.trans hsub)
  exact ((hd r hrJ).hasDerivAt hlocal).hasDerivWithinAt

variable [FiniteDimensional ℝ E]

/-- The full IVP is equivalent to the oriented integral equation, on any
nonempty real interval and for any included base time. -/
theorem ivp_iff_integral (F : ODE E) (I : TimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E) (hs : s ∈ I.carrier)
    (hx : ContinuousOn x I.carrier)
    (hgraph : ∀ t ∈ I.carrier, (t, x t) ∈ F.domain) :
    IsIVPOn F I x s ξ ↔
      ∀ t ∈ I.carrier, x t = ξ + ∫ r in s..t, F.eval r (x r) := by
  have hg : ContinuousOn (fun r => F.eval r (x r)) I.carrier :=
    F.continuousOn_eval.comp (continuousOn_id.prodMk hx) hgraph
  constructor
  · intro h t ht
    have hi := integral_eq_sub_on_interval I.ordConnected hx hg h.1.2.2 hs ht
    rw [hi, h.2.2]
    exact (add_sub_cancel ξ (x t)).symm
  · intro h
    refine ⟨⟨hx, hgraph, ?_⟩, hs, ?_⟩
    · intro t ht
      have hd := (hasDerivWithinAt_integral_on_interval I.ordConnected hg hs ht).const_add ξ
      exact hd.congr_of_mem (fun r hr => h r hr) ht
    · simpa only [intervalIntegral.integral_same, add_zero] using h s hs

/-- The integral equation also yields C¹ regularity and ordinary derivatives
when the actual interval is open. -/
theorem classicalIVP_iff_integral (F : ODE E) (I : OpenTimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E) (hs : s ∈ I.carrier)
    (hx : ContinuousOn x I.carrier)
    (hgraph : ∀ t ∈ I.carrier, (t, x t) ∈ F.domain) :
    IsClassicalIVPOn F I x s ξ ↔
      ∀ t ∈ I.carrier, x t = ξ + ∫ r in s..t, F.eval r (x r) := by
  change (Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue F I x ∧
    s ∈ I.carrier ∧ x s = ξ) ↔ _
  rw [classical_iff_solutionOn F I x]
  exact ivp_iff_integral F I.toTimeInterval x s ξ hs hx hgraph

end D13Unified
