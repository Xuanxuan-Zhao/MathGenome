import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.DomainBoundaryExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum

/-! The bounded maximal solution x(t)=t for the field 1 on ℝ × (-1,1).
The domain restriction, rather than growth of the state norm, prevents extension.
-/
noncomputable section
open Set Filter
open scoped Topology
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.DomainBoundaryExample

namespace D13Unified.Ch04.DomainBoundaryExample

private lemma boundary_eval {t x : ℝ} (hx : (t, x) ∈ boundaryODE.domain) :
    boundaryODE.eval t x = 1 := boundaryODE.eval_of_mem hx

/-- The identity is a classical solution with the required initial data. -/
theorem solution : solutionExpected := by
  refine ⟨⟨contDiff_id.contDiffOn, ?_, ?_⟩, ?_, rfl⟩
  · intro t ht; exact ht
  · intro t ht
    have hg : (t, id t) ∈ boundaryODE.domain := ht
    rw [boundary_eval hg]
    exact hasDerivAt_id t
  · exact ⟨by norm_num, by norm_num⟩

/-- Equality of derivatives on the actual open interval and the value at zero
 force every competing solution to have exactly the identity's values. -/
theorem restriction : restrictionExpected := by
  intro J x hx
  have hd (t : ℝ) (ht : t ∈ J.carrier) : HasDerivAt x 1 t := by
    simpa only [boundary_eval (hx.1.2.1 t ht)] using hx.1.2.2 t ht
  have he : EqOn x id J.carrier := J.isOpen.eqOn_of_deriv_eq
    J.ordConnected.isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    differentiable_id.differentiableOn
    (fun t ht => by rw [(hd t ht).deriv, (hasDerivAt_id t).deriv])
    hx.2.1 hx.2.2
  refine ⟨?_, he⟩
  intro t ht
  have hg := hx.1.2.1 t ht
  change x t ∈ Ioo (-1 : ℝ) 1 at hg
  change t ∈ Ioo (-1 : ℝ) 1
  simpa only [he ht, id_eq] using hg

/-- No solution through zero can extend the identity beyond (-1,1), and any
 proper restriction admits the identity as a strict extension. -/
theorem maximal : maximalExpected := by
  intro x h0 hx0
  obtain ⟨hsub, heq⟩ := restriction x.interval x.representative ⟨x.isSolution, h0, hx0⟩
  let X : Solution boundaryODE := ⟨boundaryInterval, id, solution.1⟩
  constructor
  · intro hm
    refine ⟨?_, heq⟩
    by_contra hne
    exact hm ⟨X, ⟨hsub, heq.symm⟩, ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩⟩
  · rintro ⟨hdom, _⟩ y
    obtain ⟨y, hxy, hstrict⟩ := y
    have hy0 : y.representative 0 = 0 := (hxy.2 h0).trans hx0
    have hy := (restriction y.interval y.representative
      ⟨y.isSolution, hxy.1 h0, hy0⟩).1
    exact hstrict.not_subset (hdom.symm ▸ hy)

/-- An actual maximal solution exists with precisely the stated domain and values. -/
theorem maximal_solution : maximalSolutionExpected := by
  let X : Solution boundaryODE := ⟨boundaryInterval, id, solution.1⟩
  refine ⟨X, rfl, (fun _ _ => rfl), rfl, solution.2.1, ?_⟩
  exact (maximal X solution.2.1 rfl).mpr ⟨rfl, fun _ _ => rfl⟩

/-- The state stays bounded and no such solution has domain ℝ. -/
theorem bounded_not_global : boundedNotGlobalExpected := by
  intro J x hx
  obtain ⟨hsub, heq⟩ := restriction J x hx
  constructor
  · intro t ht
    exact Real.norm_eq_abs (x t) ▸ abs_lt.mpr (hx.1.2.1 t ht)
  · intro hglobal
    have h1 := hsub (hglobal ▸ (show (1 : ℝ) ∈ univ from mem_univ _))
    exact (lt_irrefl (1 : ℝ)) h1.2

/-- The finite endpoint limits reach the excluded states 1 and -1. -/
theorem boundary_limits : boundaryLimitsExpected := by
  exact ⟨nhdsWithin_le_nhds, nhdsWithin_le_nhds, by simp [boundaryODE],
    by simp [boundaryODE]⟩

/-- A compact subset is closed and misses both endpoint graph limits, so its
 complement contains a whole final portion at each end of the graph. -/
theorem compact_escape : compactEscapeExpected := by
  intro K hK hKU
  have hout (c : ℝ) (hc : (c, c) ∉ boundaryODE.domain) :
      ∀ᶠ t in 𝓝 c, (t, t) ∉ K :=
    ((continuous_id.prodMk continuous_id).tendsto c).eventually
      (hK.isClosed.isOpen_compl.mem_nhds (fun hk => hc (hKU hk)))
  have hr : ∀ᶠ t in 𝓝[<] (1 : ℝ), (t, t) ∉ K :=
    (hout 1 boundary_limits.2.2.1).filter_mono nhdsWithin_le_nhds
  have hl : ∀ᶠ t in 𝓝[>] (-1 : ℝ), (t, t) ∉ K :=
    (hout (-1) boundary_limits.2.2.2).filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hr1, hr⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hr
  obtain ⟨l, hl1, hl⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hl
  constructor
  · refine ⟨max r 0, ⟨by exact lt_of_lt_of_le (by norm_num) (le_max_right r 0),
      max_lt hr1 (by norm_num)⟩, ?_⟩
    intro t ht
    exact hr ⟨lt_of_le_of_lt (le_max_left r 0) ht.1, ht.2⟩
  · refine ⟨min l 0, ⟨lt_min hl1 (by norm_num),
      lt_of_le_of_lt (min_le_right l 0) (by norm_num)⟩, ?_⟩
    intro t ht
    exact hl ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left l 0)⟩

/-- Globally extending the formula solves the full-domain ODE only. -/
theorem global_formula : globalFormulaExpected := by
  refine ⟨⟨⟨contDiff_id.contDiffOn, fun _ _ => mem_univ _, ?_⟩,
    mem_univ _, rfl⟩, boundary_limits.2.2.1, ?_⟩
  · intro t _
    rw [fullODE.eval_of_mem (mem_univ (t, id t))]
    exact hasDerivAt_id t
  · intro h
    exact boundary_limits.2.2.1 (h.1.2.1 1 (mem_univ _))

/-- The upstream canonical choice has this very interval and these values. -/
theorem canonical : canonicalExpected := by
  have hF : boundaryODE.LocallyLipschitzInState := by
    intro s ξ hs
    obtain ⟨b, hb, hB⟩ := Metric.isOpen_iff.mp
      (isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)) ξ hs
    have hbox : Metric.ball s 1 ×ˢ Metric.ball ξ b ⊆ boundaryODE.domain :=
      fun _ hp => hB hp.2
    refine ⟨1, b, 0, zero_lt_one, hb, le_rfl, hbox, ?_⟩
    intro t ht x hx y hy
    rw [boundary_eval (hbox ⟨ht, hx⟩), boundary_eval (hbox ⟨ht, hy⟩)]
    simp
  have hs : (0, 0) ∈ boundaryODE.domain := by constructor <;> norm_num
  obtain ⟨hx, h0, hx0, hm, _⟩ := ODE.canonical_solution boundaryODE hF 0 0 hs
  have hident := (maximal ⟨_, _, hx⟩ h0 hx0).mp hm
  refine ⟨hident.1, ?_⟩
  intro t ht
  have ht' : t ∈ (Specs.D13Unified.Ch04.MaximalSolutionMap.maximalIntervalValue
      boundaryODE 0 0).carrier := hident.1 ▸ ht
  exact (ODE.solutionValue_on_domain boundaryODE hF t 0 0 ⟨hs, ht'⟩).1.trans
    (hident.2 ht')

end D13Unified.Ch04.DomainBoundaryExample
