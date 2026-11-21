import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.CompactEscape
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.Continuation
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D13Unified.Ch04.CompactEscape
universe u
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch04.CompactEscape
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At any finite missing endpoint approached within its domain, a maximal
solution eventually escapes each compact subset of the original domain.
The filter formulation treats both time orientations with the same argument. -/
lemma maximal_compact_escape [FiniteDimensional ℝ E] (F : ODE E)
    (hF : F.LocallyLipschitzInState) (x : Solution F) (hmax : IsMaximal x)
    (c : ℝ) (hc : c ∉ x.interval.carrier) (l : Filter ℝ) [l.IsCountablyGenerated]
    (hl : Tendsto id l (𝓝 c)) (hmem : x.interval.carrier ∈ l)
    (K : Set (ℝ × E)) (hK : IsCompact K) (hKU : K ⊆ F.domain) :
    ∀ᶠ t in l, (t, x.representative t) ∉ K := by
  by_contra h
  have hfreq : ∃ᶠ t in l, (t, x.representative t) ∈ K := by
    simpa only [Filter.Frequently, not_not] using h
  obtain ⟨t, htlim, ht⟩ := exists_seq_forall_of_frequently (hfreq.and_eventually hmem)
  obtain ⟨p, hpK, φ, hφ, hconv⟩ := hK.tendsto_subseq (fun j => (ht j).1)
  have htime : Tendsto (t ∘ φ) atTop (𝓝 c) := (hl.comp htlim).comp hφ.tendsto_atTop
  have htime' : Tendsto (t ∘ φ) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hconv
  have hpc : p.1 = c := tendsto_nhds_unique htime' htime
  have hconv' : Tendsto (fun j => (t (φ j), x.representative (t (φ j))))
      atTop (𝓝 (c, p.2)) := by simpa only [← hpc, Function.comp_def, Prod.eta] using hconv
  have hpU : (c, p.2) ∈ F.domain := by simpa only [← hpc] using hKU hpK
  obtain ⟨J, y, hcJ, hy, heq, _⟩ := Continuation.cluster_local_solution F hF
    x.interval x.representative x.isSolution c p.2 hpU (t ∘ φ)
    (fun j => (ht (φ j)).2) hconv'
  have hJmem : J.carrier ∈ l := hl.eventually (J.isOpen.mem_nhds hcJ)
  have hmeet : (x.interval.carrier ∩ J.carrier).Nonempty := by
    have : l.NeBot := htlim.neBot
    exact Filter.nonempty_of_mem (inter_mem hmem hJmem)
  let U : OpenTimeInterval := ⟨x.interval.toTimeInterval.union J.toTimeInterval hmeet,
    x.interval.isOpen.union J.isOpen⟩
  let z : Solution F := ⟨U, pasteCurves x.interval.carrier x.representative y,
    classical_pasting F x.interval J x.representative y hmeet x.isSolution hy heq⟩
  apply hmax
  refine ⟨z, ⟨subset_union_left, (pasteCurves_eqOn heq).1⟩, ?_⟩
  apply ssubset_iff_subset_ne.mpr
  refine ⟨subset_union_left, ?_⟩
  intro he
  exact hc (he.symm ▸ (show c ∈ z.interval.carrier from Or.inr hcJ))

/-- Escape to the right, expressed by an actual time threshold. -/
theorem right_escape : rightEscapeExpected.{u} := by
  intro E _ _ _ F hF s ξ hs b hb K hK hKU
  obtain ⟨hx, hsi, hξ, hmax, hend, _⟩ := ODE.canonical_solution F hF s ξ hs
  have hI : (maximalIntervalValue F s ξ).carrier =
      {t : ℝ | lowerEndpointValue F s ξ < (t : EReal) ∧ t < b} := by
    have hi : (maximalIntervalValue F s ξ).carrier =
        {t : ℝ | lowerEndpointValue F s ξ < (t : EReal) ∧
          (t : EReal) < upperEndpointValue F s ξ} := hend.2.2
    simpa only [hb, EReal.coe_lt_coe_iff] using hi
  have hbI : b ∉ (maximalIntervalValue F s ξ).carrier := by
    rw [hI]; simp only [mem_ofPred_eq, lt_self_iff_false, and_false, not_false_eq_true]
  have hmem := Continuation.right_eventually_mem _ _ b hI
  have he := maximal_compact_escape F hF
    ⟨maximalIntervalValue F s ξ, solutionCurveValue F s ξ, hx⟩ hmax b hbI
    (𝓝[<] b) nhdsWithin_le_nhds hmem K hK hKU
  have hv : ∀ᶠ t in 𝓝[<] b, (t, solutionValueValue F t s ξ) ∉ K := by
    filter_upwards [he, hmem] with t ht htI
    rw [(ODE.solutionValue_on_domain F hF t s ξ ⟨hs, htI⟩).1]
    exact ht
  exact mem_nhdsLT_iff_exists_Ioo_subset.mp hv

/-- Escape to the left, with the time inequalities reversed. -/
theorem left_escape : leftEscapeExpected.{u} := by
  intro E _ _ _ F hF s ξ hs a ha K hK hKU
  obtain ⟨hx, hsi, hξ, hmax, hend, _⟩ := ODE.canonical_solution F hF s ξ hs
  have hI : (maximalIntervalValue F s ξ).carrier =
      {t : ℝ | a < t ∧ (t : EReal) < upperEndpointValue F s ξ} := by
    have hi : (maximalIntervalValue F s ξ).carrier =
        {t : ℝ | lowerEndpointValue F s ξ < (t : EReal) ∧
          (t : EReal) < upperEndpointValue F s ξ} := hend.2.2
    simpa only [ha, EReal.coe_lt_coe_iff] using hi
  have haI : a ∉ (maximalIntervalValue F s ξ).carrier := by
    rw [hI]; simp only [mem_ofPred_eq, lt_self_iff_false, false_and, not_false_eq_true]
  have hmem := Continuation.left_eventually_mem _ a _ hI
  have he := maximal_compact_escape F hF
    ⟨maximalIntervalValue F s ξ, solutionCurveValue F s ξ, hx⟩ hmax a haI
    (𝓝[>] a) nhdsWithin_le_nhds hmem K hK hKU
  have hv : ∀ᶠ t in 𝓝[>] a, (t, solutionValueValue F t s ξ) ∉ K := by
    filter_upwards [he, hmem] with t ht htI
    rw [(ODE.solutionValue_on_domain F hF t s ξ ⟨hs, htI⟩).1]
    exact ht
  exact mem_nhdsGT_iff_exists_Ioo_subset.mp hv

/-- In the full time-state space escape is a full limit to infinity. -/
theorem right_norm_limit : rightNormLimitExpected.{u} := by
  intro E _ _ _ F hF hU s ξ hs b hb
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨τ, hτ, hesc⟩ := right_escape F hF s ξ hs b hb
    (Icc (b - 1) b ×ˢ closedBall (0 : E) R)
    (isCompact_Icc.prod (isCompact_closedBall 0 R)) (by rw [hU]; exact subset_univ _)
  filter_upwards [Ioo_mem_nhdsLT hτ, Ioo_mem_nhdsLT (show b - 1 < b by linarith)]
    with t ht ht'
  have hn : ¬ ‖solutionValueValue F t s ξ‖ ≤ R := by
    intro hn
    exact hesc t ht ⟨⟨ht'.1.le, ht'.2.le⟩, by simpa only [mem_closedBall, dist_zero_right] using hn⟩
  exact (lt_of_not_ge hn).le

/-- The corresponding full norm limit at the finite left endpoint. -/
theorem left_norm_limit : leftNormLimitExpected.{u} := by
  intro E _ _ _ F hF hU s ξ hs a ha
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨τ, hτ, hesc⟩ := left_escape F hF s ξ hs a ha
    (Icc a (a + 1) ×ˢ closedBall (0 : E) R)
    (isCompact_Icc.prod (isCompact_closedBall 0 R)) (by rw [hU]; exact subset_univ _)
  filter_upwards [Ioo_mem_nhdsGT hτ, Ioo_mem_nhdsGT (show a < a + 1 by linarith)]
    with t ht ht'
  have hn : ¬ ‖solutionValueValue F t s ξ‖ ≤ R := by
    intro hn
    exact hesc t ht ⟨⟨ht'.1.le, ht'.2.le⟩, by simpa only [mem_closedBall, dist_zero_right] using hn⟩
  exact (lt_of_not_ge hn).le

end D13Unified.Ch04.CompactEscape
