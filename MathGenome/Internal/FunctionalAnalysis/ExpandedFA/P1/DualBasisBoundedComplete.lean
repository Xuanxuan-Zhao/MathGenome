import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisBoundedComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBasisBasicity
import Mathlib.Analysis.Normed.Module.WeakDual

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.DualBasisBoundedComplete
open DualBasisBasicity
open ExpandedFA.P1.C15Basis.Spec (orderedPartialSum)

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Evaluation of a dual coefficient sum eventually recovers its coefficient. -/
theorem dual_sum_eval (b : SchauderBasis 𝕜 E) (a : ℕ → 𝕜) (N i : ℕ)
    (hi : i < N) :
    (orderedPartialSum (dualVector b) a N).val (b i) = a i := by
  classical
  simp [orderedPartialSum, dualVector, DualBasisBasicity.Spec.dualVector,
    b.ortho, Pi.single_apply, hi]

/-- A shrinking basis makes every bounded dual coefficient series converge. -/
theorem dual_boundedlyComplete_of_shrinking [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (h : IsShrinking b) : IsBoundedlyComplete (𝕜 := 𝕜) (dualVector b) := by
  intro a ha
  let s := orderedPartialSum (dualVector b) a
  let g : ℕ → E →L[𝕜] 𝕜 := fun N => (s N).val
  obtain ⟨C, hC⟩ := ha
  have hg (N : ℕ) : ‖g N‖ ≤ C := hC (Set.mem_range_self N)
  let w : ℕ → WeakDual 𝕜 E := fun N => StrongDual.toWeakDual (g N)
  have hmem : ∀ᶠ N in atTop,
      w N ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : E →L[𝕜] 𝕜) C := by
    apply Filter.Eventually.of_forall
    intro N
    change dist (g N) 0 ≤ C
    simpa only [dist_zero_right] using hg N
  obtain ⟨f, _, hf⟩ := (WeakDual.isCompact_closedBall (0 : E →L[𝕜] 𝕜) C).exists_mapClusterPt
    (Filter.tendsto_principal.mpr hmem)
  have hc (i : ℕ) : WeakDual.toStrongDual f (b i) = a i := by
    have he := hf.continuousAt_comp (WeakDual.eval_continuous (b i)).continuousAt
    apply isClosed_singleton.mem_of_mapClusterPt he
    filter_upwards [eventually_gt_atTop i] with N hN
    exact dual_sum_eval b a N i hN
  have hm : WeakDual.toStrongDual f ∈ dualSpan b :=
    (shrinking_iff_dualSpan b).mp h ▸ Submodule.mem_top
  refine ⟨⟨WeakDual.toStrongDual f, hm⟩, tendsto_subtype_rng.mpr ?_⟩
  have ht := h (WeakDual.toStrongDual f)
  simpa only [← dualProjection_apply, dualProjection_eq_sum, hc,
    s, g, orderedPartialSum, Submodule.coe_sum, Submodule.coe_smul,
    DualBasisBasicity.Spec.dualVector, dualVector] using ht

/-- Bounded completeness forces every functional into the coordinate closed span. -/
theorem shrinking_of_dual_boundedlyComplete [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (h : IsBoundedlyComplete (𝕜 := 𝕜) (dualVector b)) : IsShrinking b := by
  apply (shrinking_iff_dualSpan b).mpr
  apply eq_top_iff.mpr
  intro f _
  let a : ℕ → 𝕜 := fun i => f (b i)
  let s := orderedPartialSum (dualVector b) a
  have he (N : ℕ) : (s N).val = f.comp (b.proj N) := by
    simpa only [s, a, orderedPartialSum, Submodule.coe_sum, Submodule.coe_smul,
      DualBasisBasicity.Spec.dualVector, dualVector, dualProjection_apply] using
      (dualProjection_eq_sum b N f).symm
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hb : BddAbove (Set.range fun N => ‖s N‖) := by
    refine ⟨‖f‖ * C, ?_⟩
    rintro _ ⟨N, rfl⟩
    change ‖(s N).val‖ ≤ ‖f‖ * C
    rw [he]
    exact (f.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hC N) (norm_nonneg f))
  obtain ⟨x, hx⟩ := h a hb
  have hxval : x.val = f := by
    ext y
    have ht := ((ContinuousLinearMap.apply 𝕜 𝕜 y).continuous.comp
      continuous_subtype_val).tendsto x |>.comp hx
    have ht' := f.continuous.tendsto y |>.comp (b.tendsto_proj y)
    have ht'' : Tendsto (fun N => (s N).val y) atTop (𝓝 (f y)) := by
      simpa only [he, ContinuousLinearMap.comp_apply, Function.comp_def] using ht'
    exact tendsto_nhds_unique ht ht''
  exact hxval ▸ x.property

/-- Assertion 1: bounded completeness of the dual basis iff shrinking. -/
theorem dual_boundedlyComplete_iff_shrinking : Spec.DualBoundedCompleteIffShrinking := by
  intro 𝕜 E _ _ _ _ b
  exact ⟨shrinking_of_dual_boundedlyComplete b, dual_boundedlyComplete_of_shrinking b⟩

/-- Recover the assertion under the manuscript's original expansion hypothesis. -/
theorem raw_dual_boundedlyComplete_iff_shrinking :
    Spec.RawDualBoundedCompleteIffShrinking := by
  intro 𝕜 E _ _ _ _ e h
  obtain ⟨b, he, hc, _⟩ := C15CoordinateContinuity.raw_native_basis h
  exact ⟨b, he, hc, dual_boundedlyComplete_iff_shrinking b⟩

/-- Finite coefficient sums stabilize, so both sides hold even for d = 0. -/
theorem finite_dual_boundedlyComplete_iff_shrinking :
    Spec.FiniteDualBoundedCompleteIffShrinking := by
  intro 𝕜 E _ _ _ d b
  classical
  dsimp only
  have hs (N : ℕ) (hN : d ≤ N) :
      Finset.univ.filter (fun i : Fin d => i.val < N) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact i.isLt.trans_le hN
  constructor
  · intro _ f
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    exact ((finite_dual_facts b).2.2.1 f N hN).symm
  · intro _ a _
    refine ⟨∑ i, a i • (⟨b.coord i, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self i))⟩ :
        (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure),
      tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop d] with N hN
    rw [hs N hN]

end ExpandedFA.P1.DualBasisBoundedComplete
