import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.WeakVariants.ProperBoundedDomains
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.WeakVariants.NormTotalTests
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08ClosedGraph
import Mathlib.Analysis.SpecificLimits.Normed

namespace ExpandedFA.WeakVariants.ProperBoundedDomains
universe u v w
open Filter
open scoped Topology ENNReal
noncomputable section

theorem norm_total_criterion : Spec.NormTotalCriterion.{u,v} :=
  NormTotalTests.norm_total_criterion

theorem separating_tests_insufficient : Spec.SeparatingTestsInsufficient.{u} :=
  NormTotalTests.coordinate_counterexample

theorem closed_domain_closed_graph : Spec.ClosedDomainClosedGraph.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ D T hD
  apply IsSeqClosed.isClosed
  intro z p hz hp
  choose d hd hT using hz
  change ∀ n, T (d n) = (z n).2 at hT
  have hx : Tendsto (fun n => (d n : X)) atTop (𝓝 p.1) := by
    simpa only [Function.comp_def, hd] using (continuous_fst.tendsto p).comp hp
  have hxD : p.1 ∈ D := hD.mem_of_tendsto hx (Eventually.of_forall fun n => (d n).property)
  have hsub : Tendsto d atTop (𝓝 (⟨p.1, hxD⟩ : D)) :=
    tendsto_subtype_rng.mpr hx
  refine ⟨⟨p.1, hxD⟩, rfl, ?_⟩
  apply tendsto_nhds_unique ((T.continuous.tendsto _).comp hsub)
  simpa only [Function.comp_def, hT] using (continuous_snd.tendsto p).comp hp

theorem closed_graph_closed_domain : Spec.ClosedGraphClosedDomain.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ D T hg
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨s, hs, hx⟩ := mem_closure_iff_seq_limit.mp hx
  let d : ℕ → D := fun n => ⟨s n, hs n⟩
  have hc : CauchySeq d := by
    simpa only [Metric.cauchySeq_iff, Subtype.dist_eq, d] using hx.cauchySeq
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (T.uniformContinuous.comp_cauchySeq hc)
  have hm : (x, y) ∈ ambientGraph D T.toLinearMap :=
    hg.mem_of_tendsto (hx.prodMk_nhds hy)
      (Eventually.of_forall fun n => ⟨d n, rfl, rfl⟩)
  obtain ⟨a, ha, _⟩ := hm
  exact (show (a : X) = x from ha) ▸ a.property

theorem proper_domain_closed_graph : Spec.ProperDomainClosedGraphTheorem.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ D T hD hg
  have : CompleteSpace D := hD.completeSpace_coe
  have hi : IsClosed (T.graph : Set (D × Y)) := by
    convert hg.preimage (continuous_subtype_val.prodMap continuous_id) using 1
    ext ⟨d, y⟩
    simp only [Set.mem_preimage, ambientGraph, Set.mem_ofPred_eq,
      Prod.map_apply, id_eq]
    constructor
    · intro h; exact ⟨d, rfl, h.symm⟩
    · rintro ⟨a, ha, hy⟩
      have : a = d := Subtype.ext ha
      change y = T d
      simpa only [this] using hy.symm
  obtain ⟨C, hC, hb⟩ := SemilinearMapClass.bound_of_continuous T
    (T.continuous_of_isClosed_graph hi)
  exact ⟨C, hC.le, hb⟩

theorem finite_support_identification : Spec.FiniteSupportIdentification.{u} := by
  intro 𝕜 _ x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.hasFiniteSupport
  · intro hx
    exact ⟨Finsupp.ofSupportFinite (fun n => x n) hx, lp.ext rfl⟩

/-- The graph of the identity into a subspace is closed, for every subspace. -/
theorem identity_graph_closed (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (D : Submodule 𝕜 X) :
    IsClosed (ambientGraph D (LinearMap.id : D →ₗ[𝕜] D)) := by
  have he : ambientGraph D (LinearMap.id : D →ₗ[𝕜] D) =
      {z : X × D | z.1 = (z.2 : X)} := by
    ext z
    constructor
    · rintro ⟨d, hd, ht⟩
      change d = z.2 at ht
      exact hd.symm.trans (congrArg Subtype.val ht)
    · intro h
      exact ⟨z.2, h.symm, rfl⟩
  rw [he]
  exact isClosed_eq continuous_fst (continuous_subtype_val.comp continuous_snd)

/-- Geometric coordinate-vector series produces an infinite-support limit
of finite-support vectors in the original ℓ² norm. -/
theorem finite_support_domain_not_closed (𝕜 : Type u) [RCLike 𝕜] :
    ¬ IsClosed (finiteSupportDomain 𝕜 : Set (lp (fun _ : ℕ => 𝕜) 2)) := by
  classical
  let a : ℕ → 𝕜 := fun n => (2 : 𝕜)⁻¹ ^ (n + 1)
  let f : ℕ → lp (fun _ : ℕ => 𝕜) 2 := fun n => lp.single 2 n (a n)
  have hf : Summable f := by
    apply Summable.of_norm
    simp_rw [f, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), a,
      norm_pow, norm_inv]
    have hg := summable_geometric_of_lt_one
      (show (0 : ℝ) ≤ ‖(2 : 𝕜)‖⁻¹ by positivity)
      (show ‖(2 : 𝕜)‖⁻¹ < 1 by norm_num)
    simpa only [pow_succ] using hg.mul_right (‖(2 : 𝕜)‖⁻¹)
  intro hclosed
  have hsingle (n : ℕ) : f n ∈ finiteSupportDomain 𝕜 := by
    refine ⟨Finsupp.single n (a n), ?_⟩
    apply lp.ext
    funext j
    change (Finsupp.single n (a n)) j = (lp.single (E := fun _ : ℕ => 𝕜) 2 n (a n)) j
    by_cases hj : j = n <;> simp [hj]
  have hmem : (∑' n, f n) ∈ finiteSupportDomain 𝕜 :=
    hclosed.mem_of_tendsto hf.hasSum.tendsto_sum_nat
      (Eventually.of_forall fun N => (finiteSupportDomain 𝕜).sum_mem
        fun n _ => hsingle n)
  have hcoord (n : ℕ) : (∑' j, f j) n = a n := by
    have he := (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 n).map_tsum hf
    change (∑' j, f j) n = ∑' j, f j n at he
    rw [he]
    rw [tsum_eq_single n]
    · simp [f]
    · intro j hj
      simp [f, lp.single_apply, Pi.single_eq_of_ne hj.symm]
  have hfinite := (finite_support_identification 𝕜 _).mp hmem
  have hall : Function.support (fun n => (∑' j, f j) n) = Set.univ := by
    ext n
    simp only [Function.mem_support, Set.mem_univ, iff_true, hcoord]
    exact pow_ne_zero _ (inv_ne_zero (by norm_num))
  rw [hall] at hfinite
  exact Set.infinite_univ hfinite

theorem incomplete_target_counterexample : Spec.IncompleteTargetCounterexample.{u} := by
  intro 𝕜 _
  dsimp only
  refine ⟨fun d => rfl, identity_graph_closed 𝕜 _ _,
    finite_support_domain_not_closed 𝕜, ?_⟩
  intro hc
  have : CompleteSpace (finiteSupportDomain 𝕜) := hc
  exact finite_support_domain_not_closed 𝕜
    (closed_graph_closed_domain 𝕜 _ _ (finiteSupportDomain 𝕜)
      (ContinuousLinearMap.id 𝕜 _) (identity_graph_closed 𝕜 _ _))

end
end ExpandedFA.WeakVariants.ProperBoundedDomains
