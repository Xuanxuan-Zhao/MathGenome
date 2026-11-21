import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.PrimalWeakMetrizable
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13ConverseMetric
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.DoubleDual

namespace ExpandedFA.P1.PrimalWeakMetrizable
universe u v
open Topology TopologicalSpace Filter
noncomputable section

/-- Extending the restriction to a common kernel approximates a functional
by the span of the finite tests, with the same error bound. -/
lemma approximate_by_finite_tests {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s : Finset (E →L[𝕜] 𝕜)) (g : E →L[𝕜] 𝕜) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ∀ x : E, ‖x‖ ≤ 1 → (∀ f ∈ s, f x = 0) → ‖g x‖ ≤ ε) :
    ∃ f ∈ Submodule.span 𝕜 (s : Set (E →L[𝕜] 𝕜)), ‖g - f‖ ≤ ε := by
  classical
  let M : Submodule 𝕜 E := ⨅ f : s, (f.val : E →ₗ[𝕜] 𝕜).ker
  let r : M →L[𝕜] 𝕜 := g.comp M.subtypeL
  have hr : ‖r‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
    intro x hx
    apply hsmall x (by simpa using hx.le)
    intro f hf
    exact ((Submodule.mem_iInf _).mp x.property ⟨f, hf⟩)
  obtain ⟨G, hG, hGn⟩ := C05NormExtension.norm_preserving_extension 𝕜 E M r
  have hker : (⨅ f : s, (f.val : E →ₗ[𝕜] 𝕜).ker) ≤
      (g - G).toLinearMap.ker := by
    intro x hx
    change g x - G x = 0
    exact sub_eq_zero.mpr (hG ⟨x, hx⟩).symm
  have halg := mem_span_of_iInf_ker_le_ker hker
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp halg
  let f : E →L[𝕜] 𝕜 := ∑ i : s, c i • i.val
  have hf : f = g - G := by
    ext x
    have hh := congrArg (fun l : E →ₗ[𝕜] 𝕜 => l x) hc
    simpa [f] using hh
  refine ⟨f, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span i.property))
  · rw [hf, sub_sub_cancel, hGn]
    exact hr

/-- A metrizable relative weak ball supplies countably many finite tests
which approximate every functional in operator norm. -/
theorem separable_dual_of_primal_ball_metrizable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hm : Spec.PrimalBallMetrizable 𝕜 E) : SeparableSpace (E →L[𝕜] 𝕜) := by
  classical
  let B := Metric.closedBall (0 : E) 1
  have hb : (@nhds B (TopologicalSpace.induced Subtype.val
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))) ⟨0, by simp [B]⟩).HasBasis
      (fun p : Finset (E →L[𝕜] 𝕜) × ℝ => 0 < p.2)
      (fun p => {x : B | ∀ f ∈ p.1, ‖f x.val‖ < p.2}) := by
    rw [@nhds_induced E B
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      Subtype.val ⟨0, by simp [B]⟩]
    simpa [C12DualPairSpec.PairNeighborhoodValue] using
      (dualPairTopology_nhds_basis 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) 0).comap
        (Subtype.val : B → E)
  let tB := TopologicalSpace.induced (Subtype.val : B → E)
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
  let : TopologicalSpace B := tB
  let : MetrizableSpace B := hm
  obtain ⟨p, hp, hb'⟩ := hb.exists_antitone_subbasis
  let D : Set (E →L[𝕜] 𝕜) := ⋃ n : ℕ, (p n).1
  have hD : D.Countable := Set.countable_iUnion (fun n => (p n).1.countable_toSet)
  let F := (Submodule.span 𝕜 D).topologicalClosure
  have hF : F = ⊤ := by
    apply top_unique
    intro g _
    change g ∈ closure (Submodule.span 𝕜 D : Set (E →L[𝕜] 𝕜))
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hU : {x : B | ‖g x.val‖ < ε / 2} ∈
        @nhds B tB ⟨0, by simp [B]⟩ := by
      have hcont : @Continuous B 𝕜 tB inferInstance (fun x => g x.val) := by
        rw [continuous_iff_le_induced]
        dsimp only [tB]
        rw [dualPairTopology_evaluation 𝕜 E, induced_iInf]
        simpa only [induced_compose, Function.comp_def] using
          (iInf_le (fun f : E →L[𝕜] 𝕜 =>
            TopologicalSpace.induced (Subtype.val : B → E)
              (TopologicalSpace.induced (fun x : E => f x) inferInstance)) g)
      exact (isOpen_lt hcont.norm continuous_const).mem_nhds (by simpa using half_pos hε)
    obtain ⟨n, _, hn⟩ := hb'.1.mem_iff.mp hU
    obtain ⟨f, hf, hgf⟩ := approximate_by_finite_tests (p n).1 g (ε / 2)
      (half_pos hε).le (by
        intro x hx hvan
        have hbnd : x ∈ B := by simpa [B] using hx
        have htests : (⟨x, hbnd⟩ : B) ∈ {x : B | ∀ f ∈ (p n).1, ‖f x.val‖ < (p n).2} := by
          intro f hf
          simpa [hvan f hf] using hp n
        exact (hn htests).le)
    refine ⟨f, ?_, ?_⟩
    · apply Submodule.span_mono _ hf
      intro f hf
      exact Set.mem_iUnion.mpr ⟨n, hf⟩
    · simpa only [dist_eq_norm, norm_sub_rev] using hgf.trans_lt (half_lt_self hε)
  have hs : IsSeparable (F : Set (E →L[𝕜] 𝕜)) := hD.isSeparable.span.closure
  rw [hF, Submodule.top_coe] at hs
  exact isSeparable_univ_iff.mp hs

/-- The canonical evaluation embeds the weak primal ball in the weak-star
bidual ball. Metrizability of that ball follows from separability of E′. -/
theorem primal_ball_metrizable_of_separable_dual (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hsep : SeparableSpace (E →L[𝕜] 𝕜)) : Spec.PrimalBallMetrizable 𝕜 E := by
  let B := Metric.closedBall (0 : E) 1
  let BB := Metric.closedBall (0 : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) 1
  let j : B → BB := fun x => ⟨NormedSpace.inclusionInDoubleDual 𝕜 E x.val, by
    have hx : ‖x.val‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    exact (mem_closedBall_zero_iff (E := (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)).mpr
      ((NormedSpace.double_dual_bound 𝕜 E x.val).trans hx)⟩
  let tB := TopologicalSpace.induced (Subtype.val : B → E)
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
  let tBB := TopologicalSpace.induced
    (Subtype.val : BB → (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
  let : TopologicalSpace B := tB
  let : TopologicalSpace BB := tBB
  have hm : C13ConverseMetric.Spec.BallMetrizable 𝕜 (E →L[𝕜] 𝕜) :=
    (C13ConverseMetric.dual_ball_weakStar_metrizable_iff_separable 𝕜 (E →L[𝕜] 𝕜)).mpr hsep
  let : MetrizableSpace BB := hm
  have hj : IsEmbedding j := by
    refine ⟨⟨?topologyEquality⟩, ?injectivity⟩
    case topologyEquality =>
      change tB = TopologicalSpace.induced j tBB
      dsimp only [tB, tBB]
      rw [induced_compose, C12WeakStar.weakStarTopology_evaluations,
        induced_iInf, dualPairTopology_evaluation, induced_iInf]
      simp only [induced_compose]
      rfl
    case injectivity =>
      intro x y h
      apply Subtype.ext
      exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := E)).injective
        (congrArg Subtype.val h)
  exact hj.metrizableSpace

/-- The weak topology of the primal closed unit ball is metrizable exactly
when the continuous scalar-linear dual is separable in operator norm. -/
theorem primal_ball_weak_metrizable_iff_separable_dual : Spec.PrimalCharacterization := by
  intro 𝕜 E _ _ _
  exact ⟨separable_dual_of_primal_ball_metrizable 𝕜 E,
    primal_ball_metrizable_of_separable_dual 𝕜 E⟩

/-- The second equivalence in the proposition uses the specified predual E. -/
theorem dual_ball_weakStar_metrizable_iff_separable : Spec.DualCharacterization :=
  C13ConverseMetric.dual_ball_weakStar_metrizable_iff_separable

end
end ExpandedFA.P1.PrimalWeakMetrizable
