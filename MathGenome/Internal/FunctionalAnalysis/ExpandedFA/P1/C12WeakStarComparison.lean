import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStarComparison
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12InitialProperties
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04CanonicalMap

/-!
The scalar-test characterization puts each weak-star continuous functional
in the algebraic span of evaluations. Evaluations are the range of a linear
map from E, hence already form a submodule. Separation by the original norm
dual gives uniqueness. The two initial topologies then coincide precisely
when every norm-continuous bidual test is an evaluation.
-/

namespace ExpandedFA.P1.C12WeakStarComparison

universe u v
noncomputable section

theorem weakStar_continuous_iff_unique_evaluation :
    Spec.ContinuousEvaluation.{u, v} := by
  intro 𝕜 E _ _ _ g
  rw [← C12WeakStar.weakStarTopology_dualPair 𝕜 E,
    C12InitialProperties.pairing_continuous_iff_mem_span
      𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip g]
  constructor
  · intro hg
    have hr : g ∈ (topDualPairing 𝕜 E).flip.range := by
      simpa only [← LinearMap.coe_range, Submodule.span_eq] using hg
    obtain ⟨x, hx⟩ := hr
    refine ⟨x, ?_, ?_⟩
    · intro f
      exact (LinearMap.congr_fun hx f).symm
    · intro y hy
      have hinj : Function.Injective (topDualPairing 𝕜 E).flip :=
        LinearMap.ker_eq_bot.mp
          (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp
            (C12InitialProperties.norm_dual_pairing_separates 𝕜 E))
      apply hinj
      ext f
      exact (hy f).symm.trans (LinearMap.congr_fun hx f).symm
  · rintro ⟨x, hx, _⟩
    apply Submodule.subset_span
    exact ⟨x, LinearMap.ext fun f => (hx f).symm⟩

theorem weakStar_eq_weak_iff_surjective :
    Spec.TopologiesEqualIffSurjective.{u, v} := by
  intro 𝕜 E _ _ _
  constructor
  · intro heq Φ
    have hc : @Continuous (E →L[𝕜] 𝕜) 𝕜
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
        inferInstance Φ.toLinearMap := by
      rw [heq]
      exact (C12InitialProperties.weak_continuous_linear_dual
        𝕜 (E →L[𝕜] 𝕜) Φ.toLinearMap).mpr ⟨Φ, rfl⟩
    obtain ⟨x, hx, _⟩ :=
      (weakStar_continuous_iff_unique_evaluation 𝕜 E Φ.toLinearMap).mp hc
    exact ⟨x, ContinuousLinearMap.ext fun f => (hx f).symm⟩
  · intro hsurj
    apply le_antisymm
    · rw [C12WeakStar.dualWeakTopology_initial 𝕜 E]
      apply le_iInf
      intro Φ
      obtain ⟨x, rfl⟩ := hsurj Φ
      apply continuous_iff_le_induced.mp
      exact (C12WeakStar.weakStarTopology_evaluation_coarsest
        𝕜 E _).mpr le_rfl x
    · exact (C12WeakStar.dual_topology_inclusions 𝕜 E).2

theorem nonreflexive_banach_dual_topologies_differ :
    Spec.NonreflexiveBanachTopologiesDiffer.{u, v} := by
  intro 𝕜 E _ _ _ _ hn heq
  exact hn ((weakStar_eq_weak_iff_surjective 𝕜 E).mp heq)

end
end ExpandedFA.P1.C12WeakStarComparison
