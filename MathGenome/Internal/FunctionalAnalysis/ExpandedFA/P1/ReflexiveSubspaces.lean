import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ReflexiveSubspaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure

/-! The closed-subspace clause of `fa2:p1:c14:stability`.
The weakly compact ambient unit ball meets the weakly closed subspace
in the image of its inherited unit ball. Hahn–Banach identifies the
induced topology with the intrinsic weak topology. Closedness gives
completeness, so the ball characterization gives canonical reflexivity.
-/

namespace ExpandedFA.P1.ReflexiveSubspaces

universe u v

theorem subspace_induced_weak_topology : Spec.SubspaceWeakTopology.{u, v} :=
  C12ConvexClosure.subspace_induced_weak_topology

/-- Closed subspaces of reflexive Banach spaces are reflexive. -/
theorem reflexive_closed_subspace : Spec.ClosedSubspaceReflexive.{u, v} := by
  intro 𝕜 E _ _ _ _ hE M hM
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  apply (C14BallCharacterization.reflexive_iff_weakCompact_unitBall 𝕜 M).mpr
  have hb := (C14BallCharacterization.reflexive_iff_weakCompact_unitBall 𝕜 E).mp hE
  have hMw := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule 𝕜 E M hM
  have he : @Topology.IsEmbedding M E
      (C12DualPairSpec.DualPairTopologyValue 𝕜 M (M →L[𝕜] 𝕜) (topDualPairing 𝕜 M))
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      (fun m : M => (m : E)) :=
    @Topology.IsEmbedding.mk M E
      (C12DualPairSpec.DualPairTopologyValue 𝕜 M (M →L[𝕜] 𝕜) (topDualPairing 𝕜 M))
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      (fun m : M => (m : E))
      (@Topology.IsInducing.mk M E
        (C12DualPairSpec.DualPairTopologyValue 𝕜 M (M →L[𝕜] 𝕜) (topDualPairing 𝕜 M))
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
        (fun m : M => (m : E)) (subspace_induced_weak_topology 𝕜 E M).symm)
      Subtype.val_injective
  have hball : (fun m : M => (m : E)) '' {m : M | ‖m‖ ≤ 1} =
      {x : E | ‖x‖ ≤ 1} ∩ (M : Set E) := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨hm, m.property⟩
    · rintro ⟨hx, hxM⟩
      exact ⟨⟨x, hxM⟩, hx, rfl⟩
  apply (@Topology.IsEmbedding.isCompact_iff M E
    (C12DualPairSpec.DualPairTopologyValue 𝕜 M (M →L[𝕜] 𝕜) (topDualPairing 𝕜 M))
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
    {m : M | ‖m‖ ≤ 1} (fun m : M => (m : E)) he).mpr
  rw [hball]
  exact @IsCompact.inter_right E
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
    {x : E | ‖x‖ ≤ 1} (M : Set E) hb hMw

end ExpandedFA.P1.ReflexiveSubspaces
