import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04CanonicalMap

/-! Weak-star topology for the canonical continuous linear dual, the weak
 topology of that normed dual, and transport through a specified predual.
 Definitions and results of fa2:p1:c12:weak-star, paper.tex 2290–2306. -/

namespace ExpandedFA.P1.C12WeakStar

universe u v w
open scoped Topology
noncomputable section

/-- The weak-star topology on the original norm-continuous dual. -/
def weakStarTopology : Spec.WeakStarTopologyType :=
  fun 𝕜 E _ _ _ => dualPairTopology 𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip

/-- The weak topology of the dual as a normed space. -/
def dualWeakTopology : Spec.DualWeakTopologyType :=
  fun 𝕜 E _ _ _ => dualPairTopology 𝕜 (E →L[𝕜] 𝕜)
    ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) (topDualPairing 𝕜 (E →L[𝕜] 𝕜))

/-- The finite evaluation conditions at f₀, with one common radius. -/
def weakStarNeighborhood : Spec.NeighborhoodType :=
  fun 𝕜 E _ _ _ f₀ s ε => {f : E →L[𝕜] 𝕜 | ∀ x ∈ s, ‖(f - f₀) x‖ < ε}

theorem weakStarTopology_dualPair : Spec.PairingCompatibility := by
  intro 𝕜 E _ _ _
  rfl

theorem weakStarTopology_native : Spec.NativeCompatibility := by
  intro 𝕜 E _ _ _
  rfl

theorem weakStarTopology_evaluations : Spec.Initial := by
  intro 𝕜 E _ _ _
  exact dualPairTopology_initial 𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip

theorem weakStarTopology_evaluation_coarsest : Spec.Coarsest := by
  intro 𝕜 E _ _ _ t
  exact dualPairTopology_coarsest 𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip t

theorem weakStarTopology_nhds_basis : Spec.NeighborhoodBasis := by
  intro 𝕜 E _ _ _ f₀
  exact dualPairTopology_nhds_basis 𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip f₀

theorem weakStarTopology_isOpen_iff : Spec.OpenCharacterization := by
  intro 𝕜 E _ _ _ U
  exact dualPairTopology_isOpen_iff 𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip U

theorem weakStarTopology_open_basis : Spec.OpenBasis := by
  intro 𝕜 E _ _ _
  exact dualPairTopology_open_basis 𝕜 (E →L[𝕜] 𝕜) E (topDualPairing 𝕜 E).flip

theorem weakStarNeighborhood_empty : Spec.EmptyNeighborhood := by
  intro 𝕜 E _ _ _ f₀ ε
  ext f
  simp [Spec.NeighborhoodValue]

/-- The weak topology of E′ tests against its full norm-continuous dual E″. -/
theorem dualWeakTopology_initial : Spec.DualWeakInitial := by
  intro 𝕜 E _ _ _
  exact dualPairTopology_evaluation 𝕜 (E →L[𝕜] 𝕜)

/-- Norm is finer than weak; weak is finer than weak-star. -/
theorem dual_topology_inclusions : Spec.TopologyInclusions := by
  intro 𝕜 E _ _ _
  constructor
  · rw [dualWeakTopology_initial 𝕜 E]
    exact le_iInf fun Φ => continuous_iff_le_induced.mp Φ.continuous
  · rw [weakStarTopology_evaluations 𝕜 E]
    apply le_iInf
    intro x
    rw [dualWeakTopology_initial 𝕜 E]
    exact iInf_le _ (C04CanonicalMap.canonicalEvaluation 𝕜 E x)

theorem dual_topology_open_inclusions : Spec.OpenInclusions := by
  intro 𝕜 E _ _ _ U
  exact ⟨(dual_topology_inclusions 𝕜 E).2 U,
    (dual_topology_inclusions 𝕜 E).1 U⟩

/-- The predual E includes its particular identification E′ ≃ F as data. -/
abbrev PredualIdentification : Spec.PredualIdentificationType.{u, v, w} :=
  fun 𝕜 E F _ _ _ _ _ => (E →L[𝕜] 𝕜) ≃ₗ[𝕜] F

/-- Evaluation transported using precisely the chosen dual identification. -/
def predualPairing : Spec.PredualPairingType :=
  fun 𝕜 E _ _ _ _ _ _ I => (topDualPairing 𝕜 E).flip.compl₂ I.symm.toLinearMap

/-- The weak-star topology determined by the specified predual pairing. -/
def predualWeakStarTopology : Spec.PredualTopologyType :=
  fun 𝕜 E F _ _ _ _ _ I => dualPairTopology 𝕜 F E (predualPairing 𝕜 E F I)

@[simp]
theorem predualPairing_apply : Spec.PredualEvaluation := by
  intro 𝕜 E F _ _ _ _ _ I x f
  rfl

theorem predualWeakStarTopology_initial : Spec.PredualInitial := by
  intro 𝕜 E F _ _ _ _ _ I
  exact dualPairTopology_initial 𝕜 F E (predualPairing 𝕜 E F I)

theorem predualWeakStarTopology_transport : Spec.PredualTransport := by
  intro 𝕜 E F _ _ _ _ _ I
  rw [predualWeakStarTopology_initial 𝕜 E F I, weakStarTopology_evaluations 𝕜 E,
    induced_iInf]
  simp only [induced_compose, Function.comp_def]

end
end ExpandedFA.P1.C12WeakStar
