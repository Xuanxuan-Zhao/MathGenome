import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FspaceOpenGraph
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FspaceOpenMapping
import Mathlib.LinearAlgebra.Prod
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Homeomorph.Defs

namespace ExpandedFA.P1.FspaceOpenGraph

/-- The open mapping clause is the accepted general F-space theorem. -/
theorem open_mapping : FspaceOpenGraphSpec.OpenMapping :=
  FspaceOpenMapping.open_mapping

/-- The graph projection is a continuous linear bijection of F-spaces;
open mapping makes its inverse continuous. -/
theorem closed_graph : FspaceOpenGraphSpec.ClosedGraph := by
  intro 𝕜 E F _ _ _ _ _ _ _ hE hF T hclosed
  obtain ⟨haddE, hsmulE, hmetE, hcompleteE⟩ := hE
  obtain ⟨haddF, hsmulF, hmetF, hcompleteF⟩ := hF
  let := haddE
  let := haddF
  let := hsmulE
  let := hsmulF
  let := hmetE
  let := hmetF
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcompleteE
  let : CompleteSpace F := hcompleteF
  have : TopologicalSpace.MetrizableSpace (E × F) := inferInstance
  let : TopologicalSpace.MetrizableSpace T.graph :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (T.graph : Set (E × F)))
  let : IsUniformAddGroup T.graph :=
    inferInstanceAs (IsUniformAddGroup T.graph.toAddSubgroup)
  have hG : FSpace 𝕜 T.graph := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    change @CompleteSpace T.graph (IsTopologicalAddGroup.rightUniformSpace T.graph)
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact hclosed.isComplete.completeSpace_coe
  let e : T.graph ≃ₗ[𝕜] E :=
    { toFun := fun p => p.val.1
      invFun := fun x => ⟨(x, T x), rfl⟩
      left_inv := by
        intro p
        apply Subtype.ext
        exact Prod.ext rfl p.property.symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Continuous e := continuous_fst.comp continuous_subtype_val
  have hopen : IsOpenMap e := FspaceOpenMapping.open_mapping 𝕜 T.graph E hG
    ⟨haddE, hsmulE, hmetE, hcompleteE⟩ e.toLinearMap he e.surjective
  have hinv : Continuous e.symm :=
    (e.toEquiv.toHomeomorphOfContinuousOpen he hopen).symm.continuous
  exact (continuous_snd.comp continuous_subtype_val).comp hinv

end ExpandedFA.P1.FspaceOpenGraph
