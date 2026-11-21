import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02Completion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach
import Mathlib.Analysis.Normed.Operator.Extend

/-!
The isometric Banach completion and its universal property.

The completion carries the canonical extended norm and scalar action. Extension
along a dense isometric embedding preserves the operator norm: the bound for
the extension gives one inequality and restriction gives the other. The
isometric identification of arbitrary completions extends the identity of E;
density makes it unique. None of these steps excludes the zero space.
-/

namespace ExpandedFA.P1.C02Completion

/-- The canonical scalar-linear isometric embedding into the standard completion. -/
noncomputable def completionEmbedding : Spec.completionEmbeddingType :=
  fun _ _ _ _ _ => UniformSpace.Completion.toComplₗᵢ

theorem completion_embedding_properties :
    Spec.CompletionEmbeddingProperties := by
  intro 𝕜 E _ _ _
  let i := completionEmbedding 𝕜 E
  refine ⟨?_, i.norm_map, i.isometry.dist_eq, i.injective⟩
  exact UniformSpace.Completion.denseRange_coe

theorem completion_banach : Spec.CompletionBanach := by
  intro 𝕜 E _ _ _
  refine ⟨inferInstance, ?_⟩
  exact (ExpandedFA.P1.C01Banach.isBanachSpace_iff_completeSpace (UniformSpace.Completion E)).mpr inferInstance

theorem completion_exists : Spec.CompletionExists := by
  intro 𝕜 E _ _ _
  refine ⟨UniformSpace.Completion E, inferInstance, inferInstance, ?_⟩
  exact ⟨(completion_banach 𝕜 E).1, (completion_banach 𝕜 E).2,
    completionEmbedding 𝕜 E, (completion_embedding_properties 𝕜 E).1,
    (completion_embedding_properties 𝕜 E).2.1⟩



theorem completion_extension : Spec.Extension := by
  intro 𝕜 E H _ _ _ _ _ i hi F _ _ _ T
  let S := T.extend i.toContinuousLinearMap
  have hcomp : S.comp i.toContinuousLinearMap = T := by
    ext x
    exact T.extend_eq hi i.isometry.isUniformInducing x
  refine ⟨S, hcomp, ?_, ?_⟩
  · apply le_antisymm
    · simpa [S] using
        (T.opNorm_extend_le (e := i.toContinuousLinearMap) (N := 1) hi
          (fun x => by simp))
    · apply T.opNorm_le_bound (norm_nonneg S)
      intro x
      calc
        ‖T x‖ = ‖S (i x)‖ := by rw [← hcomp]; rfl
        _ ≤ ‖S‖ * ‖i x‖ := S.le_opNorm (i x)
        _ = ‖S‖ * ‖x‖ := by rw [i.norm_map]
  · intro S' hS'
    exact (T.extend_unique hi i.isometry.isUniformInducing S' hS').symm

theorem completion_uniqueness : Spec.Uniqueness := by
  intro 𝕜 E H G _ _ _ _ _ _ _ _ _ i j hi hj
  let U : H ≃ₗᵢ[𝕜] G := (LinearEquiv.refl 𝕜 E).extendOfIsometry
    i.toLinearMap j.toLinearMap hi hj (fun x => by simp)
  have hU : ∀ x, U (i x) = j x := by
    intro x
    exact LinearEquiv.extendOfIsometry_eq _ _ _ hi hj _ x
  refine ⟨U, hU, ?_⟩
  intro V hV
  apply LinearIsometryEquiv.ext
  exact congrFun (hi.equalizer V.continuous U.continuous
    (funext fun x => (hV x).trans (hU x).symm))

theorem isometric_completion : Spec.IsometricCompletion := by
  intro 𝕜 E _ _ _
  refine ⟨UniformSpace.Completion E, inferInstance, inferInstance,
    (completion_banach 𝕜 E).1, completionEmbedding 𝕜 E,
    (completion_banach 𝕜 E).2, (completion_embedding_properties 𝕜 E).1,
    (completion_embedding_properties 𝕜 E).2.1, ?_, ?_⟩
  · exact completion_extension 𝕜 E _ _ (completion_embedding_properties 𝕜 E).1
  · intro G _ _ _ j hj
    exact completion_uniqueness 𝕜 E _ G _ j
      (completion_embedding_properties 𝕜 E).1 hj

end ExpandedFA.P1.C02Completion
