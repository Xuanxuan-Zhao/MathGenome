import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.AffineTriangularDecomposition
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.AffineSimpleTriples

/-! The triangular decomposition and simple triples of the untwisted affine Lie algebra. -/

noncomputable section

universe u

namespace RepTheorySurvey.Affine

open _root_.Specs.RepTheorySurvey.Affine.AffineTriangularDecomposition

/-- Proposition LO10 for the untwisted affine loop model. -/
theorem affineTriangularDecomposition : affineTriangularDecomposition_type.{u} := by
  intro G _ _ _ _ B H _ φ hB hφ
  obtain ⟨hcomp, hdisj⟩ := triangularDecomposition B H φ hφ
  obtain ⟨hpos, hneg⟩ := sidesClosed B H φ
  refine
    { decomposition := hcomp
      cartan_positive_disjoint := hdisj
      cartan_abelian := cartanAbelianBracket B H
      positive_closed := hpos
      negative_closed := hneg
      cartan_weight_values := ?_
      adjoint_decomposition := adjointWeightDecomposition B H
      zero_weight := affineWeightSpace_zero B H
      nonzero_weights := ?_
      real_root_spaces := ?_
      imaginary_root_spaces := ?_
      highest_root := highestFiniteRoot H φ hφ
      triple_choices := finiteSimpleTripleChoices H φ hφ
      simple_triples := ?_ }
  · exact ⟨cartanIncl B H, cartanK B H, cartanD B H, fun _ => rfl, rfl, rfl,
      delta_cartanIncl B H, delta_cartanK B H, delta_cartanD B H,
      fun α => ⟨extendFiniteRoot_cartanIncl B H α, extendFiniteRoot_cartanK B H α,
        extendFiniteRoot_cartanD B H α⟩⟩
  · intro χ
    rw [Submodule.ne_bot_iff]
    simpa only [mem_affineWeightSpace, and_comm] using nonzeroWeights B H χ
  · intro α m
    dsimp
    have h := affineWeightSpace_real B H α m
    refine ⟨h, ?_⟩
    exact (congrArg (fun P : Submodule ℂ (AffineAlgebra B) => Module.finrank ℂ P) h).trans
      (realWeightSpace B H α m).2
  · intro m hm
    dsimp
    have h := affineWeightSpace_imaginary B H m hm
    refine ⟨h, ?_⟩
    exact (congrArg (fun P : Submodule ℂ (AffineAlgebra B) => Module.finrank ℂ P) h).trans
      (imaginaryWeightSpace B H m hm).2
  · intro θ hθ T S
    obtain ⟨hrelations, hmixed⟩ := affineSimpleTripleRelations B H φ hB hφ θ hθ T S
    refine ⟨?_, hmixed, affineSimpleGenerators B H φ hB hφ θ hθ T S⟩
    intro i
    obtain ⟨hcartan, hα, he, hf⟩ := affineSimpleRootWeights B H φ hB hφ θ hθ T S i
    exact ⟨hcartan, hα, he, hf, hrelations i⟩

end RepTheorySurvey.Affine
