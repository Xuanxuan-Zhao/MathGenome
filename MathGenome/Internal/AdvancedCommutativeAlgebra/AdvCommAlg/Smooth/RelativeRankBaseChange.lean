import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.RelativeRank
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.RelativeRankBaseChange

/-! The arbitrary base-change assertion of SM-09. -/
namespace AdvCommAlg.Smooth

universe u v w z
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Smooth.RelativeRankBaseChange

/-- KD-17, tensored with the residue field upstairs, identifies the new
cotangent fiber with scalar extension of the old fiber along κ(q) → κ(q'). -/
theorem cotangent_fiber_base_change : cotangentFiberComparison.{u,v,w,z} := by
  intro A A' B C _ _ _ _ _ _ _ _ _ _ _ _ q'
  let q := q'.comap (algebraMap B C)
  let k := q.asIdeal.ResidueField
  let k' := q'.asIdeal.ResidueField
  let : Algebra k k' :=
    (Ideal.ResidueField.map q.asIdeal q'.asIdeal (algebraMap B C) rfl).toAlgebra
  let : IsScalarTower B k k' := IsScalarTower.of_algebraMap_eq' (by
    ext b
    exact (Ideal.ResidueField.map_algebraMap q.asIdeal q'.asIdeal (algebraMap B C) rfl b).symm)
  exact ⟨AlgebraTensorModule.cancelBaseChange B k k' k' (KaehlerDifferential A B) ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange B C k' k' (KaehlerDifferential A B)).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl k' k')
      (Differentials.baseChangeEquiv A A' B C)⟩

/-- The dimensions agree because extension of scalars between fields
preserves dimension. Neither the base change nor B → C needs to be flat. -/
theorem relativeRank_base_change : baseChangeRank.{u,v,w,z} := by
  intro A A' B C _ _ _ _ _ _ _ _ _ _ _ _ hs q'
  let q := q'.comap (algebraMap B C)
  let : Algebra q.asIdeal.ResidueField q'.asIdeal.ResidueField :=
    (Ideal.ResidueField.map q.asIdeal q'.asIdeal (algebraMap B C) rfl).toAlgebra
  obtain ⟨e⟩ := cotangent_fiber_base_change A A' B C q'
  change Module.finrank q'.asIdeal.ResidueField
      (q'.asIdeal.ResidueField ⊗[C] KaehlerDifferential A' C) =
    Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[B] KaehlerDifferential A B)
  rw [← e.finrank_eq, Module.finrank_baseChange]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original assertion for B' = A' ⊗[A] B and its specified prime q'. -/
theorem relativeRank_tensor_base_change : tensorBaseChangeRank.{u,v,w} := by
  intro A B A' _ _ _ _ _ hs q'
  exact relativeRank_base_change A A' B (A' ⊗[A] B) hs q'

end
end AdvCommAlg.Smooth
