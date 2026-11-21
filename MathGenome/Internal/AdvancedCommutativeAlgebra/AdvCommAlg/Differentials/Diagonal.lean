import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Diagonal

/-! The diagonal ideal model of the canonical universal differential (KD-03). -/
namespace AdvCommAlg.Differentials

universe u v
noncomputable section
open scoped TensorProduct

/-- The two B-actions agree because their difference lies in J and J kills J/J². -/
theorem diagonal_actions_agree :
    Specs.AdvCommAlg.Differentials.diagonalActionsAgree.{u,v} := by
  intro A B _ _ _ b q
  have h := Ideal.Cotangent.smul_eq_zero_of_mem
    (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A b) q
  rw [sub_smul, sub_eq_zero] at h
  exact h.symm

/-- The inherited B-module structure is induced by b ↦ b ⊗ 1. -/
theorem diagonal_left_action :
    Specs.AdvCommAlg.Differentials.diagonalLeftAction.{u,v} := by
  intro A B _ _ _ b q
  change b • q = (algebraMap B (B ⊗[A] B) b) • q
  exact (IsScalarTower.algebraMap_smul (B ⊗[A] B) b q).symm

/-- Ω_{B/A} ≃ J/J² with its left-factor B-module structure. -/
def diagonalEquiv : Specs.AdvCommAlg.Differentials.diagonalEquivType.{u,v} :=
  fun A B _ _ _ => LinearEquiv.refl B _

/-- The class of db is exactly [1 ⊗ b − b ⊗ 1]. -/
theorem diagonalEquiv_apply :
    ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (b : B),
      diagonalEquiv A B (universalDerivation A B b) =
        (Specs.AdvCommAlg.Differentials.diagonalIdeal A B).toCotangent
          ⟨(1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B),
            KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A b⟩ := by
  intro A B _ _ _ b
  rfl

end
end AdvCommAlg.Differentials
