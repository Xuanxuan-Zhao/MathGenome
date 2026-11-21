import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TowerMaps

/-! FL-13: split short exactness in a compatible tower, assuming only formal
smoothness of the second stage. The splitting is an actual linear retraction. -/
namespace Specs.AdvCommAlg.FormalLifting

universe u v w
noncomputable section
open scoped TensorProduct
open Specs.AdvCommAlg.Differentials

def splitTransitivity : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallySmoothValue B D →
      Function.Injective (towerMapUValue A B D) ∧
      Function.Exact (towerMapUValue A B D) (towerMapVValue A B D) ∧
      Function.Surjective (towerMapVValue A B D) ∧
      ∃ r : KaehlerDifferential A D →ₗ[D] D ⊗[B] KaehlerDifferential A B,
        r.comp (towerMapUValue A B D) = LinearMap.id

end
end Specs.AdvCommAlg.FormalLifting
