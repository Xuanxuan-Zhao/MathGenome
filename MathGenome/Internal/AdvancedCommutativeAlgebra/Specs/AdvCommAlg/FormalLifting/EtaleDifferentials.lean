import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TowerMaps

/-! The differential comparison in FL-11 (paper.tex, lines 739–766).
All three rings and their universes are arbitrary. The only additional
hypothesis on the compatible tower A → B → D is formal étaleness of B → D,
in the square-zero lifting sense of FL-01. The equality of linear maps
identifies the isomorphism with the canonical map of KD-08. -/
namespace Specs.AdvCommAlg.FormalLifting

universe u v w
open scoped TensorProduct

def etaleDifferentials : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallyEtaleValue B D →
      ∃ e : (D ⊗[B] KaehlerDifferential A B) ≃ₗ[D] KaehlerDifferential A D,
        e.toLinearMap = Specs.AdvCommAlg.Differentials.towerMapUValue A B D ∧
        ∀ b : B, e (1 ⊗ₜ[B] KaehlerDifferential.D A B b) =
          KaehlerDifferential.D A D (algebraMap B D b)

end Specs.AdvCommAlg.FormalLifting
