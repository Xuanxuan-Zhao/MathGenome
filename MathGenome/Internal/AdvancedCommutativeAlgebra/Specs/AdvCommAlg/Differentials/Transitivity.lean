import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TowerMaps
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Polynomial

/-! Independent statements for KD-09, paper.tex:252–264.
The exact sequence uses the canonical maps of KD-08 in every compatible tower,
including zero rings. The example uses evaluation at zero, not an unspecified
polynomial-algebra action on the field. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w
noncomputable section
open scoped TensorProduct

def transitivityExact : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    Function.Exact (towerMapUValue A B C) (towerMapVValue A B C) ∧
      Function.Surjective (towerMapVValue A B C)

/-- The first term is the one-dimensional space with generator 1 ⊗ dt;
its nonzero generator is killed by u, whose target is zero. -/
def transitivityFailureExample : Prop :=
  ∀ (k : Type u) [Field k],
    letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
    letI : IsScalarTower k (Polynomial k) k :=
      IsScalarTower.of_algebraMap_eq' (by
        ext a
        change a = Polynomial.eval 0 (Polynomial.C a)
        simp)
    let dt := (1 : k) ⊗ₜ[Polynomial k]
      KaehlerDifferential.D k (Polynomial k) Polynomial.X
    (∃ e : (k ⊗[Polynomial k] KaehlerDifferential k (Polynomial k)) ≃ₗ[k] k,
      e dt = 1) ∧
    dt ≠ 0 ∧ Subsingleton (KaehlerDifferential k k) ∧
    towerMapUValue k (Polynomial k) k dt = 0 ∧
    ¬ Function.Injective (towerMapUValue k (Polynomial k) k)

end
end Specs.AdvCommAlg.Differentials
