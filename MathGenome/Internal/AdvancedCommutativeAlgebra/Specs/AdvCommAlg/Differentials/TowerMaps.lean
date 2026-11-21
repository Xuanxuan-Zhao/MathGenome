import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Naturality

/-! Independent specifications for KD-08 (paper.tex, Maps in a tower).
All rings are commutative with identity, including the zero ring. The three
algebra structures and IsScalarTower express precisely a compatible tower.
The tensor product is over B, and both displayed maps are C-linear. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w
noncomputable section
open scoped TensorProduct

def towerMapUType :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    C ⊗[B] KaehlerDifferential A B →ₗ[C] KaehlerDifferential A C

/-- Extend scalars in the natural differential map for B → C over A. -/
def towerMapUValue : towerMapUType.{u,v,w} :=
  fun A B C _ _ _ _ _ _ _ => KaehlerDifferential.mapBaseChange A B C

def towerMapVType :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    KaehlerDifferential A C →ₗ[C] KaehlerDifferential B C

/-- The natural differential map for the base change A → B and target id_C. -/
def towerMapVValue : towerMapVType.{u,v,w} :=
  fun A B C _ _ _ _ _ _ _ => KaehlerDifferential.map A B C C

def towerMapUApply : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (c : C) (b : B),
    towerMapUValue A B C (c ⊗ₜ[B] KaehlerDifferential.D A B b) =
      c • KaehlerDifferential.D A C (algebraMap B C b)

def towerMapVApply : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (c : C),
    towerMapVValue A B C (KaehlerDifferential.D A C c) =
      KaehlerDifferential.D B C c

end
end Specs.AdvCommAlg.Differentials
