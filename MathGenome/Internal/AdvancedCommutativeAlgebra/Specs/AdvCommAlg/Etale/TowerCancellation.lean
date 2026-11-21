import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions

/-! Independent specification of ET-05 (paper.tex, lines 1634–1653).
All structural maps in the tower are specified and compatible. The formal
statement has no finiteness assumptions, and zero rings are allowed.
-/
namespace Specs.AdvCommAlg.Etale.TowerCancellation

universe u v w

/-- Formal unramifiedness of B/A and formal étaleness of C/A imply
formal étaleness of C/B, in the square-zero lifting sense of FL-01. -/
def formalEtaleCancellation : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C],
    FormalLifting.formallyUnramifiedValue A B →
    FormalLifting.formallyEtaleValue A C →
    FormalLifting.formallyEtaleValue B C

/-- If B/A and C/A are étale, then C/B is étale. The conclusion uses
ET-01's full étale predicate, so includes finite presentation over B. -/
def etaleCancellation : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C],
    etaleValue A B → etaleValue A C → etaleValue B C

end Specs.AdvCommAlg.Etale.TowerCancellation
