import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions

/-! Independent statements of FL-09, paper.tex:659–682.
The predicates below are the square-zero lifting predicates of FL-01.
Rings may be zero and no finiteness conditions are imposed. Towers have
compatible structural maps; base change has the canonical left scalar action.
-/
namespace Specs.AdvCommAlg.FormalLifting.Permanence

universe u v w

open scoped TensorProduct

/-- Formal smoothness is preserved by compatible composition. -/
def smoothComposition : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallySmoothValue A B → formallySmoothValue B D → formallySmoothValue A D

/-- Formal unramifiedness is preserved by compatible composition. -/
def unramifiedComposition : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallyUnramifiedValue A B → formallyUnramifiedValue B D →
      formallyUnramifiedValue A D

/-- Formal étaleness is preserved by compatible composition. -/
def etaleComposition : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallyEtaleValue A B → formallyEtaleValue B D → formallyEtaleValue A D

/-- Formal smoothness is preserved by arbitrary base change A → A'. -/
def smoothBaseChange : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'],
    formallySmoothValue A B → formallySmoothValue A' (A' ⊗[A] B)

/-- Formal unramifiedness is preserved by arbitrary base change A → A'. -/
def unramifiedBaseChange : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'],
    formallyUnramifiedValue A B → formallyUnramifiedValue A' (A' ⊗[A] B)

/-- Formal étaleness is preserved by arbitrary base change A → A'. -/
def etaleBaseChange : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'],
    formallyEtaleValue A B → formallyEtaleValue A' (A' ⊗[A] B)

/-- A formally smooth composite is smooth over a formally unramified intermediate ring. -/
def smoothOverUnramified : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallyUnramifiedValue A B → formallySmoothValue A D → formallySmoothValue B D

/-- Formal unramifiedness of a composite implies that of the second map. -/
def unramifiedOverIntermediate : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallyUnramifiedValue A D → formallyUnramifiedValue B D

end Specs.AdvCommAlg.FormalLifting.Permanence
