import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! FL-17, paper.tex:871–902: the existence and existence-and-uniqueness
descent assertions. The tensor product has its canonical left A'-algebra
structure. Finite presentation is a hypothesis on B over A; all rings,
including the zero ring, are allowed. The conclusions use the square-zero
lifting properties of FL-01, rather than just differential vanishing. -/
namespace Specs.AdvCommAlg.FormalLifting

open TensorProduct

universe u v w

/-- Existence of square-zero lifts descends in finite presentation. -/
def smoothFinitePresentationDescent : Prop :=
  ∀ (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.FaithfullyFlat A A']
    [Algebra.FinitePresentation A B],
    formallySmoothValue A' (A' ⊗[A] B) → formallySmoothValue A B

/-- Existence and uniqueness of square-zero lifts descend in finite presentation. -/
def etaleFinitePresentationDescent : Prop :=
  ∀ (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.FaithfullyFlat A A']
    [Algebra.FinitePresentation A B],
    formallyEtaleValue A' (A' ⊗[A] B) → formallyEtaleValue A B

end Specs.AdvCommAlg.FormalLifting
