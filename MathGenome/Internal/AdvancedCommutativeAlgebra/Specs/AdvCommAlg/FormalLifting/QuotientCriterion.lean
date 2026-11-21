import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions

/-! Independent statements for the quotient assertion of FL-12
(paper.tex:767–786). The formal properties use square-zero lifting tests.
All commutative unital rings, including the zero ring, and all ideals are
allowed. In particular no finite generation hypothesis is imposed. -/
namespace Specs.AdvCommAlg.FormalLifting.QuotientCriterion

universe u

/-- Quotient maps have unique lifts whenever lifts exist. -/
def quotientUnramified : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A),
    formallyUnramifiedValue A (A ⧸ I)

/-- A quotient is formally smooth exactly when its ideal equals its square. -/
def quotientSmoothIff : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A),
    formallySmoothValue A (A ⧸ I) ↔ I = I ^ 2

/-- A quotient is formally étale exactly when its ideal equals its square. -/
def quotientEtaleIff : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A),
    formallyEtaleValue A (A ⧸ I) ↔ I = I ^ 2

/-- For quotients, formal smoothness and formal étaleness coincide. -/
def quotientSmoothIffEtale : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A),
    formallySmoothValue A (A ⧸ I) ↔ formallyEtaleValue A (A ⧸ I)

/-- A nonzero square-zero ideal gives a quotient which is not formally smooth. -/
def squareZeroNotSmooth : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A),
    I ≠ ⊥ → I ^ 2 = ⊥ → ¬ formallySmoothValue A (A ⧸ I)

end Specs.AdvCommAlg.FormalLifting.QuotientCriterion
