import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal

/-! Independent specifications for paper.tex, Corollary KD-06 (lines 217–224).
The zero differential module is expressed by `Subsingleton`; no nontriviality,
finiteness, or properness assumption on an ideal is imposed. -/
namespace Specs.AdvCommAlg.Differentials

universe u v

/-- Every surjective structural map has zero relative differentials. -/
def surjectiveBaseSubsingleton : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    Function.Surjective (algebraMap A B) → Subsingleton (KaehlerDifferential A B)

/-- The identity structural map has zero relative differentials. -/
def selfBaseSubsingleton : Prop :=
  ∀ (A : Type u) [CommRing A], Subsingleton (KaehlerDifferential A A)

/-- Every quotient, with its canonical A-algebra structure, has zero
relative differentials over A. This includes the quotient by the unit ideal. -/
def quotientBaseSubsingleton : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A),
    Subsingleton (KaehlerDifferential A (A ⧸ I))

end Specs.AdvCommAlg.Differentials
