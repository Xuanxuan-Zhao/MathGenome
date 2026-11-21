import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusInverse

/-! Independent specification of the product assertion in `paper.tex`, p204:W09.
The order on `P × Q` is componentwise. Neither poset needs a top, bottom,
or an inhabitant, and the coefficient ring may be the zero ring. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace Specs.FiniteCombinatorics.Poset.MobiusProduct

/-- The canonical Möbius function factors on every comparable product pair,
including equality in either or both components. -/
def ProductFormula : Prop :=
  ∀ (R P Q : Type*) [CommRing R] [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q],
    ∀ (x₁ z₁ : P) (x₂ z₂ : Q), x₁ ≤ z₁ → x₂ ≤ z₂ →
      MobiusInverse.mobiusValue R (P × Q) (x₁, x₂) (z₁, z₂) =
        MobiusInverse.mobiusValue R P x₁ z₁ * MobiusInverse.mobiusValue R Q x₂ z₂

end Specs.FiniteCombinatorics.Poset.MobiusProduct
