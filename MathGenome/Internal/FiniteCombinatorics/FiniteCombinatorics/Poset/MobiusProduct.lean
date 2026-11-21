import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Poset.MobiusInverse
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusProduct

/-! The product formula in `paper.tex`, p204:W09, using the same canonical
Möbius incidence function as the general inversion interface. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace FiniteCombinatorics.Poset.IncidenceFunction

/-- Möbius values on a product interval are products of the factor values. -/
theorem mobius_product (R P Q : Type*) [CommRing R]
    [PartialOrder P] [Fintype P] [PartialOrder Q] [Fintype Q]
    (x₁ z₁ : P) (x₂ z₂ : Q) (_h₁ : x₁ ≤ z₁) (_h₂ : x₂ ≤ z₂) :
    mobius R (P × Q) (x₁, x₂) (z₁, z₂) =
      mobius R P x₁ z₁ * mobius R Q x₂ z₂ := by
  have hi : (Prod.instLocallyFiniteOrder : LocallyFiniteOrder (P × Q)) =
      finiteIntervals (P × Q) := Subsingleton.elim _ _
  have h := (congrArg (fun f : IncidenceAlgebra R (P × Q) => f (x₁, x₂) (z₁, z₂))
      (IncidenceAlgebra.mu_prod_mu R (α := P) (β := Q))).symm
  rw [hi] at h
  have hd : (@instDecidableEqProd P Q (Classical.decEq P) (Classical.decEq Q)) =
      Classical.decEq (P × Q) := Subsingleton.elim _ _
  rw [hd] at h
  exact h

end FiniteCombinatorics.Poset.IncidenceFunction
