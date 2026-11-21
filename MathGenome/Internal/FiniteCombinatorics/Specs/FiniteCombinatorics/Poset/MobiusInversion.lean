import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusInverse

/-! Independent statements of both equivalences in `paper.tex`, p204:W08.
The sums run over all elements satisfying the displayed inequality. No top,
bottom, nonemptiness, or nontriviality assumption is imposed. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace Specs.FiniteCombinatorics.Poset.MobiusInversion
open _root_.FiniteCombinatorics.Poset

/-- Lower-sum Möbius inversion, in both directions. -/
def LowerInversion : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    ∀ f g : P → R,
      (∀ x, g x = ∑ y ∈ Finset.univ.filter (fun y => y ≤ x), f y) ↔
      (∀ x, f x = ∑ y ∈ Finset.univ.filter (fun y => y ≤ x),
        MobiusInverse.mobiusValue R P y x * g y)

/-- Upper-sum Möbius inversion, in both directions. -/
def UpperInversion : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    ∀ f g : P → R,
      (∀ x, g x = ∑ y ∈ Finset.univ.filter (fun y => x ≤ y), f y) ↔
      (∀ x, f x = ∑ y ∈ Finset.univ.filter (fun y => x ≤ y),
        MobiusInverse.mobiusValue R P x y * g y)

end Specs.FiniteCombinatorics.Poset.MobiusInversion
