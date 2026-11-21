import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusInverse
import Mathlib.Data.Finset.Powerset

/-! Independent statements for the Boolean interval assertion of
`paper.tex`, p204:W09. The finite poset is the powerset of the finite
upper endpoint, ordered by inclusion. The ambient type need not be finite.
Equality of the endpoints and the empty upper endpoint are allowed. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace FiniteCombinatorics.Poset

/-- All subsets of a fixed finite set, ordered by inclusion. -/
abbrev BooleanPoset {α : Type*} (T : Finset α) :=
  {S : Finset α // S ∈ T.powerset}

end FiniteCombinatorics.Poset

namespace Specs.FiniteCombinatorics.Poset.MobiusBoolean
open _root_.FiniteCombinatorics.Poset

/-- The integer Möbius value on every finite subset interval. -/
def IntegerFormula : Prop :=
  ∀ (α : Type*) (S T : Finset α) (h : S ⊆ T),
    MobiusInverse.mobiusValue ℤ (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩ =
        (-1 : ℤ) ^ (T \ S).card

/-- The same formula over any commutative ring. -/
def RingFormula : Prop :=
  ∀ (R α : Type*) [CommRing R] (S T : Finset α) (h : S ⊆ T),
    MobiusInverse.mobiusValue R (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩ =
        (-1 : R) ^ (T \ S).card

/-- These ring values are the images of the integer values. -/
def IntegerSpecialization : Prop :=
  ∀ (R α : Type*) [CommRing R] (S T : Finset α) (h : S ⊆ T),
    (MobiusInverse.mobiusValue ℤ (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩ : R) =
    MobiusInverse.mobiusValue R (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩

end Specs.FiniteCombinatorics.Poset.MobiusBoolean
