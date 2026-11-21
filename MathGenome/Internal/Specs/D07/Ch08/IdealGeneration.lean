import MathGenome.Internal.Specs.D07.Ch08.IdealDefinition
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Fin

/-!
Independent specifications for K07.08.ideal_generation (paper.tex:1335–1356).
Rings are associative and unital, with no nontriviality assumption. In the
noncommutative statements the generated ideal is explicitly two-sided.
The index `Fin m` permits repetitions and the empty sum (`m = 0`).
-/

universe u
namespace Specs.D07.Ch08.IdealGeneration

open scoped BigOperators
open Specs.D07.Ch08.IdealDefinition

/-- The displayed finite sums, with every middle factor in the given set. -/
def TwoSidedSums {R : Type u} [Ring R] (S : Set R) (x : R) : Prop :=
  ∃ m : ℕ, ∃ r s t : Fin m → R,
    (∀ i, s i ∈ S) ∧ x = ∑ i, r i * s i * t i

/-- The finite sums for a generated left ideal (also used in a commutative ring). -/
def LeftSums {R : Type u} [Ring R] (S : Set R) (x : R) : Prop :=
  ∃ m : ℕ, ∃ r s : Fin m → R,
    (∀ i, s i ∈ S) ∧ x = ∑ i, r i * s i

/-- Single products, without closing under finite addition. -/
def SingleProducts {R : Type u} [Ring R] (S : Set R) (x : R) : Prop :=
  ∃ r s t : R, s ∈ S ∧ x = r * s * t

def GeneratedIdealFormula : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set R) (x : R),
    x ∈ TwoSidedIdeal.span S ↔ TwoSidedSums S x

/-- The span is a two-sided ideal containing the generators, and is least
among all additive subgroups satisfying the source's absorption axioms. -/
def LeastTwoSidedIdeal : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set R),
    IsTwoSidedIdeal (TwoSidedIdeal.span S).asIdeal.toAddSubgroup ∧
    S ⊆ (TwoSidedIdeal.span S : Set R) ∧
    ∀ H : AddSubgroup R, IsTwoSidedIdeal H →
      ((TwoSidedIdeal.span S : Set R) ⊆ H ↔ S ⊆ H)

def IntersectionCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set R),
    TwoSidedIdeal.span S = sInf {I : TwoSidedIdeal R | S ⊆ (I : Set R)}

def CommutativeFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Set R) (x : R),
    x ∈ TwoSidedIdeal.span S ↔ LeftSums S x

def EmptyGeneration : Prop :=
  ∀ (R : Type u) [Ring R],
    TwoSidedIdeal.span (∅ : Set R) = ⊥ ∧ Ideal.span (∅ : Set R) = ⊥

def LeftIdealFormula : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set R) (x : R),
    x ∈ Ideal.span S ↔ LeftSums S x

/-- A concrete failure of additive closure: multiples of either 2 or 3
contain 2 and 3, but do not contain their sum 5. -/
def SingleProductsNotAddClosed : Prop :=
  SingleProducts ({2, 3} : Set ℤ) 2 ∧
  SingleProducts ({2, 3} : Set ℤ) 3 ∧
  ¬ SingleProducts ({2, 3} : Set ℤ) (2 + 3)

end Specs.D07.Ch08.IdealGeneration
