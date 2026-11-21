import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.IncidenceAlgebra

/-! Independent specifications for the inverse and recurrence part of
`paper.tex`, Theorem p204:W08. All finite partial orders and commutative
rings are allowed, including empty orders and the zero ring. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace Specs.FiniteCombinatorics.Poset.MobiusInverse
open _root_.FiniteCombinatorics.Poset

def MobiusType : Type _ :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    IncidenceFunction R P

/-- The canonical recursively defined Möbius function on the same incidence algebra. -/
def mobiusValue : MobiusType := fun R P _ _ _ => IncidenceAlgebra.mu R

def InverseIdentities : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    (IncidenceAlgebra.zeta R : IncidenceFunction R P) * mobiusValue R P = 1 ∧
    mobiusValue R P * IncidenceAlgebra.zeta R = 1

def Diagonal : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    ∀ x : P, mobiusValue R P x x = 1

/-- `Ico x z` is precisely the source's set `x ≤ y < z`. -/
def Recurrence : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    ∀ x z : P, x < z →
      mobiusValue R P x z = -∑ y ∈ Finset.Ico x z, mobiusValue R P x y

def RecursionUnique : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    ∀ f : IncidenceFunction R P,
      (∀ x : P, f x x = 1) →
      (∀ x z : P, x < z → f x z = -∑ y ∈ Finset.Ico x z, f x y) →
      f = mobiusValue R P

/-- Integer coefficients map into every coefficient ring, on every pair. -/
def IntegerSpecialization : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    ∀ x z : P, (mobiusValue ℤ P x z : R) = mobiusValue R P x z

end Specs.FiniteCombinatorics.Poset.MobiusInverse
