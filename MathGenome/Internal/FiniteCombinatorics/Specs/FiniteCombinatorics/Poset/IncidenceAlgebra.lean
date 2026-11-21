import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
Independent interface for paper.tex, Chapter 1, Definition p204:W07 (252–274).
The canonical representation is Mathlib's functions vanishing off `x ≤ z`.
`restrict` and `extend` connect it to arbitrary functions on comparable pairs.
No nonemptiness or nontriviality of the poset or ring is required.
-/

noncomputable section
open Classical

namespace FiniteCombinatorics.Poset

/-- Incidence functions, represented by their zero extension to all pairs. -/
abbrev IncidenceFunction (R P : Type*) [Zero R] [LE P] := IncidenceAlgebra R P

/-- The domain of incidence functions in the source. -/
abbrev ComparablePair (P : Type*) [LE P] := {p : P × P // p.1 ≤ p.2}

abbrev ComparableFunction (R P : Type*) [LE P] := ComparablePair P → R

/-- Finiteness supplies every closed interval; this is an optional scoped instance. -/
scoped instance finiteIntervals (P : Type*) [PartialOrder P] [Fintype P] :
    LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder

namespace IncidenceFunction

/-- Restriction to precisely the pairs occurring in the source. -/
def restrict {R P : Type*} [Zero R] [LE P] (f : IncidenceFunction R P) :
    ComparableFunction R P := fun p => f p.1.1 p.1.2

/-- Zero extension imposes no condition on the values at comparable pairs. -/
def extend {R P : Type*} [Zero R] [LE P] (f : ComparableFunction R P) :
    IncidenceFunction R P where
  toFun x z := if h : x ≤ z then f ⟨(x, z), h⟩ else 0
  eq_zero_of_not_le' := fun _ _ h => dite_eq_right h

end IncidenceFunction
end FiniteCombinatorics.Poset

open scoped FiniteCombinatorics.Poset

namespace Specs.FiniteCombinatorics.Poset.IncidenceAlgebra
open _root_.FiniteCombinatorics.Poset

/-- Full type and expected value of the delta function. -/
def DeltaType : Type _ :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P], IncidenceFunction R P

def deltaValue : DeltaType := fun R P _ _ => 1

/-- Full type and expected value of the zeta function. -/
def ZetaType : Type _ :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P], IncidenceFunction R P

def zetaValue : ZetaType := fun R P _ _ => IncidenceAlgebra.zeta R

/-- The ring structure has exactly the library's convolution and pointwise operations. -/
def RingStructureType : Type _ :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    Ring (IncidenceFunction R P)

def ringStructureValue : RingStructureType := fun R P _ _ _ => inferInstance

/-- The algebra structure uses the coefficient ring itself as its scalars. -/
def AlgebraStructureType : Type _ :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
    Algebra R (IncidenceFunction R P)

def algebraStructureValue : AlgebraStructureType := fun R P _ _ _ => inferInstance

/-- Both inverse identities, with the maps explicitly defined above. -/
def ComparablePairBridge : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
  (∀ f : IncidenceFunction R P,
    IncidenceFunction.extend (IncidenceFunction.restrict f) = f) ∧
  (∀ f : ComparableFunction R P,
    IncidenceFunction.restrict (IncidenceFunction.extend f) = f)

/-- Addition, zero, negation, and scalar multiplication are pointwise. -/
def PointwiseOperations : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
  ∀ (f g : IncidenceFunction R P) (r : R) (x z : P),
    (0 : IncidenceFunction R P) x z = 0 ∧
    (f + g) x z = f x z + g x z ∧
    (-f) x z = -f x z ∧
    (r • f) x z = r * f x z

/-- `Icc` is the closed interval, so both endpoints are included in convolution. -/
def ConvolutionFormula : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
  ∀ (f g : IncidenceFunction R P) (x z : P),
    (f * g) x z = ∑ y ∈ Finset.Icc x z, f x y * g y z

def DeltaFormula : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
  ∀ x z : P, (1 : IncidenceFunction R P) x z = if x = z then 1 else 0

def ZetaFormula : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
  ∀ x z : P, (IncidenceAlgebra.zeta R : IncidenceFunction R P) x z =
    if x ≤ z then 1 else 0

/-- Associativity, two-sided identity, distributivity, and scalar bilinearity. -/
def ConvolutionLaws : Prop :=
  ∀ (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P],
  ∀ (f g h : IncidenceFunction R P) (r : R),
    (f * g) * h = f * (g * h) ∧
    (1 : IncidenceFunction R P) * f = f ∧
    f * (1 : IncidenceFunction R P) = f ∧
    f * (g + h) = f * g + f * h ∧
    (f + g) * h = f * h + g * h ∧
    (r • f) * g = r • (f * g) ∧
    f * (r • g) = r • (f * g)

end Specs.FiniteCombinatorics.Poset.IncidenceAlgebra
