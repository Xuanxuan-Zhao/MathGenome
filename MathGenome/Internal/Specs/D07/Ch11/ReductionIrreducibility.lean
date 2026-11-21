import MathGenome.Internal.Specs.D07.Ch11.GaussFractionIrreducible
import Mathlib.Data.ZMod.Basic

/-!
Independent statements for K07.11.reduction_irreducibility,
paper.tex:2655–2688. All maps are unital coefficient homomorphisms of
formal polynomial rings. No injectivity of the coefficient map is assumed.
Primitivity is the condition that all common coefficient divisors are units.
The fraction-field conclusion retains the source's UFD hypothesis.
-/

universe u v w

namespace Specs.D07.Ch11.ReductionIrreducibility

open Polynomial

def MonicReduction : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (φ : R →+* S) (f : R[X]),
    f.Monic → Irreducible (f.map φ) → Irreducible f

def IntegerReduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : ℤ[X]), f.Monic →
    Irreducible (f.map (Int.castRingHom (ZMod p))) →
    Irreducible f ∧ Irreducible (f.map (algebraMap ℤ ℚ))

/-- Survival of the product's leading coefficient forces survival of both
factor leading coefficients. Both formal and natural degrees are retained,
including the positive-degree condition used in the reduction argument. -/
def FactorDegreesPreserved : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (φ : R →+* S) (f g h : R[X]),
    f = g * h → φ f.leadingCoeff ≠ 0 →
      φ g.leadingCoeff ≠ 0 ∧ φ h.leadingCoeff ≠ 0 ∧
      (g.map φ).degree = g.degree ∧ (h.map φ).degree = h.degree ∧
      (g.map φ).natDegree = g.natDegree ∧ (h.map φ).natDegree = h.natDegree ∧
      (0 < g.natDegree → 0 < (g.map φ).natDegree) ∧
      (0 < h.natDegree → 0 < (h.map φ).natDegree)

def PrimitiveReduction : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    (φ : R →+* S) (f : R[X]), f.IsPrimitive → φ f.leadingCoeff ≠ 0 →
    Irreducible (f.map φ) → Irreducible f

def PrimitiveReductionFraction : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing S] [IsDomain S]
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K]
    (φ : R →+* S) (f : R[X]), f.IsPrimitive → φ f.leadingCoeff ≠ 0 →
    Irreducible (f.map φ) →
    Irreducible f ∧ Irreducible (f.map (algebraMap R K))

/-- Even when degree is preserved, dropping primitivity invalidates the test. -/
def NonprimitiveCounterexample : Prop :=
  let f : ℤ[X] := C 2 * X + C 2
  let φ : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  ¬f.IsPrimitive ∧ ¬f.Monic ∧ f = C 2 * (X + 1) ∧
    ¬IsUnit (C (2 : ℤ)) ∧ ¬IsUnit (X + 1 : ℤ[X]) ∧ ¬Irreducible f ∧
    f.map φ = C (2 : ZMod 3) * X + C 2 ∧
    (f.map φ).degree = 1 ∧ φ f.leadingCoeff ≠ 0 ∧
    Irreducible (f.map φ)

/-- Primitivity alone does not suffice when reduction lowers the degree. -/
def DegreeDropCounterexample : Prop :=
  let f : ℤ[X] := C 3 * X ^ 2 + C 4 * X + 1
  let φ : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  f.IsPrimitive ∧ f = (C 3 * X + 1) * (X + 1) ∧
    ¬IsUnit (C (3 : ℤ) * X + 1) ∧ ¬IsUnit (X + 1 : ℤ[X]) ∧
    ¬Irreducible f ∧ f.degree = 2 ∧
    f.map φ = (X + 1 : (ZMod 3)[X]) ∧ (f.map φ).degree = 1 ∧
    φ f.leadingCoeff = 0 ∧ Irreducible (f.map φ)

/-- A monic polynomial irreducible over Q can have reducible reduction. -/
def ConverseCounterexample : Prop :=
  let f : ℤ[X] := X ^ 2 + 1
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  f.Monic ∧ f.IsPrimitive ∧ Irreducible f ∧
    Irreducible (f.map (algebraMap ℤ ℚ)) ∧
    f.map φ = (X + 1 : (ZMod 2)[X]) ^ 2 ∧
    ¬IsUnit (X + 1 : (ZMod 2)[X]) ∧ ¬Irreducible (f.map φ)

end Specs.D07.Ch11.ReductionIrreducibility
