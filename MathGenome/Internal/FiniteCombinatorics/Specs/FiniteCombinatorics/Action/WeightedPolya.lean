import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.WeightedFixedColorings
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.MvPolynomial.Eval

/-! Independent specification of paper.tex W33. The integral inventory is a
natural-coefficient polynomial, so specialization requires no division.
The color multiplicity of an orbit is computed from a representative; its
independence is a theorem obligation below. Empty sets are allowed throughout. -/
namespace FiniteCombinatorics.WeightedPolyaSpec
open scoped BigOperators
universe u v w z
attribute [local instance] FixedColoringsSpec.coloringAction Classical.propDecidable
variable (G : Type u) (X : Type v) (C : Type w) [Group G] [MulAction G X]
variable [Fintype X] [Fintype C]
noncomputable local instance orbitsFintype :
    Fintype (MulAction.orbitRel.Quotient G (X → C)) := Fintype.ofFinite _

noncomputable def orbitEnumerator : MvPolynomial C ℕ :=
  ∑ O : MulAction.orbitRel.Quotient G (X → C),
    WeightedFixedColoringsSpec.orbitWeight G X C O

noncomputable def colorMultiplicity (f : X → C) : C →₀ ℕ :=
  ∑ x, Finsupp.single (f x) 1

noncomputable def orbitMultiplicity (O : MulAction.orbitRel.Quotient G (X → C)) : C →₀ ℕ :=
  colorMultiplicity X C O.out

/-- Variable i of the cycle index is s_(i+1). -/
noncomputable def substitutedCycleIndex [Fintype G] : MvPolynomial C ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (Fintype.card X) => ∑ c : C, MvPolynomial.X c ^ (i.val + 1))
    (CycleIndexSpec.cycleIndex G X)

-- Full expected theorem types; none is an assumed certificate.
def MultiplicityCounts : Prop := ∀ (X : Type v) (C : Type w) [Fintype X]
    (f : X → C) (c : C),
  colorMultiplicity X C f c = (Finset.univ.filter (fun x => f x = c)).card

def OrbitMultiplicityMk : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] (f : X → C),
  orbitMultiplicity G X C (Quotient.mk (MulAction.orbitRel G (X → C)) f) =
    colorMultiplicity X C f

def IntegralBurnside : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] [Fintype G],
  (Fintype.card G) • orbitEnumerator G X C =
    ∑ g : G, WeightedFixedColoringsSpec.fixedWeightSum G X C g

def Substitution : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] [Fintype G],
  MvPolynomial.map (Nat.castRingHom ℚ) (orbitEnumerator G X C) =
    substitutedCycleIndex G X C

def CoefficientCounts : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] (d : C →₀ ℕ),
  (orbitEnumerator G X C).coeff d =
    (Finset.univ.filter (fun O : MulAction.orbitRel.Quotient G (X → C) =>
      orbitMultiplicity G X C O = d)).card

def RationalCoefficientCounts : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] [Fintype G] (d : C →₀ ℕ),
  (substitutedCycleIndex G X C).coeff d =
    ((Finset.univ.filter (fun O : MulAction.orbitRel.Quotient G (X → C) =>
      orbitMultiplicity G X C O = d)).card : ℚ)

def Specialization : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C]
    (R : Type z) [CommSemiring R] (weights : C → R),
  MvPolynomial.eval₂ (Nat.castRingHom R) weights (orbitEnumerator G X C) =
    ∑ O : MulAction.orbitRel.Quotient G (X → C), ∏ x : X, weights (O.out x)

def EmptyPositions : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] [IsEmpty X],
  orbitEnumerator G X C = 1

def EmptyColors : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] [Nonempty X] [IsEmpty C],
  orbitEnumerator G X C = 0

-- Types and values of the constructions.
def orbitEnumeratorType := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C], MvPolynomial C ℕ
def colorMultiplicityType := ∀ (X : Type v) (C : Type w) [Fintype X], (X → C) → C →₀ ℕ
def orbitMultiplicityType := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X],
  MulAction.orbitRel.Quotient G (X → C) → C →₀ ℕ
def substitutedCycleIndexType := ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] [Fintype G], MvPolynomial C ℚ
end FiniteCombinatorics.WeightedPolyaSpec
