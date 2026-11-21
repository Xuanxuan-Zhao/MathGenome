import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Group.Units.Opposite

/-!
Independent specifications for the radical assertions of paper.tex, Theorem 3.2
(lines 607–641), under the global conventions at line 47.
`Ideal R` in Mathlib is a LEFT ideal even when `R` is noncommutative;
`Ideal.IsTwoSided` is an additional property. No nonzero-ring assumption is made.
A right ideal is a left ideal over `Rᵐᵒᵖ`.

The intersection of annihilators is indexed by simple modules in the scalar
universe. Every simple module is isomorphic to a quotient of `R`, so these
represent all isomorphism classes. The separate arbitrary-universe annihilation
statement also asserts the forward implication for every simple module directly.
Nakayama's assertions are allocated to the separate goal `c03_nakayama`.
-/

universe u v

namespace P103.Specs.Ch03.JacobsonRadical

abbrev radical (R : Type u) [Ring R] : Ideal R := Ring.jacobson R

def jacobsonType := ∀ (R : Type u) [Ring R], Ideal R

def jacobsonValue : jacobsonType := fun R => radical R

def maximal_intersectionType : Prop :=
  ∀ (R : Type u) [Ring R], radical R = sInf {L : Ideal R | L.IsMaximal}

/-- The intersection of the annihilators of all simple left modules. -/
def simpleIntersection (R : Type u) [Ring R] : Ideal R :=
  ⨅ (M : Type u) (_ : AddCommGroup M) (_ : Module R M) (_ : IsSimpleModule R M),
    Module.annihilator R M

def simple_annihilator_intersectionType : Prop :=
  ∀ (R : Type u) [Ring R], radical R = simpleIntersection R

def annihilates_simpleType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (x : R), x ∈ radical R → x ∈ Module.annihilator R M

def two_sidedType : Prop :=
  ∀ (R : Type u) [Ring R], (radical R).IsTwoSided

/-- Explicit closure on both sides, using the original multiplication of `R`. -/
def mul_memType : Prop :=
  ∀ (R : Type u) [Ring R] (x r : R), x ∈ radical R →
    r * x ∈ radical R ∧ x * r ∈ radical R

def unit_criterionType : Prop :=
  ∀ (R : Type u) [Ring R] (x : R),
    x ∈ radical R ↔ ∀ r : R, IsUnit (1 - r * x)

def one_sub_isUnitType : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), a ∈ radical R → IsUnit (1 - a)

/-- Right radical: the intersection of maximal right ideals, viewed in `R`. -/
def rightRadical (R : Type u) [Ring R] : Set R :=
  {x | MulOpposite.op x ∈ sInf {L : Ideal Rᵐᵒᵖ | L.IsMaximal}}

def left_eq_rightType : Prop :=
  ∀ (R : Type u) [Ring R], (radical R : Set R) = rightRadical R

/-- In a zero ring there are no proper maximal left ideals; their empty infimum is top. -/
def zero_ringType : Prop :=
  ∀ (R : Type u) [Ring R] [Subsingleton R],
    {L : Ideal R | L.IsMaximal} = ∅ ∧ radical R = ⊤

end P103.Specs.Ch03.JacobsonRadical
