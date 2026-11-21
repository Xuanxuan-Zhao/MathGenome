import MathGenome.Internal.Specs.D07.Ch09.QuotientProjection

/-!
Independent specifications for K07.09.quotient_trivial, paper.tex:1547–1554.
The quotient is the canonical additive-coset ring from QuotientConstruction.
`Subsingleton` expresses triviality, and `I ≠ ⊤` expresses properness.
Every statement allows noncommutative rings and the zero ring; the ideal
is two-sided but is not assumed proper.
-/

universe u

namespace Specs.D07.Ch09.QuotientTrivial

/-- The first step of the source's triviality criterion. -/
def TrivialIffOneEqZero : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    Subsingleton (R ⧸ I) ↔ (1 : R ⧸ I) = 0

/-- The quotient identity vanishes exactly when the ideal contains `1`. -/
def OneEqZeroIffOneMem : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    (1 : R ⧸ I) = 0 ↔ (1 : R) ∈ I

def TrivialIffTop : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    Subsingleton (R ⧸ I) ↔ I = ⊤

/-- Properness is precisely the condition for a nontrivial quotient. -/
def NontrivialIffProper : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    Nontrivial (R ⧸ I) ↔ I ≠ ⊤

/-- Equality of zero-ideal classes reduces to equality of representatives. -/
def ZeroIdealClassEq : Prop :=
  ∀ (R : Type u) [Ring R] (a b : R),
    Ideal.Quotient.mk (⊥ : Ideal R) a = Ideal.Quotient.mk ⊥ b ↔ a = b

/-- The source's map `[a] ↦ a` is a unital ring isomorphism whose inverse
is the natural projection. `RingEquiv` records bijectivity and preservation
of the ring operations, and its inverse is a ring isomorphism as well. -/
def ZeroIdealQuotientEquivalence : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ e : (R ⧸ (⊥ : Ideal R)) ≃+* R,
      (∀ a : R, e (Ideal.Quotient.mk ⊥ a) = a) ∧
      (∀ a : R, e.symm a = Ideal.Quotient.mk ⊥ a)

end Specs.D07.Ch09.QuotientTrivial
