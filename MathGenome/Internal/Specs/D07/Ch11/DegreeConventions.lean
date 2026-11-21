import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
Independent specification of K07.11.degree_conventions
(paper.tex:2184–2200; chapters/M07.11.tex:39–55).

The coefficient object is the canonical `Polynomial R` from the preceding
entry. Rings may be noncommutative or trivial. Bottom in `WithBot ℕ` denotes
minus infinity, distinct from the natural number zero. The four expected
values spell out the definitions; the propositions record their meaning and
the boundary cases asserted in the source. Degree arithmetic belongs to the
separate entry K07.11.degree_arithmetic.
-/

universe u

namespace Specs.D07.Ch11.DegreeConventions

def DegreeType : Type (u + 1) :=
  {R : Type u} → [Ring R] → Polynomial R → WithBot ℕ

noncomputable def degreeValue : DegreeType.{u} :=
  fun f => f.support.max

def NatDegreeType : Type (u + 1) :=
  {R : Type u} → [Ring R] → Polynomial R → ℕ

noncomputable def natDegreeValue : NatDegreeType.{u} :=
  fun f => f.degree.unbotD 0

def LeadingCoefficientType : Type (u + 1) :=
  {R : Type u} → [Ring R] → Polynomial R → R

noncomputable def leadingCoefficientValue : LeadingCoefficientType.{u} :=
  fun f => f.coeff f.natDegree

def MonicType : Type (u + 1) :=
  {R : Type u} → [Ring R] → Polynomial R → Prop

noncomputable def monicValue : MonicType.{u} :=
  fun f => f.leadingCoeff = 1

/-- A finite degree is exactly the largest nonzero coefficient index. -/
def DegreeCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R) (n : ℕ),
    f.degree = (n : WithBot ℕ) ↔
      f.coeff n ≠ 0 ∧ ∀ i : ℕ, f.coeff i ≠ 0 → i ≤ n

def DegreeZero : Prop :=
  ∀ (R : Type u) [Ring R], (0 : Polynomial R).degree = ⊥

def DegreeBottomIff : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R), f.degree = ⊥ ↔ f = 0

/-- The extended degree addition convention, also when both entries are bottom. -/
def BottomAddition : Prop :=
  ∀ n : WithBot ℕ, (⊥ : WithBot ℕ) + n = ⊥ ∧ n + ⊥ = ⊥

def NatDegreeAgreement : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R), f ≠ 0 →
    f.degree = (f.natDegree : WithBot ℕ)

def NatDegreeZero : Prop :=
  ∀ (R : Type u) [Ring R], (0 : Polynomial R).natDegree = 0

def LeadingCoefficientAtDegree : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R),
    f.coeff f.natDegree = f.leadingCoeff

def LeadingCoefficientZero : Prop :=
  ∀ (R : Type u) [Ring R], (0 : Polynomial R).leadingCoeff = 0

def NonzeroLeadingCoefficient : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R),
    f ≠ 0 → f.leadingCoeff ≠ 0

def MonicCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R),
    f.Monic ↔ f.leadingCoeff = 1

def MonicNonzero : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R] (f : Polynomial R),
    f.Monic → f ≠ 0

def ZeroMonicIff : Prop :=
  ∀ (R : Type u) [Ring R], (0 : Polynomial R).Monic ↔ (0 : R) = 1

def ZeroRingMonic : Prop :=
  ∀ (R : Type u) [Ring R] [Subsingleton R], (0 : Polynomial R).Monic

/-- No unit, domain or commutativity assumption is placed on the nonzero constant. -/
def ConstantDegree : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), a ≠ 0 →
    (Polynomial.C a).degree = (0 : WithBot ℕ)

def ConstantNatDegree : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), (Polynomial.C a).natDegree = 0

end Specs.D07.Ch11.DegreeConventions
