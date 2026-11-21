import MathGenome.Internal.Specs.D07.Ch08.IdealDefinition
import Mathlib.RingTheory.Ideal.Maximal

/-!
Independent specifications for K07.09.maximal_ideal (paper.tex:1642–1646).
The chapter assumes commutativity from paper.tex:1631 onward. The main
predicate therefore uses `Ideal.IsMaximal` only over a commutative ring.
The two general-ring predicates make the source's distinction explicit:
Mathlib's ideal lattice consists of left ideals, whereas maximal two-sided
ideals are tested only against two-sided ideals. Properness is required
in every case, without any ambient `Nontrivial` assumption.
-/

universe u

namespace Specs.D07.Ch09.MaximalIdeal

/-- Type of the main, commutative maximal-ideal predicate. -/
def MaximalPredicateType : Type (u + 1) :=
  {R : Type u} → [CommRing R] → Ideal R → Prop

/-- Canonical library predicate, with its commutative applicability explicit. -/
def maximalPredicateValue : MaximalPredicateType.{u} :=
  fun {_} _ M => M.IsMaximal

/-- Type of the maximal-left-ideal predicate for an arbitrary ring. -/
def MaximalLeftPredicateType : Type (u + 1) :=
  {R : Type u} → [Ring R] → Ideal R → Prop

/-- Mathlib's `Ideal.IsMaximal` tests all larger left ideals. -/
def maximalLeftPredicateValue : MaximalLeftPredicateType.{u} :=
  fun {_} _ M => M.IsMaximal

/-- Type of the maximal-two-sided-ideal predicate for an arbitrary ring. -/
def MaximalTwoSidedPredicateType : Type (u + 1) :=
  {R : Type u} → [Ring R] → Ideal R → Prop

/-- The unqualified noncommutative notion: a proper two-sided ideal with
no strictly larger proper two-sided ideal. -/
def maximalTwoSidedPredicateValue : MaximalTwoSidedPredicateType.{u} :=
  fun {_} _ M => M.IsTwoSided ∧ M ≠ ⊤ ∧
    ∀ J : Ideal _, J.IsTwoSided → M < J → J = ⊤

/-- Exactly the defining conditions in the commutative chapter. -/
def MaximalCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Ideal R),
    maximalPredicateValue M ↔
      M ≠ ⊤ ∧ ¬ ∃ J : Ideal R, M < J ∧ J < ⊤

/-- Equivalent formulation using all ideals containing the given ideal. -/
def ContainingIdealCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Ideal R),
    maximalPredicateValue M ↔
      M ≠ ⊤ ∧ ∀ J : Ideal R, M ≤ J → J = M ∨ J = ⊤

/-- The same lattice predicate over a general ring means maximal *left* ideal. -/
def MaximalLeftCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (M : Ideal R),
    maximalLeftPredicateValue M ↔
      M ≠ ⊤ ∧ ¬ ∃ J : Ideal R, M < J ∧ J < ⊤

/-- In the two-sided notion, only two-sided intermediate ideals are excluded. -/
def MaximalTwoSidedCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (M : Ideal R),
    maximalTwoSidedPredicateValue M ↔
      M.IsTwoSided ∧ M ≠ ⊤ ∧
        ¬ ∃ J : Ideal R, J.IsTwoSided ∧ M < J ∧ J < ⊤

/-- Over a commutative ring the left and two-sided notions both agree
with the main definition. This does not assert agreement over a general ring. -/
def CommutativeCoincidence : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Ideal R),
    (maximalPredicateValue M ↔ maximalLeftPredicateValue M) ∧
      (maximalPredicateValue M ↔ maximalTwoSidedPredicateValue M)

/-- No maximal ideal is the whole ring; in particular it excludes one. -/
def Properness : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Ideal R),
    maximalPredicateValue M → M ≠ ⊤ ∧ (1 : R) ∉ M

/-- The allowed zero ring has no maximal ideals. -/
def ZeroRing : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R] (M : Ideal R),
    ¬ maximalPredicateValue M

end Specs.D07.Ch09.MaximalIdeal
