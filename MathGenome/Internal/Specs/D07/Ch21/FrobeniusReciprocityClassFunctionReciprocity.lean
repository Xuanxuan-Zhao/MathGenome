import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Basic.Complex.BigOperators

/-!
Independent interface for the class-function part of Frobenius reciprocity,
paper.tex:6569–6627. All functions are arbitrary complex-valued functions;
class invariance is an explicit hypothesis, with no character assumption.
The pairing is linear in its first argument.
-/

noncomputable section
open scoped BigOperators Classical ComplexConjugate

namespace Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity

universe u

/-- Constancy on conjugacy classes, using conjugation `a * g * a⁻¹`. -/
def IsClassFunction {G : Type u} [Group G] (f : G → ℂ) : Prop :=
  ∀ a g : G, f (a * g * a⁻¹) = f g

/-- Restriction along the subgroup inclusion. -/
def restrict {G : Type u} [Group G] (H : Subgroup G) (k : G → ℂ) : H → ℂ :=
  fun h => k h

/-- The linear-first Hermitian pairing: `|G|⁻¹ ∑ g, f g * conj (k g)`. -/
def pairing {G : Type u} [Fintype G] (f k : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f g * conj (k g)

/-- Extension by zero, including the proof needed to evaluate `f` on `H`. -/
def extendZero {G : Type u} [Group G] (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  if hg : g ∈ H then f ⟨g, hg⟩ else 0

/-- Exactly the source sum over `x⁻¹ * g * x ∈ H`, with ineligible summands zero. -/
def induce {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  fun g => (Fintype.card H : ℂ)⁻¹ * ∑ x : G, extendZero H f (x⁻¹ * g * x)

-- Expected types and values for the public definitions.
def ClassPredicateType : Type (u + 1) := ∀ (G : Type u) [Group G], (G → ℂ) → Prop
def classPredicateValue : ClassPredicateType.{u} := fun _ _ => IsClassFunction

def RestrictionType : Type (u + 1) :=
  ∀ (G : Type u) [Group G] (H : Subgroup G), (G → ℂ) → (H → ℂ)
def restrictionValue : RestrictionType.{u} := fun _ _ => restrict

def PairingType : Type (u + 1) := ∀ (G : Type u) [Fintype G], (G → ℂ) → (G → ℂ) → ℂ
def pairingValue : PairingType.{u} := fun _ _ => pairing

def InductionType : Type (u + 1) :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G), (H → ℂ) → (G → ℂ)
def inductionValue : InductionType.{u} := fun _ _ _ => induce

/-- Restriction preserves conjugacy invariance. -/
def RestrictionIsClassFunction : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (k : G → ℂ),
    IsClassFunction k → IsClassFunction (restrict H k)

/-- Induction of every complex class function on every subgroup of a finite group
is again a class function. No normality or properness assumption on `H`. -/
def InductionIsClassFunction : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ),
    IsClassFunction f → IsClassFunction (induce H f)

/-- Frobenius reciprocity for arbitrary class functions and the source's
linear-first Hermitian pairing, without representation-theoretic hypotheses. -/
def Reciprocity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) (k : G → ℂ),
    IsClassFunction f → IsClassFunction k →
      pairing (induce H f) k = pairing f (restrict H k)

end Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity
