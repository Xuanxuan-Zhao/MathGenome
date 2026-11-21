import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic

/-!
Independent specifications for paper.tex, Chapter 23,
`d11:23:vector-lattice-stone` (definition and its closure assertions).
The underlying objects are subspaces of everywhere finite real functions.
Stone truncation is a separate predicate; it does not include a unit assumption.
-/

universe u

namespace D11.Ch23.Specs

/-- A vector subspace of actual functions, closed under pointwise min and max. -/
def IsVectorLattice {X : Type u} (V : Submodule ℝ (X → ℝ)) : Prop :=
  (∀ f ∈ V, ∀ g ∈ V, (fun x => min (f x) (g x)) ∈ V) ∧
  (∀ f ∈ V, ∀ g ∈ V, (fun x => max (f x) (g x)) ∈ V)

/-- Stone's condition concerns truncations only, even if the unit is absent. -/
def IsStone {X : Type u} (V : Submodule ℝ (X → ℝ)) : Prop :=
  ∀ f ∈ V, (fun x => min (f x) 1) ∈ V

def VectorLatticePredicateType :=
  ∀ {X : Type u}, Submodule ℝ (X → ℝ) → Prop

def StonePredicateType :=
  ∀ {X : Type u}, Submodule ℝ (X → ℝ) → Prop

/-- Positive part is max(f,0), pointwise. -/
def PositivePartMem : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), IsVectorLattice V →
    ∀ f ∈ V, (fun x => max (f x) 0) ∈ V

/-- Negative part is max(-f,0), pointwise. -/
def NegativePartMem : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), IsVectorLattice V →
    ∀ f ∈ V, (fun x => max (-f x) 0) ∈ V

def AbsMem : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), IsVectorLattice V →
    ∀ f ∈ V, (fun x => |f x|) ∈ V

/-- Truncation at any strictly positive real threshold. -/
def MinConstMem : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), IsStone V →
    ∀ f ∈ V, ∀ b : ℝ, 0 < b → (fun x => min (f x) b) ∈ V

/-- On an empty domain, the only function is the zero function. -/
def EmptyDomainFunction : Prop :=
  ∀ {X : Type u} [IsEmpty X] (f : X → ℝ), f = 0

/-- Every subspace on an empty domain meets both closure conditions. -/
def EmptyDomainConditions : Prop :=
  ∀ {X : Type u} [IsEmpty X] (V : Submodule ℝ (X → ℝ)),
    IsVectorLattice V ∧ IsStone V

/-- A concrete witness that Stone's condition does not require a constant unit. -/
def StoneWithoutUnit : Prop :=
  IsVectorLattice (⊥ : Submodule ℝ (Unit → ℝ)) ∧
    IsStone (⊥ : Submodule ℝ (Unit → ℝ)) ∧
    (fun _ : Unit => (1 : ℝ)) ∉ (⊥ : Submodule ℝ (Unit → ℝ))

end D11.Ch23.Specs
