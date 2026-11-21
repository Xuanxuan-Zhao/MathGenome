import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.FourierTransform
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.LinearAlgebra.Basis.Defs

/-! Independent objects and statements for paper.tex 1600–1604 and 1611–1633.
The family consists of arbitrary nonzero irreducible complex representations,
with ordinary completeness, as in the upstream Fourier interface. -/
noncomputable section
universe u v w x
namespace P103.Ch08.CentralIdempotentSpecs
open scoped MonoidAlgebra
open FourierSpecs

variable {G : Type u} [Group G]

/-- The displayed character sum, in the original group basis. -/
def idempotent [Fintype G] (C : Family.{u,v} G) (i : Fin C.n) : ℂ[G] :=
  ((Module.finrank ℂ (C.space i) : ℂ) / (Fintype.card G : ℂ)) •
    ∑ g : G, MonoidAlgebra.single g
      (CharacterSpecs.characterValue (C.representation i) g⁻¹)

/-- Identity on the selected block and zero on all other blocks. -/
def block (C : Family.{u,v} G) (i : Fin C.n) : ∀ j, Module.End ℂ (C.space j) :=
  fun j => if j = i then 1 else 0

/-- Primitive among central idempotents: a central idempotent below it is
zero or itself. This excludes the zero element. -/
def PrimitiveCentral (e : ℂ[G]) : Prop :=
  e ∈ Subalgebra.center ℂ ℂ[G] ∧ e * e = e ∧ e ≠ 0 ∧
    ∀ f : ℂ[G], f ∈ Subalgebra.center ℂ ℂ[G] → f * f = f →
      f * e = f → f = 0 ∨ f = e

/-- The class sum has coefficient one exactly on the specified conjugacy class. -/
def classSum [Fintype G] (D : ConjClasses G) : ℂ[G] :=
  by
    classical
    exact ∑ g : G, if ConjClasses.mk g = D then MonoidAlgebra.single g 1 else 0

/-- The intrinsic sum of all invariant subspaces of the specified type.
No finite-dimensionality assumption is imposed on the ambient representation. -/
def isotypic {X : Type w} [AddCommGroup X] [Module ℂ X]
    (C : Family.{u,v} G) (ρ : Representation ℂ G X) (i : Fin C.n) :
    Submodule ℂ X :=
  ⨆ (U : Subrepresentation ρ) (_ : Nonempty ((C.representation i).Equiv U.toRepresentation)),
    U.toSubmodule

def blockActionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → ∀ i, action C (idempotent C i) = block C i

def centralType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → ∀ i, idempotent C i ∈ Subalgebra.center ℂ ℂ[G]

def idempotentType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → ∀ i, idempotent C i * idempotent C i = idempotent C i

def orthogonalType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → ∀ i j, i ≠ j → idempotent C i * idempotent C j = 0

def sumType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → ∑ i, idempotent C i = 1

def primitiveType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → ∀ e : ℂ[G],
      PrimitiveCentral e ↔ ∃ i, e = idempotent C i

/-- The primitive central idempotents themselves are also a basis of the center. -/
def idempotentBasisType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C →
    ∃ b : Module.Basis (Fin C.n) ℂ (Subalgebra.center ℂ ℂ[G]),
      ∀ i, (b i : ℂ[G]) = idempotent C i

def centerCoefficientsType : Prop :=
  ∀ {G : Type u} [Group G] (a : ℂ[G]),
    a ∈ Subalgebra.center ℂ ℂ[G] ↔
      ∀ g h : G, a.coeff (h * g * h⁻¹) = a.coeff g

def classSumBasisType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G],
    ∃ b : Module.Basis (ConjClasses G) ℂ (Subalgebra.center ℂ ℂ[G]),
      ∀ D, (b D : ℂ[G]) = classSum D

/-- The action is a projection onto exactly the intrinsic component. Range
and kernel give its direct-sum splitting, and it fixes the component pointwise. -/
def isotypicProjectionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C →
    ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) i,
      let p := ρ.asAlgebraHom (idempotent C i)
      LinearMap.range p = isotypic C ρ i ∧
      p * p = p ∧
      (∀ x ∈ isotypic C ρ i, p x = x) ∧
      IsCompl (isotypic C ρ i) (LinearMap.ker p)

/-- On every irreducible subrepresentation, the action is identity on this
type and zero on all other types, in any universe and dimension. -/
def simpleActionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C →
    ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X),
    Irreducible ℂ G X ρ → ∀ i,
      (Nonempty ((C.representation i).Equiv ρ) →
        ρ.asAlgebraHom (idempotent C i) = 1) ∧
      (¬ Nonempty ((C.representation i).Equiv ρ) →
        ρ.asAlgebraHom (idempotent C i) = 0)

/-- For every internal semisimple decomposition (including an infinite one),
the intrinsic component is the sum of its summands of the specified type.
Consequently the summand is independent of the decomposition. -/
def decompositionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C →
    ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
      {J : Type x} (U : J → Subrepresentation ρ),
      (∀ j, Irreducible ℂ G (U j).toSubmodule (U j).toRepresentation) →
      iSupIndep (fun j => (U j).toSubmodule) →
      (⨆ j, (U j).toSubmodule) = ⊤ → ∀ i,
      isotypic C ρ i =
        ⨆ (j : J) (_ : Nonempty ((C.representation i).Equiv (U j).toRepresentation)), (U j).toSubmodule

end P103.Ch08.CentralIdempotentSpecs
