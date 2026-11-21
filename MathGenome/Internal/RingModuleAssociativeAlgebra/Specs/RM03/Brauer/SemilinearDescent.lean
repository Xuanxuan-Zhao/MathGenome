import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.GaloisDescent
import Mathlib.RingTheory.TensorProduct.Maps

/-! Semilinear descent in RM03-C04.13, including base change of equivariant maps. -/

open scoped TensorProduct

universe u v w w'

namespace RM03.Brauer.SemilinearDescent

open _root_.LieAlgebrasAndRepresentations.GaloisDescent (SemilinearAction)

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- A genuine semilinear action by unital ring automorphisms of a possibly
noncommutative algebra. -/
structure AlgebraAction (A : Type w) [Ring A] [Algebra K A]
    extends SemilinearAction k K A where
  map_one (g : Gal(K/k)) : act g 1 = 1
  map_mul (g : Gal(K/k)) (x y : A) : act g (x * y) = act g x * act g y

namespace AlgebraAction

variable {k K} {A : Type w} [Ring A] [Algebra K A]
variable (ρ : AlgebraAction k K A)

/-- The underlying ring equivalence of an action operator. -/
def actRingEquiv (g : Gal(K/k)) : A ≃+* A :=
  { ρ.act g with map_mul' := ρ.map_mul g }

variable [Algebra k A] [IsScalarTower k K A]

/-- The fixed vectors, with their induced unital base-field algebra structure.
The base-field structures on scalar towers are the restrictions of scalars. -/
def fixedSubalgebra : Subalgebra k A :=
  ρ.toSemilinearAction.fixed.toSubalgebra
    (fun g => ρ.map_one g)
    (fun x y hx hy g => by rw [ρ.map_mul, hx g, hy g])

@[simp]
theorem mem_fixedSubalgebra {x : A} :
    x ∈ ρ.fixedSubalgebra ↔ ∀ g, ρ.act g x = x := Iff.rfl

/-- The canonical algebra map, extending the inclusion of fixed points. -/
def descentMap : (K ⊗[k] ρ.fixedSubalgebra) →ₐ[K] A :=
  AlgHom.liftEquiv k K ρ.fixedSubalgebra A ρ.fixedSubalgebra.val

@[simp]
theorem descentMap_tmul (a : K) (x : ρ.fixedSubalgebra) :
    ρ.descentMap (a ⊗ₜ[k] x) = a • (x : A) := rfl

variable {B : Type w'} [Ring B] [Algebra K B]
variable (τ : AlgebraAction k K B)

/-- Equivariance for the given two actions of the same Galois group. -/
def Equivariant (f : A →ₐ[K] B) : Prop :=
  ∀ (g : Gal(K/k)) (x : A), f (ρ.act g x) = τ.act g (f x)

variable [Algebra k B] [IsScalarTower k K B]

/-- Restriction of an equivariant map to the two fixed subalgebras. -/
def restrictHom (f : A →ₐ[K] B) (hf : ρ.Equivariant τ f) :
    ρ.fixedSubalgebra →ₐ[k] τ.fixedSubalgebra :=
  ((f.restrictScalars k).comp ρ.fixedSubalgebra.val).codRestrict τ.fixedSubalgebra
    (fun x g => by
      change τ.act g (f (x : A)) = f (x : A)
      rw [← hf g, (ρ.mem_fixedSubalgebra.mp x.property) g])

end AlgebraAction
end RM03.Brauer.SemilinearDescent

namespace Specs.RM03.Brauer.SemilinearDescent

open _root_.LieAlgebrasAndRepresentations.GaloisDescent (SemilinearAction)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open Module

def fixed_span_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V] [FiniteDimensional K V]
    (ρ : SemilinearAction k K V),
    Submodule.span K (ρ.fixed : Set V) = ⊤

def fixed_basis_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {ι : Type w'} [Field k] [Field K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V] [FiniteDimensional K V]
    (ρ : SemilinearAction k K V) (b : Basis ι K V) (_hb : ∀ i, b i ∈ ρ.fixed),
    ∃ c : Basis ι k ρ.fixed, ∀ i, (c i : V) = b i

def linear_descent_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V] [FiniteDimensional K V]
    (ρ : SemilinearAction k K V),
    ∃ e : (K ⊗[k] ρ.fixed) ≃ₗ[K] V, ∀ (a : K) (x : ρ.fixed),
      e (a ⊗ₜ[k] x) = a • (x : V)

def algebra_descent_type : Prop :=
  ∀ {k : Type u} {K : Type v} {A : Type w} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [Ring A] [Algebra K A]
    [Algebra k A] [IsScalarTower k K A] [FiniteDimensional K A]
    (ρ : AlgebraAction k K A),
    ∃ e : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K] A, ∀ (a : K) (x : ρ.fixedSubalgebra),
      e (a ⊗ₜ[k] x) = a • (x : A)

def equivariant_restriction_type : Prop :=
  ∀ {k : Type u} {K : Type v} {A : Type w} {B : Type w'}
    [Field k] [Field K] [Algebra k K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Algebra k A] [IsScalarTower k K A] [Algebra k B] [IsScalarTower k K B]
    (ρ : AlgebraAction k K A) (τ : AlgebraAction k K B)
    (f : A →ₐ[K] B) (hf : ρ.Equivariant τ f),
    (∀ x : ρ.fixedSubalgebra, (ρ.restrictHom τ f hf x : B) = f (x : A)) ∧
    τ.descentMap.comp (Algebra.TensorProduct.map (AlgHom.id K K) (ρ.restrictHom τ f hf)) =
      f.comp ρ.descentMap

end Specs.RM03.Brauer.SemilinearDescent
