import MathGenome.Internal.Specs.D05.M15.TensorAlgebra
import MathGenome.Internal.Specs.D05.M06.QuotientLift
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.GroupTheory.Perm.Sign

/-! Independent statements for paper.tex:2997–3003. All quotients below are
algebraic, over arbitrary fields and arbitrary-dimensional spaces. Relations
are differences, with no averaging or factorial hypothesis. The adjacent indices
specify two consecutive slots; all other slots are arbitrary fixed context. -/
namespace Specs.D05.M15.Symmetric
universe u v w
open scoped TensorProduct

section Objects
variable (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V]

def commutatorIdeal : TwoSidedIdeal (_root_.TensorAlgebra K V) :=
  TwoSidedIdeal.span (Set.range fun uv : V × V =>
    _root_.TensorAlgebra.ι K uv.1 * _root_.TensorAlgebra.ι K uv.2 -
      _root_.TensorAlgebra.ι K uv.2 * _root_.TensorAlgebra.ι K uv.1)

/-- The standard congruence quotient, whose ideal presentation is an obligation below. -/
abbrev symmetricAlgebra := _root_.SymmetricAlgebra K V

/-- Degree-p relations with arbitrary context on both sides of an adjacent swap. -/
def adjacentRelations (p : ℕ) : Submodule K (TensorPower K p V) :=
  Submodule.span K {t | ∃ (x : Fin p → V) (i j : Fin p),
    j.val = i.val + 1 ∧ t = PiTensorProduct.tprod K x -
      PiTensorProduct.tprod K (x ∘ Equiv.swap i j)}

abbrev symmetricPower (p : ℕ) := TensorPower K p V ⧸ adjacentRelations K V p

def elementary (p : ℕ) : MultilinearMap K (fun _ : Fin p => V) (symmetricPower K V p) :=
  (adjacentRelations K V p).mkQ.compMultilinearMap (PiTensorProduct.tprod K)

def homogeneousMap (p : ℕ) : TensorPower K p V →ₗ[K] symmetricAlgebra K V :=
  (_root_.SymmetricAlgebra.algHom K V).toLinearMap.comp TensorPower.toTensorAlgebra

end Objects

-- The following value specifications pin down all newly exposed objects.
def commutatorIdeal_type := ∀ (K : Type u) (V : Type v)
  [Field K] [AddCommGroup V] [Module K V], TwoSidedIdeal (_root_.TensorAlgebra K V)
def commutatorIdeal_value : commutatorIdeal_type.{u,v} := commutatorIdeal

def symmetricAlgebra_type := ∀ (K : Type u) (V : Type v)
  [Field K] [AddCommGroup V] [Module K V], Type (max u v)
def symmetricAlgebra_value : symmetricAlgebra_type.{u,v} := symmetricAlgebra

def adjacentRelations_type := ∀ (K : Type u) (V : Type v)
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ), Submodule K (TensorPower K p V)
def adjacentRelations_value : adjacentRelations_type.{u,v} := adjacentRelations

def symmetricPower_type := ∀ (K : Type u) (V : Type v)
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ), Type (max u v)
def symmetricPower_value : symmetricPower_type.{u,v} := symmetricPower

def elementary_type := ∀ (K : Type u) (V : Type v)
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ),
    MultilinearMap K (fun _ : Fin p => V) (symmetricPower K V p)
def elementary_value : elementary_type.{u,v} := elementary

def homogeneousMap_type := ∀ (K : Type u) (V : Type v)
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ),
    TensorPower K p V →ₗ[K] symmetricAlgebra K V
def homogeneousMap_value : homogeneousMap_type.{u,v} := homogeneousMap

def ideal_congruence : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    (commutatorIdeal K V).ringCon = _root_.TensorAlgebra.symRingCon K V

def quotient_eq_iff : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (x y : _root_.TensorAlgebra K V),
    _root_.SymmetricAlgebra.algHom K V x = _root_.SymmetricAlgebra.algHom K V y ↔
      x - y ∈ commutatorIdeal K V

def commutative : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (x y : symmetricAlgebra K V), x * y = y * x

/-- Necessity as well as sufficiency for a possibly noncommutative target. -/
def universal_property : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A]
    (f : V →ₗ[K] A),
    (∀ u v, Commute (f u) (f v)) ↔
      ∃! F : symmetricAlgebra K V →ₐ[K] A,
        ∀ v, F (_root_.SymmetricAlgebra.ι K V v) = f v

def commutative_universal : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [CommRing A] [Algebra K A]
    (f : V →ₗ[K] A),
    ∃! F : symmetricAlgebra K V →ₐ[K] A,
      ∀ v, F (_root_.SymmetricAlgebra.ι K V v) = f v

def tensor_lift_kills_ideal : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A]
    (f : V →ₗ[K] A), (∀ u v, Commute (f u) (f v)) →
    ∀ t ∈ commutatorIdeal K V, _root_.TensorAlgebra.lift K f t = 0

/-- Symmetry under consecutive swaps is equivalent to invariance under every permutation. -/
def symmetry_iff_adjacent : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : ℕ) (b : MultilinearMap K (fun _ : Fin p => V) W),
    (∀ (x : Fin p → V) (i j : Fin p), j.val = i.val + 1 →
      b (x ∘ Equiv.swap i j) = b x) ↔
    (∀ (x : Fin p → V) (σ : Equiv.Perm (Fin p)), b (x ∘ σ) = b x)

/-- All permutations give differences in the adjacent-relation subspace. -/
def permutation_relation : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (x : Fin p → V) (σ : Equiv.Perm (Fin p)),
      PiTensorProduct.tprod K x - PiTensorProduct.tprod K (x ∘ σ) ∈
        adjacentRelations K V p

def elementary_symmetric : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (x : Fin p → V) (σ : Equiv.Perm (Fin p)),
      elementary K V p (x ∘ σ) = elementary K V p x

/-- Symmetric multilinear maps annihilate exactly the required generators. -/
def annihilates_relations : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : ℕ) (b : MultilinearMap K (fun _ : Fin p => V) W),
    adjacentRelations K V p ≤ LinearMap.ker (PiTensorProduct.lift b) ↔
      ∀ (x : Fin p → V) (σ : Equiv.Perm (Fin p)), b (x ∘ σ) = b x

def power_universal : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : ℕ) (b : MultilinearMap K (fun _ : Fin p => V) W),
    (∀ (x : Fin p → V) (σ : Equiv.Perm (Fin p)), b (x ∘ σ) = b x) ↔
      ∃! L : symmetricPower K V p →ₗ[K] W,
        ∀ x, L (elementary K V p x) = b x

/-- The ideal is homogeneous for the accepted tensor-algebra grading. -/
def ideal_homogeneous : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (t : _root_.TensorAlgebra K V), t ∈ commutatorIdeal K V →
      ∀ p : ℕ, TensorPower.toTensorAlgebra (_root_.TensorAlgebra.equivDirectSum t p) ∈
        commutatorIdeal K V

/-- Crucial bridge: these are exactly the degree-p relations in the algebra quotient. -/
def homogeneous_kernel : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), LinearMap.ker (homogeneousMap K V p) = adjacentRelations K V p

def power_equiv_homogeneous : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), ∃ E : symmetricPower K V p ≃ₗ[K] LinearMap.range (homogeneousMap K V p),
      ∀ x, (E (elementary K V p x) : symmetricAlgebra K V) =
        homogeneousMap K V p (PiTensorProduct.tprod K x)

def degree_zero : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    ∃ E : symmetricPower K V 0 ≃ₗ[K] K,
      ∀ x : Fin 0 → V, E (elementary K V 0 x) = 1

end Specs.D05.M15.Symmetric
