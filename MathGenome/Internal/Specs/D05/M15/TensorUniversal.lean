import MathGenome.Internal.Specs.D05.M15.Multilinear
import MathGenome.Internal.Specs.D05.M06.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
Independent statements for K05.15.tensor_universal, paper.tex:2711–2712.

All spaces are algebraic vector spaces over the same arbitrary field. No
finite-dimensional or characteristic hypothesis is used. Bilinear maps are
curried `LinearMap`s; finite multilinear maps use the upstream canonical
`MultilinearMap`. The universal predicates quantify over every target space
in the ambient universe, including the quotient of the proposed tensor space.
They assume neither spanning nor an equivalence with a canonical tensor model.
The spanning consequences apply to any space satisfying these predicates.
-/

namespace Specs.D05.M15.TensorUniversal

universe u
open scoped TensorProduct

/-- The paper's defining property for a specified bilinear map into U. -/
def IsTensorProduct {K V W U : Type u} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U] (τ : V →ₗ[K] W →ₗ[K] U) : Prop :=
  ∀ (H : Type u) [AddCommGroup H] [Module K H] (b : V →ₗ[K] W →ₗ[K] H),
    ∃! f : U →ₗ[K] H, ∀ v w, f (τ v w) = b v w

/-- The analogous definition for any finite family of factors, including zero. -/
def IsMultitensorProduct {K I : Type u} {V : I → Type u} {U : Type u}
    [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup U] [Module K U] (τ : MultilinearMap K V U) : Prop :=
  ∀ (H : Type u) [AddCommGroup H] [Module K H] (b : MultilinearMap K V H),
    ∃! f : U →ₗ[K] H, ∀ v, f (τ v) = b v

/-- Type of the canonical binary tensor-space constructor. -/
def tensorProduct_type : Type (u + 1) :=
  (K V W : Type u) → [Field K] → [AddCommGroup V] → [Module K V] →
    [AddCommGroup W] → [Module K W] → Type u

def tensorProduct_value : tensorProduct_type.{u} :=
  fun K V W _ _ _ _ _ => TensorProduct K V W

/-- The defining property holds for the canonical space and its elementary map. -/
def binary_universal : Prop :=
  ∀ {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W], IsTensorProduct (TensorProduct.mk K V W)

/-- The representation is linear in the bilinear map, with both directions fixed. -/
def binary_linearization : Prop :=
  ∀ {K V W H : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup H] [Module K H],
    ∃ E : (V →ₗ[K] W →ₗ[K] H) ≃ₗ[K] ((V ⊗[K] W) →ₗ[K] H),
      (∀ b v w, E b (v ⊗ₜ[K] w) = b v w) ∧
      (∀ f v w, E.symm f v w = f (v ⊗ₜ[K] w))

/-- Uniqueness in the universal property forces the elementary images to span. -/
def elementary_span_of_universal : Prop :=
  ∀ {K V W U : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (τ : V →ₗ[K] W →ₗ[K] U), IsTensorProduct τ →
    Submodule.span K (Set.range (fun vw : V × W => τ vw.1 vw.2)) = ⊤

/-- Maps out of any tensor product agree if they agree on elementary tensors. -/
def linear_ext_of_universal : Prop :=
  ∀ {K V W U H : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup H] [Module K H]
    (τ : V →ₗ[K] W →ₗ[K] U), IsTensorProduct τ →
    ∀ f g : U →ₗ[K] H, (∀ v w, f (τ v w) = g (τ v w)) → f = g

/-- The concrete binary model has the stated elementary spanning family. -/
def elementary_span : Prop :=
  ∀ {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    Submodule.span K (Set.range (fun vw : V × W => vw.1 ⊗ₜ[K] vw.2)) = ⊤

/-- Equality of linear maps in the concrete model is tested on elementary tensors. -/
def linear_ext : Prop :=
  ∀ {K V W H : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup H] [Module K H]
    (f g : (V ⊗[K] W) →ₗ[K] H),
    (∀ v w, f (v ⊗ₜ[K] w) = g (v ⊗ₜ[K] w)) → f = g

/-- Every finite arity, with heterogeneous input spaces, has the analogous property. -/
def finite_universal : Prop :=
  ∀ {K I : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)],
    IsMultitensorProduct (PiTensorProduct.tprod K (s := V))

/-- The finite-arity representing correspondence is a linear equivalence. -/
def finite_linearization : Prop :=
  ∀ {K I H : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup H] [Module K H],
    ∃ E : MultilinearMap K V H ≃ₗ[K] (PiTensorProduct K V →ₗ[K] H),
      (∀ b v, E b (PiTensorProduct.tprod K v) = b v) ∧
      (∀ f v, E.symm f v = f (PiTensorProduct.tprod K v))

/-- Spanning also follows from universality for any finite-arity model. -/
def finite_span_of_universal : Prop :=
  ∀ {K I U : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup U] [Module K U] (τ : MultilinearMap K V U),
    IsMultitensorProduct τ → Submodule.span K (Set.range τ) = ⊤

/-- Extensionality for any finite-arity model. -/
def finite_ext_of_universal : Prop :=
  ∀ {K I U H : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup U] [Module K U] [AddCommGroup H] [Module K H]
    (τ : MultilinearMap K V U), IsMultitensorProduct τ →
    ∀ f g : U →ₗ[K] H, (∀ v, f (τ v) = g (τ v)) → f = g

/-- The nullary tensor is the field, and its elementary empty tensor is 1.
The inverse formula fixes the normalization, rather than just comparing dimensions. -/
def nullary_equivalence : Prop :=
  ∀ {K I : Type u} {V : I → Type u} [Field K] [Fintype I] [IsEmpty I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)],
    ∃ E : PiTensorProduct K V ≃ₗ[K] K,
      (∀ v : ∀ i, V i, E (PiTensorProduct.tprod K v) = 1) ∧
      (∀ a : K, E.symm a = a • PiTensorProduct.tprod K (0 : ∀ i, V i))

/-- With K itself as nullary product, every nullary map factors uniquely
through the distinguished scalar 1. No false zero-input vanishing is imposed. -/
def nullary_universal : Prop :=
  ∀ {K I H : Type u} {V : I → Type u} [Field K] [IsEmpty I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup H] [Module K H] (b : MultilinearMap K V H),
    ∃! f : K →ₗ[K] H, ∀ v : ∀ i, V i, f 1 = b v

end Specs.D05.M15.TensorUniversal
