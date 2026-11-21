import MathGenome.Internal.Specs.D05.M15.TensorBasis
import MathGenome.Internal.Specs.D05.M07.Biddual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
Independent statements for K05.15.tensor_pairing, paper.tex:2839–2846.
Duals and tensors are algebraic over an arbitrary field. The evaluation maps
are defined without dimensional restrictions, and all equivalence assertions
require finite-dimensional factors. Empty index types and zero spaces are
allowed. The later arbitrary-dimensional injectivity result is a separate goal.
-/
namespace Specs.D05.M15.TensorPairing

universe u v w
open scoped TensorProduct

/-- The canonical map, also available to the later injectivity theorem. -/
def evaluation_type :=
  (K : Type u) → (V : Type v) → (W : Type w) →
    [Field K] → [AddCommGroup V] → [Module K V] →
    [AddCommGroup W] → [Module K W] →
    (Module.Dual K V ⊗[K] Module.Dual K W) →ₗ[K] Module.Dual K (V ⊗[K] W)

def evaluation_value : evaluation_type.{u, v, w} :=
  fun K V W _ _ _ _ _ => TensorProduct.dualDistrib K V W

def evaluation_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (φ : Module.Dual K V) (ψ : Module.Dual K W)
    (v : V) (w : W),
    TensorProduct.dualDistrib K V W (φ ⊗ₜ[K] ψ) (v ⊗ₜ[K] w) = φ v * ψ w

/-- The elementary formula uniquely characterizes the map in all dimensions. -/
def evaluation_unique : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (F : (Module.Dual K V ⊗[K] Module.Dual K W) →ₗ[K]
      Module.Dual K (V ⊗[K] W)),
    (∀ φ ψ v w, F (φ ⊗ₜ[K] ψ) (v ⊗ₜ[K] w) = φ v * ψ w) →
    F = TensorProduct.dualDistrib K V W

/-- Products of coordinates are exactly coordinates on the tensor basis,
also for infinite bases. Finite bases make these families full dual bases. -/
def coordinate_functionals : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : Module.Basis I K V) (f : Module.Basis J K W)
    (i : I) (j : J),
    TensorProduct.dualDistrib K V W (e.coord i ⊗ₜ[K] f.coord j) =
      (e.tensorProduct f).coord (i, j)

def perfect_pairing : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W],
    ∃ E : (Module.Dual K V ⊗[K] Module.Dual K W) ≃ₗ[K] Module.Dual K (V ⊗[K] W),
      E.toLinearMap = TensorProduct.dualDistrib K V W

/-- Bilinear forms are identified with dual tensors by their values, not just
by a dimension equality. The inverse represents every bilinear form uniquely. -/
def bilinear_forms : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W],
    ∃ E : (Module.Dual K V ⊗[K] Module.Dual K W) ≃ₗ[K] (V →ₗ[K] W →ₗ[K] K),
      ∀ z v w, E z v w = TensorProduct.dualDistrib K V W z (v ⊗ₜ[K] w)

def unique_bilinear_representation : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (b : V →ₗ[K] W →ₗ[K] K),
    ∃! z : Module.Dual K V ⊗[K] Module.Dual K W,
      ∀ v w, TensorProduct.dualDistrib K V W z (v ⊗ₜ[K] w) = b v w

/-- Finite biduality gives the corresponding primal-tensor representation. -/
def primal_bilinear_forms : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W],
    ∃ E : (V ⊗[K] W) ≃ₗ[K] (Module.Dual K V →ₗ[K] Module.Dual K W →ₗ[K] K),
      ∀ v w φ ψ, E (v ⊗ₜ[K] w) φ ψ = φ v * ψ w

/-- The analogous canonical evaluation for any finite family. -/
def finite_evaluation_type :=
  (K : Type u) → (I : Type v) → (V : I → Type w) →
    [Field K] → [Fintype I] → [∀ i, AddCommGroup (V i)] → [∀ i, Module K (V i)] →
    PiTensorProduct K (fun i => Module.Dual K (V i)) →ₗ[K]
      Module.Dual K (PiTensorProduct K V)

noncomputable def finite_evaluation_value : finite_evaluation_type.{u, v, w} :=
  fun _ _ _ _ _ _ _ => PiTensorProduct.dualDistrib

def finite_evaluation_apply : Prop :=
  ∀ {K I : Type*} {V : I → Type*} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (φ : ∀ i, Module.Dual K (V i)) (v : ∀ i, V i),
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod K φ)
      (PiTensorProduct.tprod K v) = ∏ i, φ i (v i)

def finite_coordinate_functionals : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {J : I → Type*} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (e : ∀ i, Module.Basis (J i) K (V i)) (p : ∀ i, J i),
    PiTensorProduct.dualDistrib
      (PiTensorProduct.tprod K (fun i => (e i).coord (p i))) =
      (_root_.Basis.piTensorProduct e).coord p

def finite_perfect_pairing : Prop :=
  ∀ {K I : Type*} {V : I → Type*} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)],
    ∃ E : PiTensorProduct K (fun i => Module.Dual K (V i)) ≃ₗ[K]
      Module.Dual K (PiTensorProduct K V),
      E.toLinearMap = PiTensorProduct.dualDistrib

def finite_multilinear_forms : Prop :=
  ∀ {K I : Type*} {V : I → Type*} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)],
    ∃ E : PiTensorProduct K (fun i => Module.Dual K (V i)) ≃ₗ[K]
      MultilinearMap K V K,
      ∀ φ v, E (PiTensorProduct.tprod K φ) v = ∏ i, φ i (v i)

/-- In degree zero both tensor spaces are K with empty tensor equal to 1;
the evaluation is ordinary scalar multiplication. No factor finiteness is needed. -/
def nullary_pairing : Prop :=
  ∀ {K I : Type*} {V : I → Type*} [Field K] [Fintype I] [IsEmpty I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (a b : K),
    PiTensorProduct.dualDistrib
      (a • PiTensorProduct.tprod K (0 : ∀ i, Module.Dual K (V i)))
      (b • PiTensorProduct.tprod K (0 : ∀ i, V i)) = a * b

end Specs.D05.M15.TensorPairing
