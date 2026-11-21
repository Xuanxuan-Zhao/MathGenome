import MathGenome.Internal.Specs.D05.M11.Nondegenerate
import MathGenome.Internal.Specs.D05.M15.TensorPairing
import MathGenome.Internal.Specs.D05.M15.TensorDualHom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Algebraic bilinear metric tensors, paper.tex:2872–2879.
All bases are finite ordered bases, including the empty basis. No positivity,
characteristic restriction, or Hermitian structure is assumed. A Hermitian
Riesz map is semilinear and is not the bilinear map used here. -/
namespace Specs.D05.M15.InnerTensor.MetricTensors

open Module Matrix
open scoped TensorProduct
open Specs.D05.M11.FormMatrix

universe u v

noncomputable def covariant {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) :
    Dual K V ⊗[K] Dual K V :=
  ∑ i, ∑ j, formMatrix_value e B i j • (e.coord i ⊗ₜ[K] e.coord j)

noncomputable def contravariant {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) : V ⊗[K] V :=
  ∑ i, ∑ j, (formMatrix_value e B)⁻¹ i j • (e i ⊗ₜ[K] e j)

/-- Evaluate the first vector slot against an algebraic covector. -/
def firstContraction (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    (V ⊗[K] V) →ₗ[K] (Dual K V →ₗ[K] V) :=
  (dualTensorHom K (Dual K V) V).comp
    (TensorProduct.map (Dual.eval K V) (LinearMap.id : V →ₗ[K] V))

/-- Contract the first covector slot with the first vector slot. The two
remaining factors, in order, are a covector and a vector. -/
def metricContraction (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (q : Dual K V ⊗[K] Dual K V) (t : V ⊗[K] V) : Dual K V ⊗[K] V :=
  TensorProduct.map (dualTensorHom K V (Dual K V) q) (LinearMap.id : V →ₗ[K] V) t

def covariant_type :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    {n : ℕ} → Basis (Fin n) K V → LinearMap.BilinForm K V → Dual K V ⊗[K] Dual K V
noncomputable def covariant_value : covariant_type.{u,v} := @covariant

def contravariant_type :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    {n : ℕ} → Basis (Fin n) K V → LinearMap.BilinForm K V → V ⊗[K] V
noncomputable def contravariant_value : contravariant_type.{u,v} := @contravariant

def firstContraction_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    (V ⊗[K] V) →ₗ[K] (Dual K V →ₗ[K] V)
def firstContraction_value : firstContraction_type.{u,v} := firstContraction

def metricContraction_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    (Dual K V ⊗[K] Dual K V) → (V ⊗[K] V) → Dual K V ⊗[K] V
def metricContraction_value : metricContraction_type.{u,v} := metricContraction

def metric_contraction_tmul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (α β : Dual K V) (v w : V),
    metricContraction K V (α ⊗ₜ[K] β) (v ⊗ₜ[K] w) = α v • (β ⊗ₜ[K] w)

def covariant_to_flat : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    dualTensorHom K V (Dual K V) (covariant e B) = B

def contraction_tmul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v w : V) (φ : Dual K V), firstContraction K V (v ⊗ₜ[K] w) φ = φ v • w

/-- The covariant formula represents the original form on the original vectors. -/
def covariant_evaluation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (v w : V),
    TensorProduct.dualDistrib K V V (covariant e B) (v ⊗ₜ[K] w) = B v w

def covariant_basis_independent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n m : ℕ}
    (e : Basis (Fin n) K V) (f : Basis (Fin m) K V) (B : LinearMap.BilinForm K V),
    covariant e B = covariant f B

def flat_isomorphism : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V), B.Nondegenerate →
    ∃ E : V ≃ₗ[K] Dual K V, E.toLinearMap = B

def flat_matrix : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V), B.IsSymm →
    LinearMap.toMatrix e e.dualBasis B = (formMatrix_value e B)ᵀ ∧
    (formMatrix_value e B)ᵀ = formMatrix_value e B

/-- These are genuine tensor-basis coordinates, rather than just named arrays. -/
def covariant_coefficients : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (i j : Fin n),
    (e.dualBasis.tensorProduct e.dualBasis).repr (covariant e B) (i,j) =
      formMatrix_value e B i j

def contravariant_coefficients : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (i j : Fin n),
    (e.tensorProduct e).repr (contravariant e B) (i,j) = (formMatrix_value e B)⁻¹ i j

/-- Symmetry is needed: first-slot contraction has the transpose coefficient matrix. -/
def contravariant_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V), B.IsSymm →
    ∀ (φ : Dual K V) (i : Fin n),
      e.repr (firstContraction K V (contravariant e B) φ) i =
        ∑ j, (formMatrix_value e B)⁻¹ i j * φ (e j)

/-- The tensor represents the inverse to b-flat in both directions. -/
def contravariant_inverse : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V), B.IsSymm →
    B.Nondegenerate →
    LinearMap.comp B (firstContraction K V (contravariant e B)) = LinearMap.id ∧
    (firstContraction K V (contravariant e B)).comp B = LinearMap.id

def contraction_equivalence : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    ∃ E : (V ⊗[K] V) ≃ₗ[K] (Dual K V →ₗ[K] V),
      E.toLinearMap = firstContraction K V

def contravariant_basis_independent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n m : ℕ}
    (e : Basis (Fin n) K V) (f : Basis (Fin m) K V) (B : LinearMap.BilinForm K V),
    B.IsSymm → B.Nondegenerate → contravariant e B = contravariant f B

/-- Contract a covariant slot (b-flat) with the first vector slot of the inverse
metric. Under tensor–Hom the resulting mixed tensor is the identity map. -/
def mixed_contraction_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V), B.IsSymm →
    B.Nondegenerate →
    TensorProduct.map B (LinearMap.id : V →ₗ[K] V) (contravariant e B) =
      ∑ i, e.coord i ⊗ₜ[K] e i

/-- Actual contraction between the displayed covariant and contravariant
tensors gives the identity tensor. -/
def metric_contraction_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V), B.IsSymm →
    B.Nondegenerate →
    metricContraction K V (covariant e B) (contravariant e B) =
      ∑ i, e.coord i ⊗ₜ[K] e i

def contraction_coefficients : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V), B.Nondegenerate →
    ∀ i k, (∑ j, formMatrix_value e B i j * (formMatrix_value e B)⁻¹ j k) =
      if i = k then 1 else 0

/-- The Euclidean orthonormal specialization is the case G=1. The statement
is algebraic, so in particular applies to a real Euclidean form. -/
def orthonormal_sums : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V), formMatrix_value e B = 1 →
    covariant e B = (∑ i, e.coord i ⊗ₜ[K] e.coord i) ∧
    contravariant e B = (∑ i, e i ⊗ₜ[K] e i)

/-- Identity coefficients are precisely the bilinear orthonormal condition. -/
def identity_coefficients_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    (formMatrix_value e B = 1 ↔ ∀ i j, B (e i) (e j) = if i = j then 1 else 0) ∧
    ((formMatrix_value e B)⁻¹ = 1 ↔ formMatrix_value e B = 1)

end Specs.D05.M15.InnerTensor.MetricTensors
