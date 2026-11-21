import MathGenome.Internal.Specs.D05.M15.TensorUniversal

/-!
Independent specifications for K05.15.permutation_actions, paper.tex:2889–2895.

The tensor power is the finite tensor model fixed in TensorUniversal, with
constant family `Fin p → V`. The space V may have arbitrary dimension over
any field. In particular no factorial or characteristic assumption is made.
The inverse permutation acts on slot indices, and multiplication of
permutations is function composition in the order σ(τ(i)). Degree zero uses
the upstream nullary equivalence with K, normalized at the elementary unit.
-/

namespace Specs.D05.M15.PermutationActions

universe u v

/-- Canonical operator: reindex the existing tensor power along σ. -/
noncomputable def permutationOperator {K : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V] (p : ℕ)
    (σ : Equiv.Perm (Fin p)) :
    PiTensorProduct K (fun _ : Fin p => V) →ₗ[K]
      PiTensorProduct K (fun _ : Fin p => V) :=
  (PiTensorProduct.reindex K (fun _ : Fin p => V) σ).toLinearMap

def permutationOperator_type :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), Equiv.Perm (Fin p) →
      (PiTensorProduct K (fun _ : Fin p => V) →ₗ[K]
        PiTensorProduct K (fun _ : Fin p => V))

noncomputable def permutationOperator_value : permutationOperator_type.{u, v} :=
  @permutationOperator

/-- Reordering the elementary map remains multilinear in its input vectors. -/
def reordered_multilinear : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (σ : Equiv.Perm (Fin p)),
    ∃ b : MultilinearMap K (fun _ : Fin p => V)
        (PiTensorProduct K (fun _ : Fin p => V)),
      ∀ v : Fin p → V, b v = PiTensorProduct.tprod K (fun j => v (σ⁻¹ j))

/-- This formula fixes the convention on every elementary tensor. -/
def operator_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (σ : Equiv.Perm (Fin p)) (v : Fin p → V),
    permutationOperator (K := K) p σ (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (fun j => v (σ⁻¹ j))

/-- The elementary formula determines the whole linear operator uniquely. -/
def operator_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (σ : Equiv.Perm (Fin p))
    (F : PiTensorProduct K (fun _ : Fin p => V) →ₗ[K]
      PiTensorProduct K (fun _ : Fin p => V)),
    (∀ v : Fin p → V, F (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (fun j => v (σ⁻¹ j))) →
    F = permutationOperator p σ

/-- Pσ ∘ Pτ = P(στ) for composition (στ)(j) = σ(τ(j)). -/
def operator_mul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (σ τ : Equiv.Perm (Fin p)),
    (permutationOperator (K := K) (V := V) p σ).comp
        (permutationOperator p τ) = permutationOperator p (σ * τ)

def operator_one : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (p : ℕ),
    permutationOperator (K := K) (V := V) p 1 = LinearMap.id

/-- Both inverse identities hold on all tensors, in all degrees. -/
def operator_inverse : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (σ : Equiv.Perm (Fin p)),
    (permutationOperator (K := K) (V := V) p σ⁻¹).comp
        (permutationOperator p σ) = LinearMap.id ∧
    (permutationOperator (K := K) (V := V) p σ).comp
        (permutationOperator p σ⁻¹) = LinearMap.id

/-- Under the canonical nullary equivalence, every degree-zero operator is
identity on K. In particular it fixes the distinguished elementary unit 1. -/
def degree_zero_scalar : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (σ : Equiv.Perm (Fin 0)) (t : PiTensorProduct K (fun _ : Fin 0 => V)),
    PiTensorProduct.isEmptyEquiv (R := K) (s := fun _ : Fin 0 => V) (Fin 0)
        (permutationOperator 0 σ t) =
      PiTensorProduct.isEmptyEquiv (R := K) (s := fun _ : Fin 0 => V) (Fin 0) t

end Specs.D05.M15.PermutationActions
