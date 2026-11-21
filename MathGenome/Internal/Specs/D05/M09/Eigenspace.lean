import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M03.MapAlgebra
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
Independent specifications for K05.09.eigenspace (paper.tex:1258–1262).

The objects are Mathlib's eigenspaces, eigenvectors and eigenvalues over the
named field. The kernel bridge uses the canonical identity endomorphism and
pointwise scalar action from the upstream map algebra. A zero space is expressed
by `Subsingleton V`, and a nonzero space by `Nontrivial V`.
These elementary statements hold for every vector space; consequently they also
cover the paper's finite-dimensional setting, including dimension zero.
-/

namespace Specs.D05.M09.Eigenspace

universe u v

/-- Eigenspaces are subspaces over the original scalar field. -/
def eigenspace_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Module.End K V → K → Submodule K V

def eigenspace_value : eigenspace_type.{u, v} :=
  fun _ _ _ _ _ T μ => Module.End.eigenspace T μ

/-- The eigenvector predicate keeps the scalar, operator and vector explicit. -/
def hasEigenvector_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Module.End K V → K → V → Prop

def hasEigenvector_value : hasEigenvector_type.{u, v} :=
  fun _ _ _ _ _ T μ x => Module.End.HasEigenvector T μ x

/-- Eigenvalues belong to the named field, without any scalar extension. -/
def hasEigenvalue_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Module.End K V → K → Prop

def hasEigenvalue_value : hasEigenvalue_type.{u, v} :=
  fun _ _ _ _ _ T μ => Module.End.HasEigenvalue T μ

/-- The defining kernel formula, with the actual identity endomorphism. -/
def eigenspace_eq_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K),
    T.eigenspace μ = LinearMap.ker (T - μ • (LinearMap.id : Module.End K V))

/-- A vector in the eigenspace satisfies precisely the eigenvector equation. -/
def mem_eigenspace_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K) (x : V),
    x ∈ T.eigenspace μ ↔ T x = μ • x

/-- The zero fiber in the definition really is the carrier of a subspace. -/
def eigenspace_is_subspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K),
    ∃ S : Submodule K V, (S : Set V) =
      {x : V | (T - μ • (LinearMap.id : Module.End K V)) x = 0}

/-- Eigenvectors are the nonzero members of the specified kernel. -/
def hasEigenvector_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K) (x : V),
    T.HasEigenvector μ x ↔
      x ∈ LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ∧ x ≠ 0

/-- Eigenvalue means that the specified kernel contains a nonzero vector. -/
def hasEigenvalue_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K),
    T.HasEigenvalue μ ↔
      ∃ x : V, x ∈ LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ∧ x ≠ 0

/-- On the zero space no scalar is an eigenvalue of any endomorphism. -/
def no_eigenvalues_on_zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton V]
    (T : Module.End K V) (μ : K), ¬ T.HasEigenvalue μ

/-- On a nonzero space the identity has exactly the eigenvalue one. -/
def identity_hasEigenvalue_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Nontrivial V]
    (μ : K), Module.End.HasEigenvalue (LinearMap.id : Module.End K V) μ ↔ μ = 1

end Specs.D05.M09.Eigenspace
