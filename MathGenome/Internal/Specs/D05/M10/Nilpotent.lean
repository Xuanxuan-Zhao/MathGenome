import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M10.KernelStabilization
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-!
Independent statements for K05.10.nilpotent, paper.tex:1427–1428.
All scalars lie in the original field. Endomorphism powers use composition.
The index is the infimum of the positive vanishing exponents, rather than
Mathlib's `nilpotencyClass`, which is zero on the zero endomorphism algebra.
For a nonnilpotent map this definition has the unused value zero.
-/

noncomputable section

namespace Specs.D05.M10.Nilpotent

universe u v

def nilpotent_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Module.End K V → Prop

def nilpotent_value : nilpotent_type.{u, v} :=
  fun _ _ _ _ _ N => IsNilpotent N

/-- The standard nilpotence predicate agrees with the source's positive-exponent definition. -/
def nilpotent_iff_positive_power : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (N : Module.End K V),
    IsNilpotent N ↔ ∃ r : ℕ, 0 < r ∧ N ^ r = 0

def nilpotencyIndex_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Module.End K V → ℕ

/-- The least positive vanishing exponent, when such an exponent exists. -/
def nilpotencyIndex_value : nilpotencyIndex_type.{u, v} :=
  fun _ _ _ _ _ N => sInf {r : ℕ | 0 < r ∧ N ^ r = 0}

/-- Positivity, vanishing, and minimality characterize the index. -/
def index_spec : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Module.End K V), IsNilpotent N →
      0 < nilpotencyIndex_value K V N ∧ N ^ (nilpotencyIndex_value K V N) = 0 ∧
      ∀ r : ℕ, 0 < r → N ^ r = 0 → nilpotencyIndex_value K V N ≤ r

/-- The stabilized kernel fills the space, including when its dimension is zero. -/
def kernel_pow_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (n : ℕ),
    Module.finrank K V = n → IsNilpotent N → LinearMap.ker (N ^ n) = ⊤

def pow_dimension_eq_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (n : ℕ),
    Module.finrank K V = n → IsNilpotent N → N ^ n = 0

/-- Only the index bound needs the positive-dimension hypothesis. -/
def index_le_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (n : ℕ),
    Module.finrank K V = n → 0 < n → IsNilpotent N →
      nilpotencyIndex_value K V N ≤ n

/-- Every power on the zero space vanishes, but the positive index is one. -/
def zero_dimensional : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V), Module.finrank K V = 0 →
      (∀ r : ℕ, N ^ r = 0) ∧ nilpotencyIndex_value K V N = 1

/-- The scalar in any nonzero eigenvector equation is zero; finite dimension is unnecessary. -/
def eigenvector_scalar_eq_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Module.End K V) (μ : K) (x : V),
    IsNilpotent N → x ≠ 0 → N x = μ • x → μ = 0

/-- On a nonzero finite-dimensional space, zero occurs and is the only eigenvalue. -/
def eigenvalues : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (N : Module.End K V),
    IsNilpotent N → ∀ μ : K, N.HasEigenvalue μ ↔ μ = 0

end Specs.D05.M10.Nilpotent
