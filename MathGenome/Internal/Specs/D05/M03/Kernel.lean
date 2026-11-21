import Mathlib.Algebra.Module.Submodule.Ker
import MathGenome.Internal.Specs.D05.M02.Subspace
import MathGenome.Internal.Specs.D05.M03.LinearMap

/-!
Independent statements for K05.03.kernel (paper.tex:547–548).

The kernel is Mathlib's canonical submodule of the domain, over the common
scalar field. Its carrier is exactly the zero fiber of the given linear map.
The zero and two-term combination assertions record the paper's argument.
All vector spaces are arbitrary; no finite-dimensional assumption is imposed.
-/

namespace Specs.D05.M03.Kernel

universe u v w

/-- Type of the kernel construction, with values in subspaces of the domain. -/
def kernel_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  (K : Type u) → (V : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
      (V →ₗ[K] W) → Submodule K V

/-- The construction uses the existing kernel, with its actual scalar action. -/
def kernel_value : kernel_type.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ T => LinearMap.ker T

/-- The carrier of the kernel is precisely the set defined in the paper. -/
def kernel_eq_set : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    (LinearMap.ker T : Set V) = {v : V | T v = 0}

/-- The zero vector of the domain belongs to the kernel. -/
def zero_mem_kernel : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    (0 : V) ∈ LinearMap.ker T

/-- The calculation for a linear combination of two vectors in the kernel. -/
def map_linear_combination : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W)
    (a b : K) (u v : V),
    u ∈ LinearMap.ker T → v ∈ LinearMap.ker T →
      T (a • u + b • v) = a • T u + b • T v ∧ a • T u + b • T v = 0

/-- The defining zero fiber is closed under the two-term linear combinations. -/
def linear_combination_mem_kernel : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W)
    (a b : K) (u v : V),
    u ∈ LinearMap.ker T → v ∈ LinearMap.ker T →
      a • u + b • v ∈ LinearMap.ker T

/-- Starting with the specified subset of V, it is the carrier of a subspace. -/
def kernel_is_subspace : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    ∃ S : Submodule K V, (S : Set V) = {v : V | T v = 0}

end Specs.D05.M03.Kernel
