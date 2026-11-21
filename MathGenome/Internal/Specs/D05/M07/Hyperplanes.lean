import MathGenome.Internal.Specs.D05.M06.Quotient
import MathGenome.Internal.Specs.D05.M07.Dual
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Order.Atoms

/-!
Independent statements for K05.07.hyperplanes (paper.tex:1097–1107).
All vector spaces are arbitrary algebraic vector spaces over the named field.
`Module.rank K (V ⧸ U) = 1` expresses dimension one without assuming that
`V` is finite dimensional. The zero-space boundary is included explicitly.
-/

namespace Specs.D05.M07.Hyperplanes

universe u v

def hyperplane_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → Submodule K V → Prop

/-- A hyperplane is a maximal proper subspace. -/
def hyperplane_value : hyperplane_type.{u, v} :=
  fun _ _ _ _ _ U => IsCoatom U

/-- Spell out the order-theoretic maximal-proper condition. -/
def hyperplane_iff_maximal_proper : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    IsCoatom U ↔ U ≠ ⊤ ∧ ∀ W : Submodule K V, U < W → W = ⊤

def maximal_proper_iff_quotient_dimension_one : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    IsCoatom U ↔ Module.rank K (V ⧸ U) = 1

def quotient_dimension_one_iff_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    Module.rank K (V ⧸ U) = 1 ↔
      ∃ f : Module.Dual K V, f ≠ 0 ∧ U = LinearMap.ker f

def maximal_proper_iff_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    IsCoatom U ↔ ∃ f : Module.Dual K V, f ≠ 0 ∧ U = LinearMap.ker f

/-- Every nonzero functional can be normalized at a vector of its domain. -/
def exists_value_one : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.Dual K V), f ≠ 0 → ∃ v : V, f v = 1

/-- The actual direct decomposition from the source, with unique components. -/
def kernel_unique_decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.Dual K V) (v : V), f v = 1 →
      ∀ x : V, ∃! p : (LinearMap.ker f) × K, x = (p.1 : V) + p.2 • v

def same_kernel_iff_nonzero_smul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : Module.Dual K V), f ≠ 0 → g ≠ 0 →
      (LinearMap.ker f = LinearMap.ker g ↔ ∃ c : K, c ≠ 0 ∧ g = c • f)

/-- Neither kind of object exists on a zero-dimensional vector space. -/
def zero_space_boundary : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton V],
    (∀ U : Submodule K V, ¬ IsCoatom U) ∧
      ∀ f : Module.Dual K V, f = 0

end Specs.D05.M07.Hyperplanes
