import MathGenome.Internal.Specs.D05.M03.MapAlgebra
import Mathlib.LinearAlgebra.Dual.Defs

/-!
Independent specifications for K05.07.dual (paper.tex:1012–1013).

The dual is exactly `Hom_K(V, K)` with its canonical pointwise operations.
The parameters contain only a field and an arbitrary vector space: no topology,
continuity, inner product, or finite-dimensional assumption is involved.
Scalar multiplication of functional values is ordinary field multiplication,
with no conjugation, including when the scalar field is complex.
-/

namespace Specs.D05.M07.Dual

universe u v

/-- Type of the algebraic-dual type constructor for arbitrary vector spaces. -/
def algebraicDual_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Type (max u v)

/-- All algebraic linear functionals, using the existing canonical linear maps. -/
def algebraicDual_value : algebraicDual_type.{u, v} :=
  fun K V _ _ _ => V →ₗ[K] K

/-- Type of the canonical vector-space structure on the dual. -/
def dualModule_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Module K (Module.Dual K V)

/-- The pointwise module structure already available on the Hom space. -/
def dualModule_value : dualModule_type.{u, v} :=
  fun K V _ _ _ => (inferInstance : Module K (Module.Dual K V))

/-- Exactly the additive and homogeneous functions are members of the dual. -/
def functional_iff_axioms : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (t : V → K),
    (∃ f : Module.Dual K V, (f : V → K) = t) ↔
      (∀ u v : V, t (u + v) = t u + t v) ∧
      (∀ (a : K) (v : V), t (a • v) = a * t v)

/-- Addition of functionals is pointwise addition in the field. -/
def add_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : Module.Dual K V) (v : V), (f + g) v = f v + g v

/-- Scalar multiplication is pointwise field multiplication. -/
def smul_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : K) (f : Module.Dual K V) (v : V), (a • f) v = a * f v

/-- The zero of the dual is the zero-valued functional. -/
def zero_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : V), (0 : Module.Dual K V) v = 0

/-- Additive inverses are also pointwise. -/
def neg_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.Dual K V) (v : V), (-f) v = -(f v)

/-- Every member is additive as a function on the original space. -/
def map_add : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.Dual K V) (u v : V), f (u + v) = f u + f v

/-- Every member is homogeneous over precisely the stated field. -/
def map_smul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.Dual K V) (a : K) (v : V), f (a • v) = a * f v

end Specs.D05.M07.Dual
