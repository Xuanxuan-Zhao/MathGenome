import MathGenome.Internal.Specs.D05.M06.Quotient
import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M03.Image

/-!
Independent statements for K05.06.quotient_map (paper.tex:945–946).

The map takes values in the canonical algebraic quotient already specified in
K05.06.quotient. It sends a vector to its equivalence class, with the same
quotient operations. The assertions apply to every subspace of every vector
space over the named field; no finite dimension or complement is assumed.
The zero in the quotient denotes the class of zero, whose coset is `U`.
-/

namespace Specs.D05.M06.QuotientMap

universe u v

/-- Type of the quotient projection as an actual linear map. -/
def quotientMap_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → (U : Submodule K V) → (V →ₗ[K] V ⧸ U)

/-- The specified value is the projection to equivalence classes. -/
def quotientMap_value : quotientMap_type.{u, v} :=
  fun _ _ _ _ _ U => U.mkQ

/-- The projection has exactly the representative formula in the paper. -/
def quotientMap_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (x : V),
    quotientMap_value K V U x = (Submodule.Quotient.mk x : V ⧸ U)

/-- As a subset of the original space, the class of `x` is the coset `x + U`. -/
def fiber_eq_coset : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (x : V),
    {y : V | quotientMap_value K V U y = quotientMap_value K V U x} =
      {y : V | ∃ u : V, u ∈ U ∧ y = x + u}

/-- Additivity is with respect to the canonical quotient addition. -/
def map_add : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (x y : V),
    quotientMap_value K V U (x + y) =
      quotientMap_value K V U x + quotientMap_value K V U y

/-- Homogeneity uses the original field and canonical quotient scalar action. -/
def map_smul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (a : K) (x : V),
    quotientMap_value K V U (a • x) = a • quotientMap_value K V U x

/-- Every quotient vector is the image of a vector of `V`. -/
def surjective : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V), Function.Surjective (quotientMap_value K V U)

/-- The image is the whole quotient, not a selected complement in `V`. -/
def range_eq_top : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V), LinearMap.range (quotientMap_value K V U) = ⊤

/-- The class of `x` is the zero class exactly when `x` belongs to `U`. -/
def eq_zero_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (x : V), quotientMap_value K V U x = 0 ↔ x ∈ U

/-- The kernel is exactly the given subspace of the domain. -/
def kernel_eq : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V), LinearMap.ker (quotientMap_value K V U) = U

end Specs.D05.M06.QuotientMap
