import Mathlib.LinearAlgebra.Quotient.Basic
import MathGenome.Internal.Specs.D05.M06.QuotientLift

/-!
Independent statements for K05.06.invariant (paper.tex:992–993).

All maps use the original scalar field. The restriction acts on the subspace
subtype, whereas the induced map acts on the algebraic quotient. No finite
dimension, complement, or vanishing of `T` on `U` is assumed. The constructors
below require only the pointwise preservation condition defining invariance.
-/

namespace Specs.D05.M06.Invariant

universe u v

/-- Type of the invariance predicate. -/
def invariant_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → Submodule K V → (V →ₗ[K] V) → Prop

/-- `T(U) ⊆ U`, with no dimension condition. -/
def invariant_value : invariant_type.{u, v} :=
  fun _ _ _ _ _ U T => ∀ x ∈ U, T x ∈ U

/-- Type of the restriction to an invariant subspace. -/
def restriction_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → (U : Submodule K V) → (T : V →ₗ[K] V) →
      invariant_value K V U T → (U →ₗ[K] U)

/-- Restrict both the domain and the codomain, keeping the same formula. -/
def restriction_value : restriction_type.{u, v} :=
  fun _ _ _ _ _ _ T h => T.restrict h

/-- Type of the induced endomorphism of the algebraic quotient. -/
def inducedMap_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → (U : Submodule K V) → (T : V →ₗ[K] V) →
      invariant_value K V U T → ((V ⧸ U) →ₗ[K] (V ⧸ U))

/-- The quotient construction descends `q ∘ T`, not `T : V → V`. -/
def inducedMap_value : inducedMap_type.{u, v} :=
  fun _ _ _ _ _ U T h => U.mapQ U T h

/-- Pointwise preservation is exactly containment of the set-theoretic image. -/
def invariant_iff_image_subset : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V),
    invariant_value K V U T ↔ T '' (U : Set V) ⊆ (U : Set V)

/-- The same condition expressed using the canonical subspace image. -/
def invariant_iff_map_le : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V),
    invariant_value K V U T ↔ U.map T ≤ U

/-- The restricted map has the same values in the ambient space. -/
def restriction_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T) (x : U),
    (restriction_value K V U T h x : V) = T (x : V)

/-- Linearity of the restriction uses the inherited operations on `U`. -/
def restriction_operations : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T),
    (∀ x y : U, restriction_value K V U T h (x + y) =
      restriction_value K V U T h x + restriction_value K V U T h y) ∧
    (∀ (a : K) (x : U), restriction_value K V U T h (a • x) =
      a • restriction_value K V U T h x)

/-- The inclusion intertwines the restricted operator with `T`. -/
def restriction_commutes : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T),
    U.subtype.comp (restriction_value K V U T h) = T.comp U.subtype

/-- The inclusion identity determines the restricted operator uniquely. -/
def restriction_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T)
    (R : U →ₗ[K] U),
    U.subtype.comp R = T.comp U.subtype → R = restriction_value K V U T h

/-- Invariance preserves the representative relation used to form `V/U`. -/
def representative_independence : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T)
    (x y : V), x - y ∈ U → T x - T y ∈ U

/-- The induced map sends the class of `x` to the class of `T x`. -/
def inducedMap_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T) (x : V),
    inducedMap_value K V U T h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (T x) : V ⧸ U)

/-- Linearity of the induced map uses the canonical quotient operations. -/
def inducedMap_operations : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T),
    (∀ x y : V ⧸ U, inducedMap_value K V U T h (x + y) =
      inducedMap_value K V U T h x + inducedMap_value K V U T h y) ∧
    (∀ (a : K) (x : V ⧸ U), inducedMap_value K V U T h (a • x) =
      a • inducedMap_value K V U T h x)

/-- The quotient projection intertwines `T` with the induced operator. -/
def inducedMap_commutes : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T),
    (inducedMap_value K V U T h).comp
        (Specs.D05.M06.QuotientMap.quotientMap_value K V U) =
      (Specs.D05.M06.QuotientMap.quotientMap_value K V U).comp T

/-- The projection identity determines the induced quotient operator uniquely. -/
def inducedMap_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant_value K V U T)
    (S : (V ⧸ U) →ₗ[K] (V ⧸ U)),
    S.comp (Specs.D05.M06.QuotientMap.quotientMap_value K V U) =
        (Specs.D05.M06.QuotientMap.quotientMap_value K V U).comp T →
      S = inducedMap_value K V U T h

end Specs.D05.M06.Invariant
