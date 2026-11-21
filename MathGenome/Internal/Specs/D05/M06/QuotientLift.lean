import MathGenome.Internal.Specs.D05.M06.QuotientMap
import MathGenome.Internal.Specs.D05.M03.LinearMap

/-!
Independent statements for K05.06.quotient_lift (paper.tex:948–954).

The quotient and its projection are the canonical algebraic constructions from
K05.06.quotient and K05.06.quotient_map. All maps are linear over the same named
field. No finite dimension, complement, or factorization is assumed.
-/

namespace Specs.D05.M06.QuotientLift

/-- Vanishing on `U` makes the proposed value independent of its representative. -/
def representative_independence : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (U : Submodule K V) (T : V →ₗ[K] W),
    U ≤ LinearMap.ker T → ∀ v w : V, v - w ∈ U → T v = T w

/-- Every factorization has the formula `Tbar (v + U) = T v`. -/
def factorization_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (U : Submodule K V) (T : V →ₗ[K] W)
    (Tbar : (V ⧸ U) →ₗ[K] W),
    T = Tbar.comp (Specs.D05.M06.QuotientMap.quotientMap_value K V U) →
      ∀ v : V, Tbar (Submodule.Quotient.mk v) = T v

/-- A unique linear factor through the quotient exists exactly when `T` kills `U`.
The equality is an equality of actual bundled maps with domain `V`. -/
def quotient_lift : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (U : Submodule K V) (T : V →ₗ[K] W),
    (∃! Tbar : (V ⧸ U) →ₗ[K] W,
      T = Tbar.comp (Specs.D05.M06.QuotientMap.quotientMap_value K V U)) ↔
      U ≤ LinearMap.ker T

end Specs.D05.M06.QuotientLift
