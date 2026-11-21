import MathGenome.Internal.Specs.D05.M06.QuotientLift
import MathGenome.Internal.Specs.D05.M07.Annihilator
import MathGenome.Internal.Specs.D05.M07.DualMap
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Independent specifications for K05.07.quotient_dual (paper.tex:1089–1095).

The source and target are the algebraic dual of the actual quotient and the
annihilator in the actual algebraic dual of V. All vector spaces are arbitrary;
there is no finite dimension, topology, inner product, or chosen complement.
The representative formulas specify both directions of the canonical map.
-/

namespace Specs.D05.M07.QuotientDual

universe u v

/-- Type of the quotient-dual isomorphism for every subspace. -/
def quotientDualEquiv_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    (U : Submodule K V) → (Module.Dual K (V ⧸ U) ≃ₗ[K] U.dualAnnihilator)

/-- The canonical equivalence: precomposition by the quotient projection,
with inverse given by descent of a vanishing functional. -/
def quotientDualEquiv_value : quotientDualEquiv_type.{u, v} :=
  fun _ _ _ _ _ U => U.dualQuotEquivDualAnnihilator

/-- As a functional on V, the image is exactly pullback by q. -/
def pullback_eq_dualMap : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (h : Module.Dual K (V ⧸ U)),
    (quotientDualEquiv_value K V U h).val =
      Specs.D05.M07.DualMap.dualMap_value
        (Specs.D05.M06.QuotientMap.quotientMap_value K V U) h

/-- The forward map has the paper's evaluation formula. -/
def quotientDualEquiv_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (h : Module.Dual K (V ⧸ U)) (v : V),
    (quotientDualEquiv_value K V U h).val v = h (Submodule.Quotient.mk v)

/-- The inverse is descent, evaluated on any representative of a coset. -/
def quotientDualEquiv_symm_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (f : U.dualAnnihilator) (v : V),
    (quotientDualEquiv_value K V U).symm f (Submodule.Quotient.mk v) = f.val v

/-- Pullback lands in the annihilator: every vector of U is killed. -/
def pullback_vanishes : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (h : Module.Dual K (V ⧸ U)) (u : V), u ∈ U →
    h (Specs.D05.M06.QuotientMap.quotientMap_value K V U u) = 0

/-- Full conclusion, including canonicity: there is exactly one linear
isomorphism whose underlying functionals are composition with the projection. -/
def quotient_dual : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    ∃! e : Module.Dual K (V ⧸ U) ≃ₗ[K] U.dualAnnihilator,
      ∀ h : Module.Dual K (V ⧸ U),
        (e h).val = h.comp (Specs.D05.M06.QuotientMap.quotientMap_value K V U)

end Specs.D05.M07.QuotientDual
