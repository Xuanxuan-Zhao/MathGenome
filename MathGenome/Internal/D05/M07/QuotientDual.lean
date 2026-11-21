import MathGenome.Internal.D05.M06.QuotientLift
import MathGenome.Internal.D05.M07.Annihilator
import MathGenome.Internal.D05.M07.DualMap
import MathGenome.Internal.Specs.D05.M07.QuotientDual

/-! K05.07.quotient_dual: canonical duality for an arbitrary algebraic quotient.

Mathlib's equivalence corestricts `U.mkQ.dualMap` to the annihilator. Its inverse
is `U.dualCopairing`, defined by `U.liftQ`. Its two inverse laws are proved by
evaluation on representatives. Thus it uses neither bases nor dimensions.
-/

namespace D05.M07.QuotientDual

/-- Pullback by the quotient projection, as a linear equivalence onto U⁰. -/
abbrev quotientDualEquiv (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) :
    D05.M07.Dual.algebraicDual K (V ⧸ U) ≃ₗ[K] D05.M07.Annihilator.annihilator K V U :=
  U.dualQuotEquivDualAnnihilator

theorem pullback_eq_dualMap : Specs.D05.M07.QuotientDual.pullback_eq_dualMap := by
  intro K V _ _ _ U h
  rfl

theorem quotientDualEquiv_apply : Specs.D05.M07.QuotientDual.quotientDualEquiv_apply := by
  intro K V _ _ _ U h v
  exact Submodule.dualQuotEquivDualAnnihilator_apply U h v

theorem quotientDualEquiv_symm_apply :
    Specs.D05.M07.QuotientDual.quotientDualEquiv_symm_apply := by
  intro K V _ _ _ U f v
  exact Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk U f v

theorem pullback_vanishes : Specs.D05.M07.QuotientDual.pullback_vanishes := by
  intro K V _ _ _ U h u hu
  rw [(D05.M06.QuotientMap.eq_zero_iff U u).mpr hu, h.map_zero]

theorem quotient_dual : Specs.D05.M07.QuotientDual.quotient_dual := by
  intro K V _ _ _ U
  refine ⟨quotientDualEquiv K V U, ?_, ?_⟩
  · intro h
    rfl
  · intro e he
    apply LinearEquiv.ext
    intro h
    apply Subtype.ext
    exact he h

end D05.M07.QuotientDual
