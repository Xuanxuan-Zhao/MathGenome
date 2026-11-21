import MathGenome.Internal.D05.M06.Quotient
import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M03.Image
import MathGenome.Internal.Specs.D05.M06.QuotientMap

/-! K05.06.quotient_map: the canonical surjective linear projection with kernel `U`. -/

namespace D05.M06.QuotientMap

/-- Send a vector to its coset in the algebraic quotient by `U`. -/
abbrev quotientMap (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) : V →ₗ[K] D05.M06.Quotient.quotientSpace K V U :=
  U.mkQ

theorem quotientMap_apply : Specs.D05.M06.QuotientMap.quotientMap_apply := by
  intro K V _ _ _ U x
  rfl

theorem fiber_eq_coset : Specs.D05.M06.QuotientMap.fiber_eq_coset := by
  intro K V _ _ _ U x
  exact D05.M06.Quotient.class_eq_coset U x

theorem map_add : Specs.D05.M06.QuotientMap.map_add := by
  intro K V _ _ _ U x y
  exact (Submodule.Quotient.mk_add U)

theorem map_smul : Specs.D05.M06.QuotientMap.map_smul := by
  intro K V _ _ _ U a x
  exact Submodule.Quotient.mk_smul U a x

theorem surjective : Specs.D05.M06.QuotientMap.surjective := by
  intro K V _ _ _ U x
  exact D05.M06.Quotient.every_class_representative U x

theorem range_eq_top : Specs.D05.M06.QuotientMap.range_eq_top := by
  intro K V _ _ _ U
  apply top_unique
  intro x _
  exact surjective U x

theorem eq_zero_iff : Specs.D05.M06.QuotientMap.eq_zero_iff := by
  intro K V _ _ _ U x
  exact Submodule.Quotient.mk_eq_zero U

theorem kernel_eq : Specs.D05.M06.QuotientMap.kernel_eq := by
  intro K V _ _ _ U
  apply Submodule.ext
  intro x
  exact (LinearMap.mem_ker).trans (eq_zero_iff U x)

end D05.M06.QuotientMap
