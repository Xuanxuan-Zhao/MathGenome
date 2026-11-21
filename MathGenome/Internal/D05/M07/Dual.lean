import MathGenome.Internal.D05.M03.MapAlgebra
import MathGenome.Internal.Specs.D05.M07.Dual

/-! K05.07.dual: the algebraic dual and its pointwise vector-space structure. -/

namespace D05.M07.Dual

/-- The algebraic dual consists of all linear maps to the scalar field. -/
abbrev algebraicDual (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  Module.Dual K V

/-- Specialize the existing Hom-space module structure to scalar-valued maps. -/
abbrev dualModule (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Module K (algebraicDual K V) :=
  D05.M03.MapAlgebra.homModule K V K

theorem functional_iff_axioms : Specs.D05.M07.Dual.functional_iff_axioms := by
  intro K V _ _ _ t
  exact D05.M03.LinearMap.linearMap_iff_axioms t

theorem add_apply : Specs.D05.M07.Dual.add_apply := by
  intro K V _ _ _ f g v
  exact D05.M03.MapAlgebra.add_apply f g v

theorem smul_apply : Specs.D05.M07.Dual.smul_apply := by
  intro K V _ _ _ a f v
  exact D05.M03.MapAlgebra.smul_apply a f v

theorem zero_apply : Specs.D05.M07.Dual.zero_apply := by
  intro K V _ _ _ v
  exact D05.M03.MapAlgebra.zero_apply v

theorem neg_apply : Specs.D05.M07.Dual.neg_apply := by
  intro K V _ _ _ f v
  exact D05.M03.MapAlgebra.neg_apply f v

theorem map_add : Specs.D05.M07.Dual.map_add := by
  intro K V _ _ _ f u v
  exact f.map_add u v

theorem map_smul : Specs.D05.M07.Dual.map_smul := by
  intro K V _ _ _ f a v
  exact f.map_smul a v

end D05.M07.Dual
