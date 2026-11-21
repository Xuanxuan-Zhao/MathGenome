import MathGenome.Internal.D05.M07.Dual
import MathGenome.Internal.Specs.D05.M07.DualMap

/-! K05.07.dual_map: algebraic precomposition and its contravariant laws. -/

namespace D05.M07.DualMap

/-- Pull a functional back by ordinary composition, over the stated field. -/
abbrev dualMap {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) :
    D05.M07.Dual.algebraicDual K W →ₗ[K] D05.M07.Dual.algebraicDual K V :=
  T.dualMap

theorem dualMap_apply : Specs.D05.M07.DualMap.dualMap_apply := by
  intro K V W _ _ _ _ _ T f
  rfl

theorem dualMap_apply_apply : Specs.D05.M07.DualMap.dualMap_apply_apply := by
  intro K V W _ _ _ _ _ T f v
  rfl

theorem map_add : Specs.D05.M07.DualMap.map_add := by
  intro K V W _ _ _ _ _ T f g
  exact T.dualMap.map_add f g

theorem map_smul : Specs.D05.M07.DualMap.map_smul := by
  intro K V W _ _ _ _ _ T a f
  exact T.dualMap.map_smul a f

theorem dualMap_comp : Specs.D05.M07.DualMap.dualMap_comp := by
  intro K V W X _ _ _ _ _ _ _ S T
  rfl

theorem dualMap_id : Specs.D05.M07.DualMap.dualMap_id := by
  intro K V _ _ _
  exact LinearMap.dualMap_id

theorem dualMap_add : Specs.D05.M07.DualMap.dualMap_add := by
  intro K V W _ _ _ _ _ S T
  ext f v
  exact f.map_add (S v) (T v)

theorem dualMap_smul : Specs.D05.M07.DualMap.dualMap_smul := by
  intro K V W _ _ _ _ _ a T
  ext f v
  exact f.map_smul a (T v)

theorem dualMap_linear_combination :
    Specs.D05.M07.DualMap.dualMap_linear_combination := by
  intro K V W _ _ _ _ _ a b S T
  rw [dualMap_add, dualMap_smul, dualMap_smul]

theorem complex_no_conjugation : Specs.D05.M07.DualMap.complex_no_conjugation := by
  intro V W _ _ _ _ a T f v
  exact f.map_smul a (T v)

end D05.M07.DualMap
