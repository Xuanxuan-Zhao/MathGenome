import MathGenome.Internal.Specs.D05.M07.DoubleAnnihilator
import MathGenome.Internal.D05.M07.Annihilator
import MathGenome.Internal.D05.M07.Biddual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! K05.07.double_annihilator: double annihilation and transport to the bidual. -/

namespace D05.M07.DoubleAnnihilator

/-- Mathlib's coannihilator is pointwise vanishing on the submodule of
functionals. Spanning its carrier makes no change, and its double-annihilation
theorem holds over a field without any additional separation assumption. -/
theorem double_annihilator : Specs.D05.M07.DoubleAnnihilator.double_annihilator := by
  intro K V _ _ _ _ U
  simpa only [Submodule.span_eq] using
    (Subspace.dualAnnihilator_dualCoannihilator_eq (W := U))

/-- Pulling the bidual annihilator back by evaluation is, by definition,
the coannihilator in V. The preceding identity then recovers U. -/
theorem evaluation_mem_iff : Specs.D05.M07.DoubleAnnihilator.evaluation_mem_iff := by
  intro K V _ _ _ _ U v
  have h : U.dualAnnihilator.dualCoannihilator = U := by
    simpa only [Submodule.span_eq] using double_annihilator U
  change v ∈ U.dualAnnihilator.dualCoannihilator ↔ v ∈ U
  rw [h]

/-- Every bidual vector is an evaluation in finite dimension. Membership in
the annihilator therefore reduces to membership of its preimage in U. -/
theorem bidual_annihilator : Specs.D05.M07.DoubleAnnihilator.bidual_annihilator := by
  intro K V _ _ _ _ U
  apply le_antisymm
  · intro F hF
    obtain ⟨v, rfl⟩ := (D05.M07.Biddual.evaluation_bijective (K := K) (V := V)).2 F
    exact Submodule.mem_map.mpr ⟨v, (evaluation_mem_iff U v).mp hF, rfl⟩
  · intro F hF
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hF
    exact (evaluation_mem_iff U v).mpr hv

end D05.M07.DoubleAnnihilator
