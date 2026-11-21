import MathGenome.Internal.Specs.D05.M06.Projection
import MathGenome.Internal.D05.M03.Image
import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M06.DirectSum
import Mathlib.LinearAlgebra.Projection

/-! K05.06.projection: arbitrary algebraic idempotents and internal decompositions. -/

namespace D05.M06.Projection

theorem range_iff_fixed : Specs.D05.M06.Projection.range_iff_fixed := by
  intro K V _ _ _ P hP v
  have hp : IsIdempotentElem P := by simpa only [IsIdempotentElem, pow_two] using hP
  exact LinearMap.IsIdempotentElem.mem_range_iff hp

theorem decomposition_formula : Specs.D05.M06.Projection.decomposition_formula := by
  intro K V _ _ _ P hP v
  have hp : P (P v) = P v := by
    exact (range_iff_fixed P hP (P v)).mp (LinearMap.mem_range_self P v)
  refine ⟨LinearMap.mem_range_self P v, ?_, ?_⟩
  · change P (v - P v) = 0
    rw [map_sub, hp, sub_self]
  · rw [← add_sub_assoc, add_sub_cancel_left]

theorem range_kernel_direct_sum : Specs.D05.M06.Projection.range_kernel_direct_sum := by
  intro K V _ _ _ P hP
  have hp : IsIdempotentElem P := by simpa only [IsIdempotentElem, pow_two] using hP
  exact (D05.M06.DirectSum.pair_internal_iff_sup_inf P.range P.ker).mpr
    ⟨(LinearMap.IsIdempotentElem.isCompl hp).sup_eq_top, (LinearMap.IsIdempotentElem.isCompl hp).inf_eq_bot⟩

theorem projection_exists_unique : Specs.D05.M06.Projection.projection_exists_unique := by
  intro K V _ _ _ U W h
  obtain ⟨hs, hi⟩ := (D05.M06.DirectSum.pair_internal_iff_sup_inf U W).mp h
  have hc : IsCompl U W := isCompl_iff.mpr ⟨disjoint_iff.mpr hi, codisjoint_iff.mpr hs⟩
  let P : Module.End K V := U.projection W hc
  have hp : IsIdempotentElem P := Submodule.isIdempotentElem_projection hc
  have hr : P.range = U := Submodule.range_projection hc
  have hk : P.ker = W := Submodule.ker_projection hc
  refine ⟨P, ⟨?_, hr, hk⟩, ?_⟩
  · simpa only [pow_two] using hp.eq
  · rintro Q ⟨hq, hqr, hqk⟩
    have hqi : IsIdempotentElem Q := by simpa only [IsIdempotentElem, pow_two] using hq
    exact LinearMap.IsIdempotentElem.ext hqi hp ⟨hqr.trans hr.symm, hqk.trans hk.symm⟩

theorem projection_apply_sum : Specs.D05.M06.Projection.projection_apply_sum := by
  intro K V _ _ _ U W P hp hr hk u w hu hw
  have hpu : P u = u := (range_iff_fixed P hp u).mp (hr.symm ▸ hu)
  have hpw : P w = 0 := LinearMap.mem_ker.mp (hk.symm ▸ hw)
  rw [map_add, hpu, hpw, add_zero]

end D05.M06.Projection
