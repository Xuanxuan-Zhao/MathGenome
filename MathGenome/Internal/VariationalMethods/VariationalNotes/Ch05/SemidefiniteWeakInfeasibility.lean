import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.SemidefiniteWeakInfeasibility
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.NonclosedPSDImage

noncomputable section
open Set Filter
open VariationalNotes.ConvexGeometry.PSDImage

namespace VariationalNotes.Ch05.SemidefiniteWeakInfeasibility

theorem projectedCone_description : Specs.projectedCone_description :=
  VariationalNotes.ConvexGeometry.PSDImage.projectedCone_description

theorem approximating_matrices : Specs.approximating_matrices := by
  intro n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · change symmetricMatrix (1 / (n : ℝ)) 1 (n : ℝ) ∈ psdCone
    have h := positive_psd_lift (1 / (n : ℝ)) 1 (one_div_pos.mpr hn')
    simpa only [one_pow, one_div_one_div] using h
  · rfl

theorem projected_matrices_tendsto : Specs.projected_matrices_tendsto := by
  exact tendsto_one_div_atTop_nhds_zero_nat.prodMk_nhds tendsto_const_nhds

theorem target_not_mem : Specs.target_not_mem :=
  VariationalNotes.ConvexGeometry.PSDImage.target_not_mem

theorem target_mem_closure : Specs.target_mem_closure :=
  VariationalNotes.ConvexGeometry.PSDImage.target_mem_closure

theorem target_weakly_infeasible : Specs.target_weakly_infeasible := by
  exact ⟨target_not_mem, target_mem_closure⟩

theorem nonnegative_at_target : Specs.nonnegative_at_target := by
  intro l hl
  have hclosure : closure projectedCone ⊆ {p | 0 ≤ l p} :=
    closure_minimal hl (isClosed_le continuous_const l.continuous)
  exact hclosure target_mem_closure

theorem no_strict_farkas_certificate : Specs.no_strict_farkas_certificate := by
  rintro ⟨l, hl, hneg⟩
  exact (not_lt_of_ge (nonnegative_at_target l hl)) hneg

end VariationalNotes.Ch05.SemidefiniteWeakInfeasibility
