import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualMaps
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
Norming and distance-separating functionals, `fa2:p1:c05:norming`.

Mathlib's `exists_dual_vector` is valid over both scalar fields, without
completeness, and gives the positive real norm as its scalar value.
For distance separation we norm the nonzero coset in the quotient by the
closure of the original subspace. The accepted quotient-dual isometry
pulls this functional back with exactly the same norm. The quotient norm
is distance to the closure, which equals distance to the original subspace.
-/

namespace ExpandedFA.P1.C05Norming

universe u v

theorem norming_functional_nonzero : Spec.NonzeroNormingFunctional.{u, v} := by
  intro 𝕜 E _ _ _ x hx
  exact exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)

theorem norming_functional_zero : Spec.ZeroNormingFunctional.{u, v} := by
  intro 𝕜 E _ _ _ x hx
  simp [hx]

theorem norming_functional : Spec.NormingFunctional.{u, v} := by
  intro 𝕜 E _ _ _ x
  by_cases hx : x = 0
  · exact ⟨0, norming_functional_zero 𝕜 E x hx⟩
  · obtain ⟨f, hf, hfx⟩ := norming_functional_nonzero 𝕜 E x hx
    exact ⟨f, hf.le, hfx⟩

theorem subspace_distance_formulas : Spec.SubspaceDistanceFormulas.{u, v} := by
  intro 𝕜 E _ _ _ M x
  have h := C02QuotientNorm.distanceSeminorm_mk 𝕜 E M x
  exact ⟨Metric.infDist_closure, h.2.1.symm.trans h.1⟩

theorem distance_norming_functional : Spec.DistanceNormingFunctional.{u, v} := by
  intro 𝕜 E _ _ _ M x hx
  let N := M.topologicalClosure
  have hN : IsClosed (N : Set E) := M.isClosed_topologicalClosure
  letI : IsClosed (N : Set E) := hN
  have hqx : N.mkQ x ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero N).mp h)
  obtain ⟨g, hg, hgx⟩ := norming_functional_nonzero 𝕜 (E ⧸ N) (N.mkQ x) hqx
  obtain ⟨e, he⟩ := C04DualMaps.quotient_dual_isometry 𝕜 E N hN
  have hdist : ‖N.mkQ x‖ = Metric.infDist x (M : Set E) := by
    calc
      ‖N.mkQ x‖ = Metric.infDist x (N : Set E) := QuotientAddGroup.norm_mk x
      _ = Metric.infDist x (M : Set E) := Metric.infDist_closure
  refine ⟨(e g).val, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact (e g).property m (M.le_topologicalClosure hm)
  · exact (e.norm_map g).trans hg
  · rw [he g x, hgx, hdist]
  · exact (Metric.infDist_pos_iff_notMem_closure ⟨0, M.zero_mem⟩).mp hx

end ExpandedFA.P1.C05Norming
