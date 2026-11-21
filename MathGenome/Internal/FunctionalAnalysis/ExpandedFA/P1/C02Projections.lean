import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02Projections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02TopologicalSum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FiniteDimensionalComplements
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FiniteCodimensionalComplements

/-! Bounded projections and their complementary coordinate maps,
Proposition `fa2:p1:c02:projections` (projection equivalence clause).
All arguments apply to arbitrary real or complex normed spaces, including
the zero space; no completeness hypothesis is used. -/

namespace ExpandedFA.P1.C02Projections

universe u v

theorem bounded_projection_direct_sum :
    Spec.ProjectionDecomposition.{u, v} := by
  intro 𝕜 E _ _ _ P hP
  obtain ⟨h, heq⟩ := (C02TopologicalSum.bounded_projection_iff_native_projection 𝕜 E P).mp hP
  refine ⟨h, h.isClosed, h.symm.isClosed, heq.symm, ?_⟩
  rw [Submodule.projectionL_eq_id_sub_projectionL h, ← heq]

theorem topological_direct_sum_closed :
    Spec.DirectSumClosed.{u, v} := by
  intro 𝕜 E _ _ _ M N h
  exact ⟨h.isClosed, h.symm.isClosed⟩

theorem topological_direct_sum_projections :
    Spec.DirectSumProjections.{u, v} := by
  intro 𝕜 E _ _ _ M N h
  refine ⟨M.projectionL N h, N.projectionL M h.symm, ?_, ?_,
    Submodule.range_projectionL h, Submodule.ker_projectionL h,
    Submodule.range_projectionL h.symm, Submodule.ker_projectionL h.symm,
    Submodule.projectionL_add_projectionL_eq_id h, ?_⟩
  · exact Submodule.isIdempotentElem_projectionL h
  · exact Submodule.isIdempotentElem_projectionL h.symm
  · intro x
    exact ⟨rfl, rfl⟩

/-- Assemble the accepted finite-dimensional projection construction. -/
theorem finite_dimensional_complemented :
    Spec.FiniteDimensionalComplement.{u, v} := by
  intro 𝕜 E _ _ _ M _
  obtain ⟨hM, hcomp, N, hN, htop⟩ :=
    FiniteDimensionalComplements.finite_dimensional_complemented 𝕜 E M
  exact ⟨hcomp, N, hM, hN, htop⟩

/-- Assemble the accepted bounded quotient-section construction. -/
theorem finite_codimensional_complemented :
    Spec.FiniteCodimensionalComplement.{u, v} := by
  intro 𝕜 E _ _ _ M hM _
  obtain ⟨N, hfinite, hN, htop⟩ :=
    FiniteCodimensionalComplements.finite_codimensional_complemented 𝕜 E M hM
  exact ⟨⟨N, htop⟩, N, hfinite, hN, htop⟩

end ExpandedFA.P1.C02Projections
