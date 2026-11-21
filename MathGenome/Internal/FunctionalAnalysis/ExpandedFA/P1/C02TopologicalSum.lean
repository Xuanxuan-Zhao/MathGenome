import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02TopologicalSum

/-! Topological direct sums and bounded projections, Definition fa2:p1:c02:topological-sum.
The native structures use the given norm and inherited subspace topologies.
No Banach or closed-subspace assumption is imposed. -/
namespace ExpandedFA.P1.C02TopologicalSum

universe u v

/-- Each vector has unique coordinates in the two subspaces and the coordinate
maps are bounded. See `topological_direct_sum_iff_coordinates`. -/
abbrev TopologicalDirectSum : Spec.TopologicalDirectSumType.{u, v} :=
  fun {_ _} [_] [_] [_] M N => Submodule.IsTopCompl M N

/-- Existence of a companion giving a topological direct sum. -/
def Complemented : Spec.ComplementedType.{u, v} :=
  fun {_ _} [_] [_] [_] M => ∃ N : Submodule _ _, TopologicalDirectSum M N

/-- Boundedness and linearity are carried by the native operator type. -/
def IsBoundedProjection : Spec.IsBoundedProjectionType.{u, v} :=
  fun {_ _} [_] [_] [_] P => P.comp P = P

noncomputable def leftCoordinate : Spec.LeftCoordinateType.{u, v} :=
  fun {_ _} [_] [_] [_] M N h => M.projectionOntoL N h

noncomputable def rightCoordinate : Spec.RightCoordinateType.{u, v} :=
  fun {_ _} [_] [_] [_] M N h => N.projectionOntoL M h.symm

/-- The native predicate has exactly the source's unique bounded-coordinate meaning. -/
theorem topological_direct_sum_iff_coordinates :
    Spec.CoordinateCharacterization.{u, v} := by
  intro 𝕜 E _ _ _ M N
  constructor
  · intro h
    refine ⟨leftCoordinate M N h, rightCoordinate M N h, ?_⟩
    intro x
    refine ⟨Submodule.projectionL_add_projectionL_eq_self h x, ?_⟩
    intro m n hmn
    constructor
    · simpa [leftCoordinate] using congrArg (M.projectionOntoL N h) hmn
    · simpa [rightCoordinate] using congrArg (N.projectionOntoL M h.symm) hmn
  · rintro ⟨p, q, h⟩
    have hfix : ∀ m : M, p m = m := by
      intro m
      exact ((h m).2 m 0 (by simp)).1.symm
    have hker : p.ker = N := by
      ext x
      constructor
      · intro hx
        have hp : p x = 0 := hx
        have hxq : (q x : E) = x := by simpa [hp] using (h x).1
        exact hxq ▸ (q x).property
      · intro hx
        have hp := ((h x).2 0 ⟨x, hx⟩ (by simp)).1
        exact hp.symm
    rw [← hker]
    exact p.isTopCompl_of_proj hfix

/-- Continuity of the native projections is exactly a norm bound on each
coordinate map, including for the zero space and zero summands. -/
theorem topological_direct_sum_iff_bounded_coordinates :
    Spec.BoundedCoordinateCharacterization.{u, v} := by
  intro 𝕜 E _ _ _ M N
  constructor
  · intro h
    obtain ⟨p, q, hpq⟩ := (topological_direct_sum_iff_coordinates 𝕜 E M N).mp h
    exact ⟨p.toLinearMap, q.toLinearMap, ‖p‖, ‖q‖,
      norm_nonneg p, norm_nonneg q, p.le_opNorm, q.le_opNorm, hpq⟩
  · rintro ⟨p, q, C, D, _, _, hp, hq, hpq⟩
    exact (topological_direct_sum_iff_coordinates 𝕜 E M N).mpr
      ⟨p.mkContinuous C hp, q.mkContinuous D hq, hpq⟩

theorem topological_direct_sum_unique_decomposition :
    Spec.UniqueDecomposition.{u, v} := by
  intro 𝕜 E _ _ _ M N h x
  exact Submodule.existsUnique_add_of_isCompl_prod h.isCompl x

theorem coordinate_bounds : Spec.CoordinateBounds.{u, v} := by
  intro 𝕜 E _ _ _ M N h
  exact ⟨⟨‖M.projectionOntoL N h‖, norm_nonneg _, (M.projectionOntoL N h).le_opNorm⟩,
    ⟨‖N.projectionOntoL M h.symm‖, norm_nonneg _, (N.projectionOntoL M h.symm).le_opNorm⟩⟩

theorem complemented_iff_native :
    Spec.ComplementedIdentification.{u, v} := by
  intro 𝕜 E _ _ _ M
  exact Submodule.closedComplemented_iff_exists_isTopCompl.symm

theorem bounded_projection_iff_idempotent :
    Spec.ProjectionIdempotence.{u, v} := by
  intro 𝕜 E _ _ _ P
  rfl

theorem bounded_projection_iff_native_projection :
    Spec.ProjectionIdentification.{u, v} := by
  intro 𝕜 E _ _ _ P
  exact ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker

end ExpandedFA.P1.C02TopologicalSum
