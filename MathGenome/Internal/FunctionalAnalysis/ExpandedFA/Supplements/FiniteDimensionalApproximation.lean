import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.FiniteDimensionalApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.StrictApproximation
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-! Best approximation in a finite-dimensional subspace of an arbitrary normed
space, including closed nonconvex subsets and the zero-dimensional case. -/
namespace ExpandedFA.Supplements.FiniteDimensionalApproximation
universe u v
noncomputable section
open Set

/-- Restrict the distance to a nonempty compact sublevel in the subspace.
Triangle inequality bounds that sublevel without assuming ambient completeness. -/
theorem closed_subset_nearest_point : Spec.ClosedSubsetExistence.{u,v} := by
  intro 𝕜 E _ _ _ M _ C hCne hCclosed x
  obtain ⟨a, ha⟩ := hCne
  let f : M → ℝ := fun z => ‖x - (z : E)‖
  let S : Set M := C ∩ {z | f z ≤ f a}
  have hf : Continuous f := (continuous_const.sub continuous_subtype_val).norm
  have hSclosed : IsClosed S := hCclosed.inter (isClosed_le hf continuous_const)
  have hSbounded : Bornology.IsBounded S := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨f a + ‖x‖, ?_⟩
    intro z hz
    calc
      ‖z‖ ≤ ‖(z : E) - x‖ + ‖x‖ := norm_le_norm_sub_add (z : E) x
      _ = f z + ‖x‖ := by rw [norm_sub_rev]
      _ ≤ f a + ‖x‖ := add_le_add (show f z ≤ f a from hz.2) (le_refl ‖x‖)
  have hScompact : IsCompact S :=
    (P1.C01FiniteDimension.finite_dimensional_closed_bounded_compact 𝕜 M S).mpr
      ⟨hSclosed, hSbounded⟩
  have haS : a ∈ S := ⟨ha, show f a ≤ f a from le_rfl⟩
  obtain ⟨z, hz, hmin⟩ := hScompact.exists_isMinOn ⟨a, haS⟩ hf.continuousOn
  refine ⟨z, ⟨z, hz.1, rfl⟩, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  change f z ≤ f w
  by_cases hwa : f w ≤ f a
  · exact hmin ⟨hw, hwa⟩
  · exact (hmin haS).trans (le_of_not_ge hwa)

/-- Take the entire finite-dimensional subspace as the approximating set. -/
theorem subspace_nearest_point : Spec.SubspaceExistence.{u,v} := by
  intro 𝕜 E _ _ _ M _ x
  obtain ⟨z, hz⟩ := closed_subset_nearest_point 𝕜 E M Set.univ
    Set.univ_nonempty isClosed_univ x
  refine ⟨(z : E), z.property, ?_⟩
  intro y hy
  exact hz.2 y ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩

/-- Reuse strict convexity's uniqueness theorem for arbitrary convex sets. -/
theorem convex_subset_nearest_point_unique : Spec.ConvexSubsetUniqueness.{u,v} := by
  intro 𝕜 E _ _ _ hrot
  exact (P1.StrictApproximation.rotund_iff_nearest_unique 𝕜 E).mp hrot

end
end ExpandedFA.Supplements.FiniteDimensionalApproximation
