import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorSegments
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeInteriorIntersections
import Batteries.Tactic.OpenPrivate

open Set
noncomputable section
universe u v
namespace VariationalNotes.ConvexGeometry

open private mem_openSegment_extension from
  MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorSegments

private theorem exists_positive_common_bound {ι : Type v} [Finite ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ s : ℝ, 0 < s ∧ ∀ i, s ≤ r i := by
  classical
  letI := Fintype.ofFinite ι
  have h (J : Finset ι) : ∃ s : ℝ, 0 < s ∧ ∀ i ∈ J, s ≤ r i := by
    induction J using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i J hi ih =>
      obtain ⟨s, hs, hJ⟩ := ih
      refine ⟨min s (r i), lt_min hs (hr i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hJ j hj)
  obtain ⟨s, hs, hbound⟩ := h Finset.univ
  exact ⟨s, hs, fun i => hbound i (Finset.mem_univ i)⟩

private theorem extension_downward {E : Type u} [AddCommGroup E] [Module ℝ E]
    {C : Set E} (hC : Convex ℝ C) {x y : E} (hx : x ∈ C)
    {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r)
    (hz : x + r • (x - y) ∈ C) : x + s • (x - y) ∈ C := by
  have h := hC hx hz (sub_nonneg.mpr ((div_le_one hr).mpr hsr))
    (div_nonneg hs hr.le) (sub_add_cancel 1 (s/r))
  have heq : (1-s/r) • x + (s/r) • (x + r • (x-y)) = x + s • (x-y) := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ (ne_of_gt hr)]
    module
  exact heq ▸ h

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E] {ι : Type v} [Finite ι]

/-- Relative interior commutes with a finite intersection having a common
relative-interior point, including intersections of lower-dimensional sets. -/
theorem relativeInterior_iInter (C : ι → Set E) (hC : ∀ i, Convex ℝ (C i))
    (hne : (⋂ i, relativeInterior (C i)).Nonempty) :
    relativeInterior (⋂ i, C i) = ⋂ i, relativeInterior (C i) := by
  obtain ⟨a, ha⟩ := hne
  have haC : a ∈ ⋂ i, C i := mem_iInter.mpr fun i =>
    intrinsicInterior_subset (mem_iInter.mp ha i)
  have hconv : Convex ℝ (⋂ i, C i) := convex_iInter hC
  apply subset_antisymm
  · intro x hx
    have hxC : x ∈ ⋂ i, C i := intrinsicInterior_subset hx
    obtain ⟨s, hs, hz⟩ :=
      (mem_relativeInterior_iff_extendible _ hconv x hxC).mp hx a haC
    apply mem_iInter.mpr
    intro i
    exact (hC i).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      (mem_iInter.mp ha i) (subset_intrinsicClosure (mem_iInter.mp hz i))
      (mem_openSegment_extension x a hs)
  · intro x hx
    have hxC : x ∈ ⋂ i, C i := mem_iInter.mpr fun i =>
      intrinsicInterior_subset (mem_iInter.mp hx i)
    apply (mem_relativeInterior_iff_extendible _ hconv x hxC).mpr
    intro y hy
    have hext : ∀ i, ∃ r : ℝ, 0 < r ∧ x + r • (x-y) ∈ C i := fun i =>
      (mem_relativeInterior_iff_extendible _ (hC i) x (mem_iInter.mp hxC i)).mp
        (mem_iInter.mp hx i) y (mem_iInter.mp hy i)
    choose r hr hz using hext
    obtain ⟨s, hs, hsr⟩ := exists_positive_common_bound r hr
    exact ⟨s, hs, mem_iInter.mpr fun i =>
      extension_downward (hC i) (mem_iInter.mp hxC i) (hr i) hs.le (hsr i) (hz i)⟩

/-- A common relative-interior point also gives the intersection closure identity. -/
theorem closure_iInter (C : ι → Set E) (hC : ∀ i, Convex ℝ (C i))
    (hne : (⋂ i, relativeInterior (C i)).Nonempty) :
    closure (⋂ i, C i) = ⋂ i, closure (C i) := by
  apply subset_antisymm
  · intro x hx
    exact mem_iInter.mpr fun i => closure_mono (iInter_subset C i) hx
  · obtain ⟨a, ha⟩ := hne
    intro b hb
    have hseg : openSegment ℝ a b ⊆ ⋂ i, C i := by
      rintro z ⟨u, t, hu, ht, hut, rfl⟩
      apply mem_iInter.mpr
      intro i
      have heq : u = 1-t := by linarith
      rw [heq]
      exact intrinsicInterior_subset (relativeInterior_halfOpenSegment (C i) (hC i)
        a b (mem_iInter.mp ha i) (mem_iInter.mp hb i) t ht.le (by linarith))
    exact closure_mono hseg
      (segment_subset_closure_openSegment (right_mem_segment ℝ a b))

end VariationalNotes.ConvexGeometry
