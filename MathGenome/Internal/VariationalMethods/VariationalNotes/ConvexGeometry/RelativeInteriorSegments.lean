import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Foundations
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeInteriorSegments
import Mathlib.Tactic.Module

open Set Topology
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E]

/-- A compatible norm is used only to invoke the finite-dimensional nonemptiness theorem. -/
theorem relativeInterior_nonempty (C : Set E) (hC : Convex ℝ C) (hne : C.Nonempty) :
    (relativeInterior C).Nonempty := by
  let : IsNormableSpace ℝ E := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup ℝ E
  let : NormedSpace ℝ E := IsNormableSpace.toNormedSpace ℝ E
  let : NormedAddCommGroup E := { MetricSpace.ofT0PseudoMetricSpace E with
    dist_eq := dist_eq_norm_neg_add }
  exact Set.Nonempty.intrinsicInterior hC hne

private theorem affineSpan_isClosed (C : Set E) : IsClosed (affineSpan ℝ C : Set E) := by
  exact (affineSpan ℝ C).isClosed_direction_iff.mp
    (affineSpan ℝ C).direction.closed_of_finiteDimensional

private theorem intrinsicClosure_eq_ambientClosure (C : Set E) :
    intrinsicClosure ℝ C = closure C := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  exact inter_eq_left.mpr (closure_minimal (subset_affineSpan ℝ C) (affineSpan_isClosed C))

/-- The coefficient of the relative-interior endpoint remains positive. -/
theorem relativeInterior_halfOpenSegment (C : Set E) (hC : Convex ℝ C)
    (a b : E) (ha : a ∈ relativeInterior C) (hb : b ∈ closure C)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) • a + t • b ∈ relativeInterior C := by
  rcases eq_or_lt_of_le ht0 with rfl | ht0
  · simpa using ha
  · apply hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior ha
      (by rwa [intrinsicClosure_eq_ambientClosure])
    exact ⟨1-t, t, sub_pos.mpr ht1, ht0, sub_add_cancel 1 t, rfl⟩

omit [T2Space E] [FiniteDimensional ℝ E] in
/-- Continuity of a line in the affine span permits extension past an interior point. -/
private theorem exists_extension_of_mem_relativeInterior {C : Set E} {x : E}
    (hx : x ∈ relativeInterior C) {y : E} (hy : y ∈ C) :
    ∃ s : ℝ, 0 < s ∧ x + s • (x - y) ∈ C := by
  obtain ⟨xA, hxA, rfl⟩ := (mem_intrinsicInterior).mp hx
  let : Nonempty (affineSpan ℝ C) := ⟨xA⟩
  let yA : affineSpan ℝ C := ⟨y, subset_affineSpan ℝ C hy⟩
  have h := AffineMap.lineMap_apply_one (k := ℝ) yA xA
  obtain ⟨t, ht, hmem⟩ := AffineMap.lineMap_continuous.tendsto' _ _ h |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp hxA) |>.exists_gt
  refine ⟨t - 1, sub_pos.mpr ht, ?_⟩
  have heq : (AffineMap.lineMap yA xA t : E) = (xA : E) + (t - 1) • ((xA : E) - y) := by
    rw [← (affineSpan ℝ C).subtype_apply, AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_module]
    change (1-t) • y + t • (xA : E) = _
    module
  exact heq ▸ hmem

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [T2Space E] [FiniteDimensional ℝ E] in
/-- A point is in the open segment from `y` to its positive extension away from `y`. -/
private theorem mem_openSegment_extension (x y : E) {s : ℝ} (hs : 0 < s) :
    x ∈ openSegment ℝ y (x + s • (x - y)) := by
  have hsp : 0 < 1+s := by linarith
  refine ⟨s/(1+s), 1/(1+s), div_pos hs hsp, div_pos zero_lt_one hsp, ?_, ?_⟩
  · field_simp
    ring
  · simp only [smul_add, smul_sub, smul_smul]
    have hc : 1/(1+s) + 1/(1+s)*s = (1 : ℝ) := by field_simp
    have hd : s/(1+s) = 1/(1+s)*s := by ring
    rw [hd]
    calc
      _ = (1/(1+s) + 1/(1+s)*s) • x := by module
      _ = x := by rw [hc, one_smul]

/-- The extension characterization does not require a positive-dimensional affine hull. -/
theorem mem_relativeInterior_iff_extendible (C : Set E) (hC : Convex ℝ C)
    (x : E) (hx : x ∈ C) : x ∈ relativeInterior C ↔
      ∀ y ∈ C, ∃ s : ℝ, 0 < s ∧ x + s • (x - y) ∈ C := by
  constructor
  · exact fun h y hy => exists_extension_of_mem_relativeInterior h hy
  · intro h
    obtain ⟨a, ha⟩ := relativeInterior_nonempty C hC ⟨x, hx⟩
    obtain ⟨s, hs, hz⟩ := h a (intrinsicInterior_subset ha)
    exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior ha
      (subset_intrinsicClosure hz) (mem_openSegment_extension x a hs)

/-- Approaching a closure point along an open segment gives density of the relative interior. -/
theorem closure_relativeInterior (C : Set E) (hC : Convex ℝ C) (hne : C.Nonempty) :
    closure (relativeInterior C) = closure C := by
  refine subset_antisymm (closure_mono intrinsicInterior_subset) ?_
  obtain ⟨a, ha⟩ := relativeInterior_nonempty C hC hne
  intro b hb
  exact closure_mono
    (hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior ha
      (by rwa [intrinsicClosure_eq_ambientClosure]))
    (segment_subset_closure_openSegment (right_mem_segment ℝ a b))

private theorem affineSpan_ambientClosure (C : Set E) :
    affineSpan ℝ (closure C) = affineSpan ℝ C := by
  exact (affineSpan_le.mpr (closure_minimal (subset_affineSpan ℝ C)
    (affineSpan_isClosed C))).antisymm (affineSpan_mono ℝ subset_closure)

/-- Closing a convex set leaves its relative interior unchanged. -/
theorem relativeInterior_closure (C : Set E) (hC : Convex ℝ C) (hne : C.Nonempty) :
    relativeInterior (closure C) = relativeInterior C := by
  apply subset_antisymm
  · obtain ⟨a, ha⟩ := relativeInterior_nonempty C hC hne
    intro x hx
    obtain ⟨s, hs, hz⟩ := exists_extension_of_mem_relativeInterior hx
      (subset_closure (intrinsicInterior_subset ha))
    exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior ha
      (by rwa [intrinsicClosure_eq_ambientClosure]) (mem_openSegment_extension x a hs)
  · change intrinsicInterior ℝ C ⊆ intrinsicInterior ℝ (closure C)
    rw [intrinsicInterior, intrinsicInterior, affineSpan_ambientClosure]
    exact image_mono (interior_mono (preimage_mono subset_closure))

end VariationalNotes.ConvexGeometry
