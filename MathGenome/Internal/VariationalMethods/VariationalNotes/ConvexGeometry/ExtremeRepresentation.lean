import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeBoundarySupport
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.ExtremeRepresentation
import Mathlib.Analysis.Convex.KreinMilman

open Set
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry

section Normed
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Density of the extreme-point hull already represents every relative-interior point. -/
private theorem relativeInterior_subset_extremePoint_hull (C : Set E)
    (hne : C.Nonempty) (hc : IsCompact C) (hv : Convex ℝ C) :
    relativeInterior C ⊆ convexHull ℝ (C.extremePoints ℝ) := by
  let D := convexHull ℝ (C.extremePoints ℝ)
  have hDne : D.Nonempty := (hc.extremePoints_nonempty hne).mono (subset_convexHull ℝ _)
  have hri := relativeInterior_closure D (convex_convexHull ℝ _) hDne
  have hcl : closure D = C := closure_convexHull_extremePoints hc hv
  rw [hcl] at hri
  intro x hx
  exact intrinsicInterior_subset (hri ▸ hx)

/-- A relative boundary point belongs to a proper exposed face of smaller affine dimension. -/
private theorem exists_smaller_exposed_face (C : Set E) (hc : IsCompact C)
    (hv : Convex ℝ C) (x : E) (hx : x ∈ C) (hxr : x ∉ relativeInterior C) :
    ∃ F : Set E, x ∈ F ∧ IsCompact F ∧ Convex ℝ F ∧ IsExtreme ℝ C F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction <
        Module.finrank ℝ (affineSpan ℝ C).direction := by
  obtain ⟨n, -, hn, y, hy, hny⟩ :=
    relativeBoundary_support C ⟨x, hx⟩ hc.isClosed hv x hx hxr
  obtain ⟨f, hf⟩ := n.exists_extend
  have hf_apply (y : E) (hy : y ∈ C) : f (y - x) =
      n ⟨y - x, AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hx)⟩ :=
    LinearMap.congr_fun hf ⟨y - x, AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hx)⟩
  have hle (y : E) (hy : y ∈ C) : f y ≤ f x := by
    have := hn y hy
    rw [← hf_apply y hy, map_sub] at this
    linarith
  have hlt : f y < f x := by
    rw [← hf_apply y hy, map_sub] at hny
    linarith
  let l := f.toContinuousLinearMap
  let F : Set E := {z ∈ C | ∀ w ∈ C, l w ≤ l z}
  have he : IsExposed ℝ C F := fun _ => ⟨l, rfl⟩
  have hxF : x ∈ F := ⟨hx, hle⟩
  have hFlevel (z : E) (hz : z ∈ F) : f z = f x :=
    (hle z hz.1).antisymm (hz.2 x hx)
  let H : AffineSubspace ℝ E :=
    ({f x} : AffineSubspace ℝ ℝ).comap f.toAffineMap
  have hspan : affineSpan ℝ F ≤ H := by
    apply affineSpan_le.mpr
    intro z hz
    exact hFlevel z hz
  have hproper : affineSpan ℝ F < affineSpan ℝ C := by
    refine lt_of_le_of_ne (affineSpan_mono ℝ he.subset) ?_
    intro heq
    have hyH := hspan (heq ▸ subset_affineSpan ℝ C hy)
    change f y = f x at hyH
    exact hlt.ne hyH
  exact ⟨F, hxF, he.isCompact hc, he.convex hv, he.isExtreme,
    Submodule.finrank_lt_finrank_of_lt
      (AffineSubspace.direction_lt_of_nonempty hproper ⟨x, subset_affineSpan ℝ F hxF⟩)⟩

private theorem mem_extremePoint_hull (C : Set E) (hc : IsCompact C)
    (hv : Convex ℝ C) (x : E) (hx : x ∈ C) :
    x ∈ convexHull ℝ (C.extremePoints ℝ) := by
  generalize hd : Module.finrank ℝ (affineSpan ℝ C).direction = d
  induction d using Nat.strong_induction_on generalizing C x with
  | h d ih =>
    by_cases hxr : x ∈ relativeInterior C
    · exact relativeInterior_subset_extremePoint_hull C ⟨x, hx⟩ hc hv hxr
    · obtain ⟨F, hxF, hcF, hvF, heF, hdim⟩ := exists_smaller_exposed_face C hc hv x hx hxr
      have hF := ih _ (hd ▸ hdim) F hcF hvF x hxF rfl
      exact convexHull_mono heF.extremePoints_subset_extremePoints hF

end Normed

/-- The finite-dimensional extreme point representation, without a closure on the hull. -/
theorem extremePoint_representation
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C : Set E)
    (_hne : C.Nonempty) (hc : IsCompact C) (hv : Convex ℝ C) :
    C = convexHull ℝ (C.extremePoints ℝ) := by
  let : IsNormableSpace ℝ E := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup ℝ E
  let : NormedSpace ℝ E := IsNormableSpace.toNormedSpace ℝ E
  let : NormedAddCommGroup E := { MetricSpace.ofT0PseudoMetricSpace E with
    dist_eq := dist_eq_norm_neg_add }
  exact subset_antisymm (fun x hx => mem_extremePoint_hull C hc hv x hx)
    (convexHull_min extremePoints_subset hv)

end VariationalNotes.ConvexGeometry
