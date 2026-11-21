import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorIntersections
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeInteriorAffine

open Set
open scoped Pointwise
noncomputable section
universe u v w
namespace VariationalNotes.ConvexGeometry

open private mem_openSegment_extension from
  MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorSegments

section TwoSpaces
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
  [FiniteDimensional ℝ F]

private theorem map_extension (A : E →ᵃ[ℝ] F) (x y : E) (s : ℝ) :
    A (x + s • (x-y)) = A x + s • (A x - A y) := by
  have hl : A.linear (x-y) = A x - A y := A.linear_apply_vsub x y
  simpa only [vadd_eq_add, map_smul, hl, add_comm] using
    (A.map_vadd x (s • (x - y)))

private theorem image_relativeInterior_subset (A : E →ᵃ[ℝ] F)
    (C : Set E) (hC : Convex ℝ C) :
    A '' relativeInterior C ⊆ relativeInterior (A '' C) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxC : x ∈ C := intrinsicInterior_subset hx
  apply (mem_relativeInterior_iff_extendible _ (hC.affine_image A) _
    (mem_image_of_mem A hxC)).mpr
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨s, hs, hz⟩ :=
    (mem_relativeInterior_iff_extendible C hC x hxC).mp hx y hy
  exact ⟨s, hs, ⟨x + s • (x-y), hz, map_extension A x y s⟩⟩

/-- Lift an extension in the image, and take the corresponding open-segment point. -/
theorem relativeInterior_affine_image (A : E →ᵃ[ℝ] F) (C : Set E)
    (hC : Convex ℝ C) (hne : C.Nonempty) :
    relativeInterior (A '' C) = A '' relativeInterior C := by
  apply subset_antisymm _ (image_relativeInterior_subset A C hC)
  intro y hy
  obtain ⟨a, ha⟩ := relativeInterior_nonempty C hC hne
  have haC : a ∈ C := intrinsicInterior_subset ha
  have hyC : y ∈ A '' C := intrinsicInterior_subset hy
  obtain ⟨s, hs, b, hb, heq⟩ :=
    (mem_relativeInterior_iff_extendible _ (hC.affine_image A) y hyC).mp hy
      (A a) (mem_image_of_mem A haC)
  have hsp : 0 < 1+s := by linarith
  let t : ℝ := 1/(1+s)
  have ht0 : 0 ≤ t := (div_pos zero_lt_one hsp).le
  have ht1 : t < 1 := (div_lt_one hsp).mpr (by linarith)
  refine ⟨(1-t) • a + t • b,
    relativeInterior_halfOpenSegment C hC a b ha (subset_closure hb) t ht0 ht1, ?_⟩
  have hmap := A.apply_lineMap a b t
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at hmap
  rw [hmap, heq]
  dsimp [t]
  have hc : 1/(1+s) + 1/(1+s)*s = (1 : ℝ) := by field_simp
  simp only [smul_add, smul_sub, smul_smul]
  have hd : 1 - 1/(1+s) = 1/(1+s)*s := by field_simp; ring
  rw [hd]
  calc
    _ = (1/(1+s) + 1/(1+s)*s) • y := by module
    _ = y := by rw [hc, one_smul]

/-- The extension test transfers through an affine preimage in both directions. -/
theorem relativeInterior_affine_preimage (A : E →ᵃ[ℝ] F) (D : Set F)
    (hD : Convex ℝ D) (hne : (range A ∩ relativeInterior D).Nonempty) :
    relativeInterior (A ⁻¹' D) = A ⁻¹' relativeInterior D := by
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hne
  have haD : A a ∈ D := intrinsicInterior_subset ha
  have hconv : Convex ℝ (A ⁻¹' D) := hD.affine_preimage A
  apply subset_antisymm
  · intro x hx
    have hxC : x ∈ A ⁻¹' D := intrinsicInterior_subset hx
    have hxD : A x ∈ D := hxC
    obtain ⟨s, hs, hz⟩ :=
      (mem_relativeInterior_iff_extendible _ hconv x hxD).mp hx a haD
    have hzD : A x + s • (A x - A a) ∈ D := by
      rw [← map_extension]; exact hz
    exact hD.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      ha (subset_intrinsicClosure hzD) (mem_openSegment_extension (A x) (A a) hs)
  · intro x hx
    have hxD : A x ∈ D := intrinsicInterior_subset hx
    apply (mem_relativeInterior_iff_extendible _ hconv x hxD).mpr
    intro y hy
    obtain ⟨s, hs, hz⟩ :=
      (mem_relativeInterior_iff_extendible D hD (A x) hxD).mp hx (A y) hy
    exact ⟨s, hs, by change A (x + s • (x-y)) ∈ D; rwa [map_extension]⟩

/-- Interior in the product affine hull is the product of the two interiors. -/
theorem relativeInterior_product (C : Set E) (D : Set F)
    (_hC : Convex ℝ C) (_hneC : C.Nonempty) (_hD : Convex ℝ D) (_hneD : D.Nonempty) :
    relativeInterior (C ×ˢ D) = relativeInterior C ×ˢ relativeInterior D := by
  exact intrinsicInterior_prod_eq C D
end TwoSpaces

section Sum
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E]

/-- Addition is an affine map on the product, so its image gives the sum identity. -/
theorem relativeInterior_minkowski_sum (C D : Set E)
    (hC : Convex ℝ C) (hneC : C.Nonempty) (hD : Convex ℝ D) (hneD : D.Nonempty) :
    relativeInterior (C + D) = relativeInterior C + relativeInterior D := by
  let A : E × E →ᵃ[ℝ] E :=
    (LinearMap.fst ℝ E E + LinearMap.snd ℝ E E).toAffineMap
  have himage (S T : Set E) : A '' (S ×ˢ T) = S + T := by
    ext z
    constructor
    · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x,y), ⟨hx,hy⟩, rfl⟩
  rw [← himage C D, relativeInterior_affine_image A _ (hC.prod hD) (hneC.prod hneD),
    relativeInterior_product C D hC hneC hD hneD, himage]
end Sum

/-- The complete relative-interior calculus, reusing the earlier closure and intersection clauses. -/
theorem relativeInterior_calculus :
    Specs.closure_relativeInterior.{u} ∧ Specs.relativeInterior_closure.{u} ∧
    Specs.relativeInterior_iInter.{u,w} ∧ Specs.closure_iInter.{u,w} ∧
    Specs.relativeInterior_affine_image.{u,v} ∧ Specs.relativeInterior_affine_preimage.{u,v} ∧
    Specs.relativeInterior_product.{u,v} ∧ Specs.relativeInterior_minkowski_sum.{u} := by
  exact ⟨closure_relativeInterior, relativeInterior_closure,
    relativeInterior_iInter, closure_iInter, relativeInterior_affine_image,
    relativeInterior_affine_preimage, relativeInterior_product, relativeInterior_minkowski_sum⟩

end VariationalNotes.ConvexGeometry
