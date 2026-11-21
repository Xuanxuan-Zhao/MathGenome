import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorSegments
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeBoundarySupport
import Mathlib.Analysis.LocallyConvex.Separation

open Set
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry

/-- Relative boundary support, including nonconstancy on the set.

Translate the set into its affine hull's direction space. Its interior is
nonempty and excludes zero. Separate that interior from zero, and extend the
weak inequality to the set by density. The strict inequality on the interior
also gives nonconstancy and ensures that the functional is nonzero.
-/
theorem relativeBoundary_support {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : Set E) (hne : C.Nonempty) (_hclosed : IsClosed C)
    (hC : Convex ℝ C) (x : E) (hx : x ∈ C) (hxr : x ∉ relativeInterior C) :
    ∃ n : (affineSpan ℝ C).direction →ₗ[ℝ] ℝ,
      n ≠ 0 ∧
      (∀ (y : E) (hy : y ∈ C),
        n ⟨y - x, AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hx)⟩ ≤ 0) ∧
      ∃ (y : E) (hy : y ∈ C),
        n ⟨y - x, AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hx)⟩ < 0 := by
  let H := affineSpan ℝ C
  let xH : H := ⟨x, subset_affineSpan ℝ C hx⟩
  let : Nonempty H := ⟨xH⟩
  let A : H.direction →ᵃ[ℝ] E :=
    H.subtype.comp (AffineEquiv.vaddConst ℝ xH).toAffineMap
  let D : Set H.direction := A ⁻¹' C
  have hA : ⇑A = Subtype.val ∘ Homeomorph.vaddConst xH := rfl
  have hri : relativeInterior C = A '' interior D := by
    change intrinsicInterior ℝ C = _
    rw [intrinsicInterior, ← image_interior_preimage_comp
      (Homeomorph.vaddConst xH) (Homeomorph.vaddConst xH).isHomeomorph]
    rfl
  have hD : Convex ℝ D := hC.affine_preimage A
  have hDi : (interior D).Nonempty := by
    have := relativeInterior_nonempty C hC hne
    rwa [hri, image_nonempty] at this
  have hzero : (0 : H.direction) ∉ interior D := by
    intro hz
    apply hxr
    rw [hri]
    exact ⟨0, hz, by simp [A, xH]⟩
  obtain ⟨f, r, hf, hr⟩ := geometric_hahn_banach_open hD.interior isOpen_interior
    (convex_singleton (0 : H.direction)) (disjoint_singleton_right.mpr hzero)
  have hr0 : r ≤ 0 := by simpa using hr 0 (mem_singleton 0)
  have hweak : ∀ v ∈ D, f v ≤ 0 := by
    intro v hv
    have hcl : v ∈ closure (interior D) := by
      rw [hD.closure_interior_eq_closure_of_nonempty_interior hDi]
      exact subset_closure hv
    have hle : closure (interior D) ⊆ {v | f v ≤ r} :=
      closure_minimal (fun v hv => (hf v hv).le)
        (isClosed_Iic.preimage f.continuous)
    exact (hle hcl).trans hr0
  obtain ⟨v, hv⟩ := hDi
  have hstrict : f v < 0 := (hf v hv).trans_le hr0
  refine ⟨f.toLinearMap, ?_, ?_, ?_⟩
  · intro hf0
    have : f v = 0 := congrArg (fun n : H.direction →ₗ[ℝ] ℝ => n v) hf0
    linarith
  · intro y hy
    let w : H.direction := ⟨y - x, AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hx)⟩
    have hAw : A w = y := by simp [A, w, xH]
    exact hweak w (by change A w ∈ C; rwa [hAw])
  · have hvC : A v ∈ C := (interior_subset hv : v ∈ D)
    refine ⟨A v, hvC, ?_⟩
    have hw : (⟨A v - x, AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ C hvC)
        (subset_affineSpan ℝ C hx)⟩ : H.direction) = v := by
      apply Subtype.ext
      simp [A, xH]
    change f _ < 0
    rw [hw]
    exact hstrict

end VariationalNotes.ConvexGeometry
