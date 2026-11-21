import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.Tactic.Linarith

/-!
# Extreme points and nonempty faces

Definition `fa2:p1:c24:faces` (paper.tex:4935–4943) of the manuscript. These definitions use real
convexity, so a complex ambient space is treated by restricting its scalars to
ℝ; no topology is changed. The definitions need only a real module, and the
compact-face definition uses its supplied topology. They therefore apply, in
particular, to the Hausdorff locally convex spaces of Chapter 24, without any
normability or completeness hypothesis.

Mathlib's `IsExtreme` is the endpoint property, allowing empty sets and not
including convexity. `isFace_iff_native` records both extra requirements.
-/

universe u

namespace ExpandedFA.P1

/-- Extreme points as defined by proper real convex combinations in the paper. -/
def extremePoints : C24FacesSpec.extremePointsType.{u} :=
  @C24FacesSpec.extremePoints

/-- A nonempty convex subset satisfying the endpoint property. -/
def IsFace : C24FacesSpec.isFaceType.{u} :=
  @C24FacesSpec.IsFace

/-- A face compact in the given ambient topology. -/
def IsCompactFace : C24FacesSpec.isCompactFaceType.{u} :=
  @C24FacesSpec.IsCompactFace

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The native two-positive-coefficient description agrees with `0 < t < 1`. -/
theorem mem_openSegment_iff_real_combination {x y z : E} :
    x ∈ openSegment ℝ y z ↔
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = t • y + (1 - t) • z := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, hx⟩
    refine ⟨a, ha, by linarith, ?_⟩
    have hb' : b = 1 - a := by linarith
    simpa only [hb'] using hx.symm
  · rintro ⟨t, ht0, ht1, hx⟩
    exact ⟨t, 1 - t, ht0, sub_pos.mpr ht1, add_sub_cancel _ _, hx.symm⟩

/-- Identification with Mathlib's real extreme-point set. -/
theorem extremePoints_eq_native (K : Set E) : extremePoints K = K.extremePoints ℝ := by
  ext x
  change (x ∈ K ∧ _) ↔ _
  rw [mem_extremePoints]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro h y hy z hz hx
    obtain ⟨t, ht0, ht1, heq⟩ := mem_openSegment_iff_real_combination.mp hx
    exact h y hy z hz t ht0 ht1 heq
  · intro h y hy z hz t ht0 ht1 heq
    exact h y hy z hz (mem_openSegment_iff_real_combination.mpr ⟨t, ht0, ht1, heq⟩)

/-- Mathlib's extreme subsets become faces upon imposing nonemptiness and convexity. -/
theorem isFace_iff_native (K F : Set E) :
    IsFace K F ↔ F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ K F := by
  constructor
  · rintro ⟨hne, hconv, hsub, hend⟩
    refine ⟨hne, hconv, hsub, ?_⟩
    intro y hy z hz x hx hseg
    obtain ⟨t, ht0, ht1, heq⟩ := mem_openSegment_iff_real_combination.mp hseg
    exact (hend y hy z hz t ht0 ht1 (heq ▸ hx)).1
  · rintro ⟨hne, hconv, hext⟩
    refine ⟨hne, hconv, hext.subset, ?_⟩
    intro y hy z hz t ht0 ht1 hx
    have hseg : t • y + (1 - t) • z ∈ openSegment ℝ y z :=
      mem_openSegment_iff_real_combination.mpr ⟨t, ht0, ht1, rfl⟩
    exact ⟨hext.left_mem_of_mem_openSegment hy hz hx hseg,
      hext.right_mem_of_mem_openSegment hy hz hx hseg⟩

/-- Compactness uses the same topology on both sides of the identification. -/
theorem isCompactFace_iff_native [TopologicalSpace E] (K F : Set E) :
    IsCompactFace K F ↔ F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ K F ∧ IsCompact F := by
  change (IsFace K F ∧ IsCompact F) ↔ _
  rw [isFace_iff_native]
  exact and_assoc.trans (and_congr_right fun _ => and_assoc)

/-- The empty set is a native convex extreme subset, but is not a face here. -/
theorem empty_face_conventions (K : Set E) :
    IsExtreme ℝ K ∅ ∧ Convex ℝ (∅ : Set E) ∧ ¬ IsFace K ∅ := by
  refine ⟨⟨Set.empty_subset K, ?_⟩, convex_empty, ?_⟩
  · intro y hy z hz x hx
    exact False.elim hx
  · intro h
    exact Set.not_nonempty_empty h.1

/-- In particular, the empty set is not a compact face. -/
theorem not_isCompactFace_empty [TopologicalSpace E] (K : Set E) :
    ¬ IsCompactFace K ∅ := by
  intro h
  exact (empty_face_conventions K).2.2 h.1

end ExpandedFA.P1
