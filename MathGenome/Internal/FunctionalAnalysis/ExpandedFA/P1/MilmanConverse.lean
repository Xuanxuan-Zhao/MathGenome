import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.MilmanConverse
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ExtremeAffineLifting
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology

/-!
Milman's converse and extreme-point lifting (`fa2:p1:milman-converse`).
The proof of the converse uses finitely many closed half-space slices of the
compact hull. Their convex hull is compact, and its extreme points belong to
their union. Lifting reuses the accepted theorem on compact fibers.
-/

universe u v

namespace ExpandedFA.P1

open Set

section CompactHulls

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The join of two compact sets is the continuous image of a compact product. -/
theorem isCompact_convexJoin {S T : Set E} (hS : IsCompact S) (hT : IsCompact T) :
    IsCompact (convexJoin ℝ S T) := by
  have heq : convexJoin ℝ S T =
      (fun p : ℝ × (E × E) => (1 - p.1) • p.2.1 + p.1 • p.2.2) ''
        (Icc (0 : ℝ) 1 ×ˢ (S ×ˢ T)) := by
    ext z
    simp only [mem_convexJoin, mem_image, mem_prod, mem_Icc]
    constructor
    · rintro ⟨x, hx, y, hy, hz⟩
      obtain ⟨t, ht, rfl⟩ := (segment_eq_image ℝ x y) ▸ hz
      exact ⟨(t, x, y), ⟨ht, hx, hy⟩, rfl⟩
    · rintro ⟨⟨t, x, y⟩, ⟨ht, hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, (segment_eq_image ℝ x y) ▸ ⟨t, ht, rfl⟩⟩
  rw [heq]
  exact (isCompact_Icc.prod (hS.prod hT)).image (by fun_prop)

/-- The hull of a finite union of compact convex sets is compact. -/
theorem isCompact_convexHull_finite_union {ι : Type*} (s : Finset ι) (C : ι → Set E)
    (hcompact : ∀ i ∈ s, IsCompact (C i)) (hconvex : ∀ i ∈ s, Convex ℝ (C i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ s, C i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hCi := hcompact i (Finset.mem_insert_self i s)
    have hVi := hconvex i (Finset.mem_insert_self i s)
    have hCs := ih (fun j hj => hcompact j (Finset.mem_insert_of_mem hj))
      (fun j hj => hconvex j (Finset.mem_insert_of_mem hj))
    rw [Finset.set_biUnion_insert]
    obtain h₁ | h₁ := (C i).eq_empty_or_nonempty
    · simpa [h₁] using hCs
    obtain h₂ | h₂ := (⋃ j ∈ s, C j).eq_empty_or_nonempty
    · simpa [h₂, hVi.convexHull_eq] using hCi
    rw [convexHull_union h₁ h₂, hVi.convexHull_eq]
    exact isCompact_convexJoin hCi hCs

end CompactHulls

/-- Milman's converse, without a nonemptiness or metrizability assumption. -/
theorem real_milman_converse : MilmanConverseSpec.realConverseType.{u} := by
  intro E _ _ _ _ _ _ _ K A heq hK x hx
  classical
  by_contra hxA
  have hconvK : Convex ℝ K := by
    rw [heq]
    exact (convex_convexHull ℝ A).closure
  have hAK : closure A ⊆ K := by
    rw [heq]
    exact closure_mono (subset_convexHull ℝ A)
  have hAc : IsCompact (closure A) := hK.of_isClosed_subset isClosed_closure hAK
  have hsep : ∀ y : closure A, ∃ f : E →L[ℝ] ℝ, f x < f y := by
    intro y
    exact geometric_hahn_banach_point_point (fun h => hxA (h ▸ y.property))
  choose f hf using hsep
  let c (y : closure A) : ℝ := (f y x + f y y) / 2
  have hcx (y : closure A) : f y x < c y := by dsimp [c]; linarith [hf y]
  have hcy (y : closure A) : c y < f y y := by dsimp [c]; linarith [hf y]
  let U (y : closure A) : Set E := {z | c y < f y z}
  let C (y : closure A) : Set E := K ∩ {z | c y ≤ f y z}
  obtain ⟨s, hs⟩ := hAc.elim_finite_subcover U
    (fun y => isOpen_lt continuous_const (f y).continuous)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hcy ⟨y, hy⟩⟩)
  have hCc (y : closure A) : IsCompact (C y) :=
    hK.inter_right (isClosed_le continuous_const (f y).continuous)
  have hCv (y : closure A) : Convex ℝ (C y) :=
    hconvK.inter ((convex_Ici (c y)).linear_preimage (f y).toLinearMap)
  have hCcompact : IsCompact (convexHull ℝ (⋃ y ∈ s, C y)) :=
    isCompact_convexHull_finite_union s C (fun y _ => hCc y) (fun y _ => hCv y)
  have hAcover : A ⊆ ⋃ y ∈ s, C y := by
    intro a ha
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs (subset_closure ha))
    obtain ⟨hys, hay⟩ := mem_iUnion.mp hy
    change c y < f y a at hay
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hys, hAK (subset_closure ha), hay.le⟩⟩
  have hKhull : K = convexHull ℝ (⋃ y ∈ s, C y) := by
    apply Subset.antisymm
    · rw [heq]
      exact closure_minimal
        (convexHull_mono hAcover) hCcompact.isClosed
    · exact convexHull_min (iUnion_subset fun y => iUnion_subset fun _ => inter_subset_left)
        hconvK
  have hx' : x ∈ (convexHull ℝ (⋃ y ∈ s, C y)).extremePoints ℝ := by
    rw [← hKhull, ← extremePoints_eq_native]
    exact hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (extremePoints_convexHull_subset hx')
  obtain ⟨_hys, hxy⟩ := mem_iUnion.mp hy
  exact (hcx y).not_ge hxy.2

/-- The complex version uses the same real hull and unchanged topology. -/
theorem complex_milman_converse : MilmanConverseSpec.complexConverseType.{u} := by
  intro E _ _ _ _ _ _ _ K A heq hK
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact real_milman_converse K A heq hK

/-- The second clause is the accepted lifting theorem for maps on the subsets. -/
theorem real_milman_extreme_affine_lifting : MilmanConverseSpec.realLiftingType.{u, v} :=
  real_extreme_affine_lifting

/-- Complex continuous affine surjections lift real extreme points as well. -/
theorem complex_milman_extreme_affine_lifting :
    MilmanConverseSpec.complexLiftingType.{u, v} :=
  complex_extreme_affine_lifting

end ExpandedFA.P1
