import MathGenome.Internal.ExtremalOptimization.P205.Matroids.Models
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.UnionCopies

/-! The two genuine labelled-copy matroids and their rank/assignment interfaces. -/
namespace P205.Matroids
open Set
open scoped BigOperators
noncomputable section
universe u

def sliceMatroid : Specs.P205.Matroids.sliceMatroidType.{u} :=
  @Specs.P205.Matroids.sliceMatroidValue.{u}

def labelMatroid : Specs.P205.Matroids.labelMatroidType.{u} :=
  @Specs.P205.Matroids.labelMatroidValue.{u}

theorem slice_ground : Specs.P205.Matroids.SliceGround := by
  intro α k F S
  ext p
  simp [Specs.P205.Matroids.sliceMatroidValue, Matroid.sum'_ground_eq]
  exact ⟨p.2, (p.1 : α), p.1.property, rfl⟩

theorem label_ground : Specs.P205.Matroids.LabelGround := by
  intro α S k
  ext p
  simp [Specs.P205.Matroids.labelMatroidValue, p.1.property]

theorem copy_finite : Specs.P205.Matroids.CopyFinite := by
  intro α k F S hS
  let := (F.ground_finite.subset hS).fintype
  constructor
  · exact ⟨(slice_ground F S).symm ▸ Set.finite_univ⟩
  · exact ⟨(label_ground S k).symm ▸ Set.finite_univ⟩

private theorem swap_slice {α : Type u} {S : Set α} {k : ℕ}
    (J : Set (CopyGround S k)) (i : Fin k) :
    Prod.mk i ⁻¹' (Prod.swap '' J) = copyFiber J i := by
  ext e
  simp [copyFiber, Prod.swap_prod_mk]

theorem slice_indep : Specs.P205.Matroids.SliceIndep := by
  intro α k F S J
  simp only [Specs.P205.Matroids.sliceMatroidValue, Matroid.comap_indep_iff,
    Matroid.sum'_indep_iff, swap_slice, Matroid.restrictSubtype_indep_iff]
  exact and_iff_left Prod.swap_injective.injOn

theorem label_indep : Specs.P205.Matroids.LabelIndep := by
  intro α S k J
  simp only [Specs.P205.Matroids.labelMatroidValue, Matroid.comap_indep_iff,
    Matroid.freeOn_indep_iff]
  exact and_iff_right (by rintro e ⟨p, hp, rfl⟩; exact p.1.property)

theorem label_rank : Specs.P205.Matroids.LabelRank := by
  intro α S k Y
  unfold Specs.P205.Matroids.rankValue Specs.P205.Matroids.labelMatroidValue
  rw [Matroid.eRk_comap, Matroid.eRk_freeOn]
  · rfl
  · rintro e ⟨p, hp, rfl⟩
    exact p.1.property

/-- The slices partition a finite set of copies; the subtype coercion preserves size. -/
theorem copy_ncard_eq_sum {α : Type u} {S : Set α} {k : ℕ}
    (hS : S.Finite) (J : Set (CopyGround S k)) :
    J.ncard = ∑ i, (copySlice J i).ncard := by
  classical
  let := hS.fintype
  have heq : J = ⋃ i, (fun e : S => (e, i)) '' copyFiber J i := by
    ext p
    constructor
    · intro hp
      exact mem_iUnion.mpr ⟨p.2, ⟨p.1, hp, rfl⟩⟩
    · rintro hp
      obtain ⟨i, e, he, rfl⟩ := mem_iUnion.mp hp
      exact he
  calc
    J.ncard = (⋃ i, (fun e : S => (e, i)) '' copyFiber J i).ncard := congrArg Set.ncard heq
    _ = ∑ i, (copySlice J i).ncard := by
      rw [Set.ncard_iUnion_of_finite, finsum_eq_sum_of_fintype]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Set.ncard_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h)]
        exact (Subtype.val_injective.injOn.ncard_image (s := copyFiber J i)).symm
      · intro i
        exact (Set.toFinite _).image _
      · intro i j hij
        apply Set.disjoint_left.mpr
        rintro p ⟨e, he, rfl⟩ ⟨f, hf, heq⟩
        exact hij (congrArg Prod.snd heq).symm

/-- A basis in the direct sum has, in each original matroid, a basis of its slice. -/
theorem copy_slice_basis {α : Type u} {k : ℕ} (F : Family α k) (S : Set α)
    (hS : S ⊆ F.ground) {I U : Set (CopyGround S k)}
    (hI : (sliceMatroid F S).IsBasis I U) (i : Fin k) :
    (F.matroid i).IsBasis (copySlice I i) (copySlice U i) := by
  have h := (Matroid.comap_isBasis_iff.mp hI).1
  have hi := (Matroid.sum'_isBasis_iff.mp h) i
  rw [swap_slice, swap_slice, Matroid.restrictSubtype_isBasis_iff] at hi
  exact hi.isBasis (by
    rintro e ⟨a, ha, rfl⟩
    rw [F.ground_eq i]
    exact hS a.property)

theorem slice_rank : Specs.P205.Matroids.SliceRank := by
  intro α k F S hS U
  let : (sliceMatroid F S).Finite := (copy_finite F S hS).1
  have hg : (sliceMatroid F S).E = univ := slice_ground F S
  obtain ⟨I, hI⟩ := (sliceMatroid F S).exists_isBasis U (by rw [hg]; exact subset_univ _)
  change Specs.P205.Matroids.rankValue (sliceMatroid F S) U = _
  rw [← (basis_rank (sliceMatroid F S) I U (by rw [hg]; exact subset_univ _)).mp hI |>.2.2]
  rw [copy_ncard_eq_sum (F.ground_finite.subset hS)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (basis_rank (F.matroid i) _ _ (by
    rintro e ⟨a, ha, rfl⟩
    rw [F.ground_eq i]
    exact hS a.property)).mp (copy_slice_basis F S hS hI i) |>.2.2

/-- All represented elements lie in the underlying set, even for an empty index type. -/
theorem copy_labels_subset {α : Type u} {S : Set α} {k : ℕ}
    (J : Set (CopyGround S k)) : copyLabels J ⊆ S := by
  rintro e ⟨p, hp, rfl⟩
  exact p.1.property

theorem copy_labels_eq_union {α : Type u} {S : Set α} {k : ℕ}
    (J : Set (CopyGround S k)) : copyLabels J = ⋃ i, copySlice J i := by
  ext e
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact mem_iUnion.mpr ⟨p.2, ⟨p.1, hp, rfl⟩⟩
  · intro he
    obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.mp he
    exact ⟨(a, i), ha, rfl⟩

/-- Injectivity of labels is exactly disjointness of the original-element slices. -/
theorem copy_labels_inj_iff {α : Type u} {S : Set α} {k : ℕ}
    (J : Set (CopyGround S k)) :
    J.InjOn (fun p => (p.1 : α)) ↔
      Pairwise (fun i j => Disjoint (copySlice J i) (copySlice J j)) := by
  constructor
  · intro hinj i j hij
    apply disjoint_left.mpr
    rintro e ⟨a, ha, hae⟩ ⟨b, hb, hbe⟩
    have hp : (a, i) = (b, j) := hinj ha hb (hae.trans hbe.symm)
    exact hij (congrArg Prod.snd hp)
  · intro hd p hp q hq he
    have hfirst : p.1 = q.1 := Subtype.val_injective he
    have hsecond : p.2 = q.2 := by
      by_contra hne
      exact disjoint_left.mp (hd hne)
        (show (p.1 : α) ∈ copySlice J p.2 from ⟨p.1, hp, rfl⟩)
        (show (p.1 : α) ∈ copySlice J q.2 from ⟨q.1, hq, he.symm⟩)
    exact Prod.ext hfirst hsecond

theorem common_assignment : Specs.P205.Matroids.CommonAssignment := by
  intro α k F S J
  rw [slice_indep, label_indep, copy_labels_inj_iff]
  exact ⟨fun h => ⟨copy_labels_subset J, h.1, h.2, copy_labels_eq_union J⟩,
    fun h => ⟨h.2.1, h.2.2.1⟩⟩

theorem common_cardinality : Specs.P205.Matroids.CommonCardinality := by
  intro α k F S J _ hJ
  exact (label_indep S k J).mp hJ |>.ncard_image

theorem copies_inverse : Specs.P205.Matroids.CopiesInverse := by
  intro α S k J
  ext p
  constructor
  · rintro ⟨a, ha, he⟩
    have h : a = p.1 := Subtype.val_injective he
    simpa [copyFiber, h] using ha
  · intro hp
    exact ⟨p.1, hp, rfl⟩

/-- Recover the specified part; the subset condition prevents losses at the subtype boundary. -/
theorem labelled_parts_slice {α : Type u} {S : Set α} {k : ℕ}
    (parts : Fin k → Set α) (hparts : ∀ i, parts i ⊆ S) (i : Fin k) :
    copySlice (labelledParts S parts) i = parts i := by
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro he
    exact ⟨⟨e, hparts i he⟩, he, rfl⟩

theorem assignment_copies : Specs.P205.Matroids.AssignmentCopies := by
  intro α k F S I parts h
  have hparts : ∀ i, parts i ⊆ S := by
    intro i e he
    apply h.1
    rw [h.2.2.2]
    exact mem_iUnion.mpr ⟨i, he⟩
  have hslices := labelled_parts_slice parts hparts
  have hlabels : copyLabels (labelledParts S parts) = I := by
    rw [copy_labels_eq_union, h.2.2.2]
    congr 1
    funext i
    exact hslices i
  have ha : DisjointAssignment F S (copyLabels (labelledParts S parts))
      (copySlice (labelledParts S parts)) := by
    have heq : copySlice (labelledParts S parts) = parts := funext hslices
    rw [hlabels, heq]
    exact h
  have hcommon := (common_assignment F S (labelledParts S parts)).mpr ha
  refine ⟨hcommon.1, hcommon.2, hlabels, hslices, ?_⟩
  rw [← hlabels]
  exact (common_cardinality F S (labelledParts S parts) hcommon.1 hcommon.2).symm

end
end P205.Matroids
