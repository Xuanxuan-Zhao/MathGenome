import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations

open Set
open scoped Pointwise
noncomputable section
universe u v
namespace VariationalNotes.ConvexGeometry

/-- An affine set, using native affine subspaces (which allow the empty set). -/
def IsAffine {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Prop := Specs.IsAffine s

/-- The smallest affine set containing the generators. -/
def affineHull {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Set E := Specs.affineHull s

/-- The manuscript convention: zero, addition, and nonnegative real scaling. -/
def IsCone {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Prop := Specs.IsCone s

/-- The zero-containing conic hull, i.e. the span over nonnegative scalars. -/
def conicHull {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Set E := Specs.conicHull s

/-- A convex extreme subset; for convex C this is a face in the manuscript. -/
def IsFace {E : Type u} [AddCommGroup E] [Module ℝ E] (C F : Set E) : Prop := Specs.IsFace C F

/-- The native extreme-point predicate; its singleton-face bridge is proved below. -/
def IsExtremePoint {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) (x : E) : Prop := Specs.IsExtremePoint C x

/-- Interior in the affine span, mapped back to the ambient space. -/
def relativeInterior {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (s : Set E) : Set E := Specs.relativeInterior s

theorem affineHull_description :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), x ∈ affineHull C ↔
  ∃ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C ∧
    (∑ y ∈ s, w y) = 1 ∧ (∑ y ∈ s, w y • y) = x := by
  intro E _ _ C x
  classical
  change x ∈ affineSpan ℝ C ↔ _
  constructor
  · intro hx
    have hx' : x ∈ affineSpan ℝ (id '' C) := by simpa using hx
    obtain ⟨t, w, ht, hw, hxw⟩ := eq_affineCombination_of_mem_affineSpan_image hx'
    refine ⟨t, w, ht, hw, ?_⟩
    simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw, id_eq] using hxw.symm
  · rintro ⟨t, w, ht, hw, rfl⟩
    have hmem := affineCombination_mem_affineSpan_image hw
      (fun i hi hnot => False.elim (hnot (ht hi))) (id : E → E)
    simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw, id_eq, Set.image_id, Set.image_id']
      using hmem

theorem convexHull_description :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), x ∈ convexHull ℝ C ↔
  ∃ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C ∧
    (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y) = 1 ∧ (∑ y ∈ s, w y • y) = x := by
  intro E _ _ C x
  classical
  rw [convexHull_eq_union_convexHull_finite_subsets]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨w, hw0, hw1, hxw⟩ := Finset.mem_convexHull'.mp hx
    exact ⟨t, w, ht, hw0, hw1, hxw⟩
  · rintro ⟨t, w, ht, hw0, hw1, hxw⟩
    exact ⟨t, ht, Finset.mem_convexHull'.mpr ⟨w, hw0, hw1, hxw⟩⟩

theorem conicHull_description :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), x ∈ conicHull C ↔
  ∃ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C ∧
    (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y • y) = x := by
  intro E _ _ C x
  classical
  change x ∈ PointedCone.hull ℝ C ↔ _
  constructor
  · intro hx
    obtain ⟨c, hc, hc0, hcx⟩ := PointedCone.mem_hull_set.mp hx
    exact ⟨c.support, c, hc, fun y _ => hc0 y, hcx⟩
  · rintro ⟨t, w, ht, hw0, rfl⟩
    exact Submodule.sum_mem _ (fun y hy =>
      PointedCone.smul_mem _ (hw0 y hy) (PointedCone.subset_hull (ht hy)))

theorem isAffine_iff_combinations :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, IsAffine C ↔
  ∀ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C →
    (∑ y ∈ s, w y) = 1 → (∑ y ∈ s, w y • y) ∈ C := by
  intro E _ _ C
  constructor
  · rintro ⟨A, rfl⟩ t w ht hw
    have hx : (∑ y ∈ t, w y • y) ∈ affineHull (A : Set E) :=
      (affineHull_description _ _).mpr ⟨t, w, ht, hw, rfl⟩
    exact (affineSpan_le.mpr (Subset.rfl : (A : Set E) ⊆ A)) hx
  · intro h
    refine ⟨affineSpan ℝ C, Set.Subset.antisymm ?_ (subset_affineSpan ℝ C)⟩
    intro x hx
    obtain ⟨t, w, ht, hw, hxw⟩ := (affineHull_description C x).mp hx
    exact hxw ▸ h t w ht hw

theorem convex_iff_combinations :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, Convex ℝ C ↔
  ∀ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C →
    (∀ y ∈ s, 0 ≤ w y) → (∑ y ∈ s, w y) = 1 → (∑ y ∈ s, w y • y) ∈ C := by
  intro E _ _ C
  constructor
  · intro h t w ht hw0 hw1
    exact h.sum_mem hw0 hw1 (fun y hy => ht hy)
  · intro h
    apply convex_iff_sum_mem.mpr
    intro t w hw0 hw1 ht
    exact h t w ht hw0 hw1

theorem isCone_iff_pointedCone :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, IsCone C ↔
  ∃ K : PointedCone ℝ E, (K : Set E) = C := by
  intro E _ _ C
  constructor
  · rintro ⟨h0, hadd, hsmul⟩
    refine ⟨{ carrier := C
              zero_mem' := h0
              add_mem' := fun hx hy => hadd hx hy
              smul_mem' := fun r x hx => hsmul r.val r.property hx }, rfl⟩
  · rintro ⟨K, rfl⟩
    exact ⟨K.zero_mem, fun _ _ hx hy => K.add_mem hx hy,
      fun r hr _ hx => PointedCone.smul_mem K hr hx⟩

theorem hull_properties :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E,
  (IsAffine (affineHull C) ∧ C ⊆ affineHull C ∧
    ∀ A, IsAffine A → C ⊆ A → affineHull C ⊆ A) ∧
  (Convex ℝ (convexHull ℝ C) ∧ C ⊆ convexHull ℝ C ∧
    ∀ A, Convex ℝ A → C ⊆ A → convexHull ℝ C ⊆ A) ∧
  (IsCone (conicHull C) ∧ C ⊆ conicHull C ∧
    ∀ A, IsCone A → C ⊆ A → conicHull C ⊆ A) := by
  intro E _ _ C
  refine ⟨⟨⟨affineSpan ℝ C, rfl⟩, subset_affineSpan ℝ C, ?_⟩,
    ⟨convex_convexHull ℝ C, subset_convexHull ℝ C, ?_⟩,
    ⟨(isCone_iff_pointedCone _).mpr ⟨PointedCone.hull ℝ C, rfl⟩,
      PointedCone.subset_hull, ?_⟩⟩
  · rintro A ⟨H, rfl⟩ hCH
    exact affineSpan_le.mpr hCH
  · intro A hA hCA
    exact convexHull_min hCA hA
  · intro A hA hCA
    obtain ⟨K, rfl⟩ := (isCone_iff_pointedCone A).mp hA
    exact Submodule.span_le.mpr hCA

theorem empty_hulls :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], affineHull (∅ : Set E) = ∅ ∧ convexHull ℝ (∅ : Set E) = ∅ ∧
  conicHull (∅ : Set E) = {0} := by
  intro E _ _
  change (affineSpan ℝ (∅ : Set E) : Set E) = ∅ ∧ _ ∧
    (Submodule.span (Nonneg ℝ) (∅ : Set E) : Set E) = {0}
  simp

theorem face_iff_segment :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C F : Set E, IsFace C F ↔
  F ⊆ C ∧ Convex ℝ F ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 < t → t < 1 →
      (1-t) • x + t • y ∈ F → x ∈ F ∧ y ∈ F := by
  intro E _ _ C F
  constructor
  · rintro ⟨hconv, hext⟩
    refine ⟨hext.subset, hconv, ?_⟩
    intro x hx y hy t ht0 ht1 hz
    have hseg : (1-t) • x + t • y ∈ openSegment ℝ x y :=
      ⟨1-t, t, sub_pos.mpr ht1, ht0, sub_add_cancel 1 t, rfl⟩
    exact ⟨hext.left_mem_of_mem_openSegment hx hy hz hseg,
      hext.right_mem_of_mem_openSegment hx hy hz hseg⟩
  · rintro ⟨hFC, hconv, hseg⟩
    refine ⟨hconv, hFC, ?_⟩
    rintro x hx y hy z hz ⟨a, b, ha, hb, hab, rfl⟩
    have ha' : a = 1-b := by linarith
    exact (hseg x hx y hy b hb (by linarith) (by simpa only [← ha'] using hz)).1

theorem extremePoint_iff_singleton_face :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), IsExtremePoint C x ↔ IsFace C {x} := by
  intro E _ _ C x
  change x ∈ C.extremePoints ℝ ↔ Convex ℝ ({x} : Set E) ∧ IsExtreme ℝ C {x}
  rw [isExtreme_singleton]
  exact ⟨fun h => ⟨convex_singleton x, h⟩, And.right⟩

theorem convex_intersections :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ S : Set (Set E), (∀ C ∈ S, Convex ℝ C) → Convex ℝ (⋂₀ S) := by
  intro E _ _ S hS
  exact convex_sInter hS

theorem convex_affine_image :
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (f : E →ᵃ[ℝ] G) (C : Set E),
    Convex ℝ C → Convex ℝ (f '' C) := by
  intro E G _ _ _ _ f C hC
  exact Convex.affine_image f hC

theorem convex_affine_preimage :
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (f : E →ᵃ[ℝ] G) (C : Set G),
    Convex ℝ C → Convex ℝ (f ⁻¹' C) := by
  intro E G _ _ _ _ f C hC
  exact Convex.affine_preimage f hC

theorem convex_product :
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (C : Set E) (D : Set G),
    Convex ℝ C → Convex ℝ D → Convex ℝ (C ×ˢ D) := by
  intro E G _ _ _ _ C D hC hD
  exact hC.prod hD

theorem convex_minkowski_sum :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C D : Set E,
  Convex ℝ C → Convex ℝ D → Convex ℝ (C + D) := by
  intro E _ _ C D hC hD
  exact hC.add hD

theorem cone_linear_image :
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (f : E →ₗ[ℝ] G) (C : Set E),
    IsCone C → IsCone (f '' C) := by
  intro E G _ _ _ _ f C hC
  obtain ⟨K, rfl⟩ := (isCone_iff_pointedCone C).mp hC
  exact (isCone_iff_pointedCone _).mpr ⟨PointedCone.map f K, rfl⟩

theorem cone_convex :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, IsCone C → Convex ℝ C := by
  intro E _ _ C hC
  obtain ⟨K, rfl⟩ := (isCone_iff_pointedCone C).mp hC
  exact PointedCone.convex K

theorem relativeInterior_eq :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (C : Set E), relativeInterior C =
    (Subtype.val : affineSpan ℝ C → E) ''
      interior ((Subtype.val : affineSpan ℝ C → E) ⁻¹' C) := by
  intro E _ _ _ C
  rfl

theorem relativeInterior_empty :
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  relativeInterior (∅ : Set E) = ∅ := by
  intro E _ _ _
  exact intrinsicInterior_empty

/-- Arbitrary Cartesian products, including an empty index set. -/
theorem convex_cartesian_products :
  ∀ {ι : Type u} {E : ι → Type v} [∀ i, AddCommGroup (E i)]
    [∀ i, Module ℝ (E i)], ∀ (I : Set ι) (C : ∀ i, Set (E i)),
    (∀ i ∈ I, Convex ℝ (C i)) → Convex ℝ (I.pi C) := by
  intro ι E _ _ I C hC
  exact convex_pi (fun {i} hi => hC i hi)

end VariationalNotes.ConvexGeometry
