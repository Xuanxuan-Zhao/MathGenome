import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.FacetIncidence
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.SimplexTriangulation
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace D10Topology.Ch17

abbrev incidentTopCells : Specs.D10Topology.Ch17.FacetIncidence.incidentTopCellsType :=
  @Specs.D10Topology.Ch17.FacetIncidence.incidentTopCellsValue

/-- Every cell extends to an actual top-dimensional cell, by finiteness and purity. -/
theorem exists_topCell_superset {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {F : Finset (Euclidean m)} (hF : F ∈ T.complex.cells) :
    ∃ C ∈ topCells T, F ⊆ C := by
  classical
  let A := T.complex.cells.filter (F ⊆ ·)
  have hA : A.Nonempty := ⟨F, Finset.mem_filter.mpr ⟨hF, Finset.Subset.refl F⟩⟩
  obtain ⟨C, hC, hmax⟩ := A.exists_max_image Finset.card hA
  obtain ⟨hCcell, hFC⟩ := Finset.mem_filter.mp hC
  have hCM : C ∈ maximalCells T.complex := by
    apply Finset.mem_filter.mpr
    refine ⟨hCcell, ?_⟩
    intro D hD hCD
    exact Finset.eq_of_subset_of_card_le hCD
      (hmax D (Finset.mem_filter.mpr ⟨hD, hFC.trans hCD⟩))
  exact ⟨C, Finset.mem_filter.mpr ⟨hCcell, T.pure C hCM⟩, hFC⟩

theorem incidentTopCells_nonempty {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {F : Finset (Euclidean m)} (hF : F ∈ T.complex.cells) :
    (incidentTopCells T F).Nonempty := by
  obtain ⟨C, hC, hFC⟩ := exists_topCell_superset T hF
  exact ⟨C, Finset.mem_filter.mpr ⟨hC, hFC⟩⟩

theorem cellHull_subset_simplexHull {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {C : Finset (Euclidean m)} (hC : C ∈ T.complex.cells) :
    cellHull C ⊆ simplexHull S := by
  intro x hx
  have hcovers : complexSupport T.complex = simplexHull S := T.covers
  rw [← hcovers]
  exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hC, hx⟩⟩

/-- The top-dimensional cells are exactly the maximal cells. -/
theorem topCells_eq_maximalCells {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) : topCells T = maximalCells T.complex := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hCcell, hCcard⟩ := Finset.mem_filter.mp hC
    apply Finset.mem_filter.mpr
    refine ⟨hCcell, ?_⟩
    intro D hD hCD
    obtain ⟨E, hE, hDE⟩ := exists_topCell_superset T hD
    have hEcard := (Finset.mem_filter.mp hE).2
    apply Finset.eq_of_subset_of_card_le hCD
    calc D.card ≤ E.card := Finset.card_le_card hDE
         _ = C.card := hEcard.trans hCcard.symm
  · intro hC
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hC).1, T.pure C hC⟩

/-- All geometric cells are closed, including the empty cell. -/
theorem cellHull_isClosed {m : ℕ} (C : Finset (Euclidean m)) :
    IsClosed (cellHull C) := C.finite_toSet.isClosed_convexHull (𝕜 := ℝ)

/-- A ball avoiding all cells not containing its center. This uses geometric
closedness and finiteness, and makes no incidence assumption. -/
theorem exists_ball_avoiding_cells {m : ℕ} (K : GeometricComplex m) (p : Euclidean m) :
    ∃ r > 0, ∀ C ∈ K.cells, p ∉ cellHull C →
      Disjoint (Metric.ball p r) (cellHull C) := by
  classical
  let A := K.cells.filter (fun C => p ∉ cellHull C)
  have hopen : IsOpen (⋂ C ∈ A, (cellHull C)ᶜ) :=
    isOpen_biInter_finset fun C _ => (cellHull_isClosed C).isOpen_compl
  have hp : p ∈ ⋂ C ∈ A, (cellHull C)ᶜ := by
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro C hC
    exact (Finset.mem_filter.mp hC).2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen p hp
  refine ⟨r, hr, fun C hC hpC => Set.disjoint_left.mpr ?_⟩
  intro x hx hxC
  exact (Set.mem_iInter.mp (Set.mem_iInter.mp (hball hx) C)
    (Finset.mem_filter.mpr ⟨hC, hpC⟩)) hxC

/-- Full-index nonnegative weights for the convex hull of a finite family. -/
theorem mem_convexHull_range_weights {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (v : ι → E) {x : E} :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
        Finset.univ.affineCombination ℝ v w = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hnonneg, hsum, hx⟩ := hx
    refine ⟨(s : Set ι).indicator w, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ s <;> simp [hi, hnonneg]
    · simpa only [Finset.sum_indicator_subset _ (Finset.subset_univ s)] using hsum
    · rwa [← Finset.affineCombination_indicator_subset w v (Finset.subset_univ s)]
  · rintro ⟨w, hnonneg, hsum, rfl⟩
    exact affineCombination_mem_convexHull (fun i _ => hnonneg i) hsum

/-- The original face criterion is derived from affine independence, not
postulated as a certificate of the triangulation. -/
theorem affineCombination_mem_simplexFace_iff {m n : ℕ} (S : AffineSimplex m n)
    (I : Finset (Fin (n + 1))) {w : Fin (n + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ S.points w ∈ simplexFace S I ↔
      ∀ i, i ∉ I → w i = 0 := by
  classical
  constructor
  · intro hx i hi
    exact S.independent.eq_zero_of_affineCombination_mem_affineSpan hsum
      (convexHull_subset_affineSpan (𝕜 := ℝ) _ hx) (Finset.mem_univ i) hi
  · intro hz
    have hsI : ∑ i ∈ I, w i = 1 := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hz i hi)
    have heq : I.affineCombination ℝ S.points w =
        Finset.univ.affineCombination ℝ S.points w := by
      simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
        (Finset.univ.affineCombination_filter_of_ne w S.points
          (pred := fun i => i ∈ I) (fun i _ hwi => by
            by_contra hi
            exact hwi (hz i hi)))
    rw [← heq, affineCombination_eq_centerMass hsI]
    exact I.centerMass_mem_convexHull (fun i _ => hw i) (by rw [hsI]; norm_num)
      (fun i hi => Set.mem_image_of_mem _ hi)

/-- Every original simplex face is an extreme subset of its hull. -/
theorem simplexFace_isExtreme {m n : ℕ} (S : AffineSimplex m n)
    (I : Finset (Fin (n + 1))) :
    IsExtreme ℝ (simplexHull S) (simplexFace S I) := by
  classical
  refine ⟨convexHull_mono (Set.image_subset_range _ _), ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨wx, hwx, hsx, rfl⟩ := (mem_convexHull_range_weights S.points).mp hx
  obtain ⟨wy, hwy, hsy, rfl⟩ := (mem_convexHull_range_weights S.points).mp hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  let w : Fin (n + 1) → ℝ := fun i => a * wx i + b * wy i
  have hw : ∀ i, 0 ≤ w i := fun i =>
    add_nonneg (mul_nonneg ha.le (hwx i)) (mul_nonneg hb.le (hwy i))
  have hsw : ∑ i, w i = 1 := by
    simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum, hsx, hsy, mul_one, hab]
  have heq : Finset.univ.affineCombination ℝ S.points w =
      a • Finset.univ.affineCombination ℝ S.points wx +
      b • Finset.univ.affineCombination ℝ S.points wy := by
    simp only [Finset.affineCombination_eq_linear_combination _ _ _ hsw,
      Finset.affineCombination_eq_linear_combination _ _ _ hsx,
      Finset.affineCombination_eq_linear_combination _ _ _ hsy,
      w, add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
  have hz0 := (affineCombination_mem_simplexFace_iff S I hw hsw).mp (heq ▸ hz)
  apply (affineCombination_mem_simplexFace_iff S I hwx hsx).mpr
  intro i hi
  have hzero := hz0 i hi
  dsimp [w] at hzero
  have hmul : a * wx i = 0 := le_antisymm (by nlinarith [hwy i]) (mul_nonneg ha.le (hwx i))
  exact (mul_eq_zero.mp hmul).resolve_left ha.ne'

/-- Intersection with a convex extreme subset retains exactly its vertices.
This reusable hull lemma does not require the finite set to be independent. -/
theorem convexHull_inter_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Finset E) {A F : Set E} (hC : (C : Set E) ⊆ A)
    (hconvA : Convex ℝ A) (hF : IsExtreme ℝ A F) (hconv : Convex ℝ F) :
    convexHull ℝ (C : Set E) ∩ F = convexHull ℝ (C.filter (· ∈ F) : Set E) := by
  classical
  let H := convexHull ℝ (C.filter (· ∈ F) : Set E)
  have hgen : convexHull ℝ (C : Set E) ⊆ {x | x ∈ A ∧ (x ∈ F → x ∈ H)} := by
    apply convexHull_min
    · intro x hx
      exact ⟨hC hx, fun hxF => subset_convexHull ℝ _ (Finset.mem_filter.mpr ⟨hx, hxF⟩)⟩
    · intro x hx y hy a b ha hb hab
      refine ⟨hconvA hx.1 hy.1 ha hb hab, ?_⟩
      intro hz
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy.2 (by simpa [ha0, hb1] using hz)
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simpa [ha1, hb0] using hx.2 (by simpa [ha1, hb0] using hz)
      have hseg : a • x + b • y ∈ openSegment ℝ x y :=
        ⟨a, b, lt_of_le_of_ne ha (Ne.symm ha0), lt_of_le_of_ne hb (Ne.symm hb0), hab, rfl⟩
      exact (convex_convexHull ℝ _)
        (hx.2 (hF.left_mem_of_mem_openSegment hx.1 hy.1 hz hseg))
        (hy.2 (hF.right_mem_of_mem_openSegment hx.1 hy.1 hz hseg)) ha hb hab
  apply Set.Subset.antisymm
  · intro x hx
    exact (hgen hx.1).2 hx.2
  · exact Set.subset_inter
      (convexHull_mono (fun x hx => (Finset.mem_filter.mp hx).1))
      (convexHull_min (fun x hx => (Finset.mem_filter.mp hx).2) hconv)

/-- Intersecting a triangulation cell with an original face is exactly
its subcell on the vertices in that face. -/
theorem cellHull_inter_simplexFace {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {C : Finset (Euclidean m)} (hC : C ∈ T.complex.cells)
    (I : Finset (Fin (n + 1))) :
    cellHull C ∩ simplexFace S I = cellHull (C.filter (· ∈ simplexFace S I)) := by
  exact convexHull_inter_extreme C
    ((subset_convexHull ℝ _).trans (cellHull_subset_simplexHull T hC))
    (convex_convexHull ℝ _) (simplexFace_isExtreme S I) (convex_convexHull ℝ _)

/-- The induced complex covers the entire original face. Its purity is a
separate geometric obligation. -/
theorem inducedComplex_support {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) (I : Finset (Fin (n + 1))) :
    complexSupport (inducedComplex T I) = simplexFace S I := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hC, hxC⟩ := Set.mem_iUnion.mp hxC
    exact ((inducedCells_iff T I C).mp hC).2 hxC
  · intro x hx
    have hxS := (simplexFace_isExtreme S I).subset hx
    have hcovers : complexSupport T.complex = simplexHull S := T.covers
    rw [← hcovers] at hxS
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hxS
    obtain ⟨hC, hxC⟩ := Set.mem_iUnion.mp hxC
    let F := C.filter (· ∈ simplexFace S I)
    have hF : F ∈ inducedCells T I := by
      apply Finset.mem_filter.mpr
      exact ⟨T.complex.face_closed C hC F (Finset.filter_subset _ _),
        fun y hy => (Finset.mem_filter.mp hy).2⟩
    have hxF : x ∈ cellHull F := by
      rw [← cellHull_inter_simplexFace T hC I]
      exact ⟨hxC, hx⟩
    exact Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr ⟨hF, hxF⟩⟩

/-- A strictly positive barycentric point of a nonempty cell belongs only
to cofaces of that cell. -/
theorem exists_point_detects_cofaces {m : ℕ} (K : GeometricComplex m)
    {F : Finset (Euclidean m)} (hF : F ∈ K.cells) (hne : F.Nonempty) :
    ∃ p ∈ cellHull F, ∀ C ∈ K.cells, p ∈ cellHull C → F ⊆ C := by
  classical
  have : Nonempty F := hne.to_subtype
  let v : F → Euclidean m := Subtype.val
  let w : F → ℝ := fun _ => (Fintype.card F : ℝ)⁻¹
  have hc : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := F))
  have hsum : ∑ i, w i = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc
  let p := Finset.univ.affineCombination ℝ v w
  have hv : Set.range v = (F : Set (Euclidean m)) := by ext x; simp [v]
  have hp : p ∈ cellHull F := by
    change p ∈ convexHull ℝ (F : Set (Euclidean m))
    rw [← hv]
    exact affineCombination_mem_convexHull (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hsum
  refine ⟨p, hp, ?_⟩
  intro C hC hpC x hx
  by_contra hxC
  have hpI : p ∈ cellHull (F ∩ C) := by
    have hinter : cellHull F ∩ cellHull C = cellHull (F ∩ C) := K.inter_eq F hF C hC
    rw [← hinter]
    exact ⟨hp, hpC⟩
  have hi : v '' {i : F | (i : Euclidean m) ∈ C} =
      ((F ∩ C : Finset (Euclidean m)) : Set (Euclidean m)) := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_inter, Set.mem_inter_iff,
      Finset.mem_coe]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.property, hi⟩
    · rintro ⟨hyF, hyC⟩
      exact ⟨⟨y, hyF⟩, hyC, rfl⟩
  have hpSpan : p ∈ affineSpan ℝ (v '' {i : F | (i : Euclidean m) ∈ C}) := by
    rw [hi]
    exact convexHull_subset_affineSpan (𝕜 := ℝ) _ hpI
  have hzero := (K.independent F hF).eq_zero_of_affineCombination_mem_affineSpan
    hsum hpSpan (Finset.mem_univ (⟨x, hx⟩ : F)) hxC
  exact (inv_ne_zero hc) hzero

/-- A maximal cell in a finite geometric complex with convex support spans
the whole support. Finiteness excludes cells away from a positive-weight
point, and maximality excludes all the remaining cells except itself. -/
theorem support_subset_affineSpan_of_maximal {m : ℕ} (K : GeometricComplex m)
    (hconv : Convex ℝ (complexSupport K)) {F : Finset (Euclidean m)}
    (hF : F ∈ maximalCells K) (hne : F.Nonempty) :
    complexSupport K ⊆ affineSpan ℝ (F : Set (Euclidean m)) := by
  classical
  obtain ⟨hFcell, hFmax⟩ := Finset.mem_filter.mp hF
  obtain ⟨p, hpF, hp⟩ := exists_point_detects_cofaces K hFcell hne
  have hpK : p ∈ complexSupport K :=
    Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr ⟨hFcell, hpF⟩⟩
  obtain ⟨r, hr, hav⟩ := exists_ball_avoiding_cells K p
  have hlocal : Metric.ball p r ∩ complexSupport K ⊆ cellHull F := by
    intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx.2
    obtain ⟨hC, hxC⟩ := Set.mem_iUnion.mp hxC
    have hpC : p ∈ cellHull C := by
      by_contra hnot
      exact Set.disjoint_left.mp (hav C hC hnot) hx.1 hxC
    have heq := hFmax C hC (hp C hC hpC)
    rw [heq]
    exact hxC
  intro q hq
  let t : ℝ := min (1 / 2) (r / (2 * (dist q p + 1)))
  have hden : 0 < 2 * (dist q p + 1) := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hr hden)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let x := (1 - t) • p + t • q
  have hxK : x ∈ complexSupport K := hconv hpK hq (sub_nonneg.mpr ht1) ht.le (by ring)
  have hdist : dist x p < r := by
    have heq : x - p = t • (q - p) := by dsimp [x]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← dist_eq_norm]
    have hbound : t ≤ r / (2 * (dist q p + 1)) := min_le_right _ _
    have hprod : t * (2 * (dist q p + 1)) ≤ r := (le_div_iff₀ hden).mp hbound
    nlinarith [dist_nonneg (x := q) (y := p)]
  have hxF := hlocal ⟨hdist, hxK⟩
  have hpSpan := convexHull_subset_affineSpan (𝕜 := ℝ) _ hpF
  have hxSpan := convexHull_subset_affineSpan (𝕜 := ℝ) _ hxF
  have hxline : x = AffineMap.lineMap p q t := by
    simp [x, AffineMap.lineMap_apply_module]
  rw [hxline] at hxSpan
  simpa [ht.ne'] using AffineMap.lineMap_mem t⁻¹ hpSpan hxSpan

/-- Purity follows from the geometry of a finite common-face covering of a
simplex. In particular it is available for restricted complexes without
assuming that the restriction is already a triangulation. -/
theorem geometricComplex_pure_of_support {m n : ℕ} (K : GeometricComplex m)
    (S : AffineSimplex m n) (hcover : complexSupport K = simplexHull S) :
    ∀ F ∈ maximalCells K, F.card = n + 1 := by
  classical
  intro F hF
  have hFcell := (Finset.mem_filter.mp hF).1
  have hFmax := (Finset.mem_filter.mp hF).2
  have hne : F.Nonempty := by
    by_contra hn
    have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hp : S.points 0 ∈ complexSupport K := by
      rw [hcover]
      exact subset_convexHull ℝ _ (Set.mem_range_self 0)
    obtain ⟨C, hpC⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hC, hpC⟩ := Set.mem_iUnion.mp hpC
    have heq : F = C := hFmax C hC (hzero ▸ Finset.empty_subset _)
    rw [← heq] at hpC
    change S.points 0 ∈ cellHull F at hpC
    rw [hzero, cellHull_empty] at hpC
    exact hpC
  have hconv : Convex ℝ (complexSupport K) := by
    rw [hcover]
    exact convex_convexHull ℝ _
  have hSpan := support_subset_affineSpan_of_maximal K hconv hF hne
  let V := Finset.univ.image S.points
  have hV : (V : Set (Euclidean m)) = Set.range S.points := by simp [V]
  have hVcard : V.card = n + 1 := by
    rw [Finset.card_image_of_injective _ S.independent.injective]
    simp
  have hVi : AffineIndependent ℝ ((↑) : V → Euclidean m) := by
    have hr := S.independent.range
    rw [← hV] at hr
    exact hr
  apply le_antisymm
  · rw [← hVcard]
    apply (K.independent F hFcell).card_le_card_of_subset_affineSpan
    intro x hx
    have hxK : x ∈ complexSupport K := Set.mem_iUnion.mpr
      ⟨F, Set.mem_iUnion.mpr ⟨hFcell, subset_convexHull ℝ _ hx⟩⟩
    rw [hcover] at hxK
    rw [hV]
    exact convexHull_subset_affineSpan (𝕜 := ℝ) _ hxK
  · rw [← hVcard]
    apply hVi.card_le_card_of_subset_affineSpan
    intro x hx
    apply hSpan
    rw [hcover]
    exact subset_convexHull ℝ _ (hV ▸ hx)

/-- The geometric restriction to each original facet is a triangulation,
with no change to its set of cells. -/
theorem original_facet_triangulation :
    Specs.D10Topology.Ch17.FacetIncidence.original_facet_triangulation := by
  intro m n S T i
  let h : (Finset.univ.erase i).card = n + 1 := by simp
  let S' := S.face h
  let K := inducedComplex T (Finset.univ.erase i)
  have hcover : complexSupport K = simplexHull S' := by
    rw [simplexHull_face]
    exact inducedComplex_support T _
  exact ⟨⟨K, hcover, geometricComplex_pure_of_support K S' hcover⟩, rfl⟩


/-- Ambient affine coordinates extending the coordinates on an independent cell.
Only their vertex values are data; all geometric consequences are derived below. -/
structure CellCoordinates {m : ℕ} (C : Finset (Euclidean m)) where
  coord : C → (Euclidean m →ᵃ[ℝ] ℝ)
  on_vertex : ∀ i j : C, coord i j = if i = j then 1 else 0

theorem exists_cellCoordinates {m : ℕ} {C : Finset (Euclidean m)}
    (hC : AffineIndependent ℝ ((↑) : C → Euclidean m)) :
    Nonempty (CellCoordinates C) := by
  classical
  obtain ⟨A, hCA, hA, hspan⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top (s := (C : Set (Euclidean m))) hC
  let b : AffineBasis A ℝ (Euclidean m) := ⟨Subtype.val, hA, by simpa using hspan⟩
  refine ⟨⟨fun i => b.coord ⟨i, hCA i.property⟩, ?_⟩⟩
  intro i j
  change b.coord ⟨i, hCA i.property⟩ (b ⟨j, hCA j.property⟩) = _
  rw [b.coord_apply]
  simp only [Subtype.mk.injEq, Subtype.coe_inj]

namespace CellCoordinates
variable {m : ℕ} {C : Finset (Euclidean m)} (c : CellCoordinates C)

theorem apply_combination {w : C → ℝ} (hw : ∑ i, w i = 1) (i : C) :
    c.coord i (Finset.univ.affineCombination ℝ ((↑) : C → Euclidean m) w) = w i := by
  rw [Finset.map_affineCombination Finset.univ _ _ hw (c.coord i),
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp [c.on_vertex]

theorem represents {x : Euclidean m} (hx : x ∈ affineSpan ℝ (C : Set (Euclidean m))) :
    ∑ i, c.coord i x = 1 ∧
      Finset.univ.affineCombination ℝ ((↑) : C → Euclidean m) (fun i => c.coord i x) = x := by
  have hr : Set.range ((↑) : C → Euclidean m) = (C : Set (Euclidean m)) := by simp
  rw [← hr] at hx
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  simpa only [c.apply_combination hw, and_true] using hw

theorem hull_iff {x : Euclidean m} (hx : x ∈ affineSpan ℝ (C : Set (Euclidean m))) :
    x ∈ cellHull C ↔ ∀ i, 0 ≤ c.coord i x := by
  have hr : Set.range ((↑) : C → Euclidean m) = (C : Set (Euclidean m)) := by simp
  change x ∈ convexHull ℝ (C : Set (Euclidean m)) ↔ _
  rw [← hr, mem_convexHull_range_weights]
  constructor
  · rintro ⟨w, hw, hsum, rfl⟩ i
    simpa only [c.apply_combination hsum] using hw i
  · intro h
    exact ⟨_, h, (c.represents hx).1, (c.represents hx).2⟩

theorem nonneg {x : Euclidean m} (hx : x ∈ cellHull C) (i : C) : 0 ≤ c.coord i x :=
  (c.hull_iff (convexHull_subset_affineSpan (𝕜 := ℝ) _ hx)).mp hx i

/-- Evaluation of any affine functional from its values at the vertices. -/
theorem eval {x : Euclidean m} (hx : x ∈ affineSpan ℝ (C : Set (Euclidean m)))
    (f : Euclidean m →ᵃ[ℝ] ℝ) :
    f x = ∑ i, c.coord i x * f i := by
  have h := c.represents hx
  conv_lhs => rw [← h.2]
  rw [Finset.map_affineCombination Finset.univ _ _ h.1 f,
    Finset.affineCombination_eq_linear_combination _ _ _ h.1]
  rfl

end CellCoordinates

/-- The affine span of each top cell is the affine span of the simplex. -/
theorem topCell_affineSpan {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {C : Finset (Euclidean m)} (hC : C ∈ topCells T) :
    affineSpan ℝ (C : Set (Euclidean m)) = affineSpan ℝ (Set.range S.points) := by
  have hcell := (Finset.mem_filter.mp hC).1
  have hcard := (Finset.mem_filter.mp hC).2
  have hle : affineSpan ℝ (C : Set (Euclidean m)) ≤
      affineSpan ℝ (Set.range S.points) := by
    apply affineSpan_le.mpr
    exact (subset_convexHull ℝ _).trans
      ((cellHull_subset_simplexHull T hcell).trans (convexHull_subset_affineSpan (𝕜 := ℝ) _))
  apply le_antisymm hle
  by_contra hnot
  have hlt := lt_of_le_not_ge hle hnot
  let V := Finset.univ.image S.points
  have hV : (V : Set (Euclidean m)) = Set.range S.points := by simp [V]
  have hvc : V.card = n + 1 := by simp [V, Finset.card_image_of_injective _ S.independent.injective]
  rw [← hV] at hlt
  have h := (T.complex.independent C hcell).card_lt_card_of_affineSpan_lt_affineSpan hlt
  omega


/-- An affine functional vanishing at the generators vanishes on their affine span. -/
theorem affine_zero_on_span {m : ℕ} {F : Finset (Euclidean m)}
    (f : Euclidean m →ᵃ[ℝ] ℝ) (hf : ∀ v ∈ F, f v = 0)
    {x : Euclidean m} (hx : x ∈ affineSpan ℝ (F : Set (Euclidean m))) : f x = 0 := by
  have hr : Set.range ((↑) : F → Euclidean m) = (F : Set (Euclidean m)) := by simp
  rw [← hr] at hx
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  rw [Finset.map_affineCombination Finset.univ _ _ hw f,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp [hf]

theorem affine_nonneg_on_hull {m : ℕ} {F : Finset (Euclidean m)}
    (f : Euclidean m →ᵃ[ℝ] ℝ) (hf : ∀ v ∈ F, 0 ≤ f v)
    {x : Euclidean m} (hx : x ∈ cellHull F) : 0 ≤ f x := by
  have hr : Set.range ((↑) : F → Euclidean m) = (F : Set (Euclidean m)) := by simp
  change x ∈ convexHull ℝ (F : Set (Euclidean m)) at hx
  rw [← hr, mem_convexHull_range_weights] at hx
  obtain ⟨w, hw, hsum, rfl⟩ := hx
  rw [Finset.map_affineCombination Finset.univ _ _ hsum f,
    Finset.affineCombination_eq_linear_combination _ _ _ hsum]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hf i i.property))

/-- A barycenter detects every nonnegative affine functional that vanishes on
its cell. The universal property also applies to coordinates of other cells. -/
theorem exists_point_detects_affine_zeros {m : ℕ} {F : Finset (Euclidean m)}
    (hne : F.Nonempty) : ∃ p ∈ cellHull F,
      ∀ f : Euclidean m →ᵃ[ℝ] ℝ, (∀ v ∈ F, 0 ≤ f v) →
        (f p = 0 ↔ ∀ v ∈ F, f v = 0) := by
  classical
  have : Nonempty F := hne.to_subtype
  let w : F → ℝ := fun _ => (Fintype.card F : ℝ)⁻¹
  have hc : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ i, w i = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc.ne'
  let p := Finset.univ.affineCombination ℝ ((↑) : F → Euclidean m) w
  have hp : p ∈ cellHull F := by
    have hr : Set.range ((↑) : F → Euclidean m) = (F : Set (Euclidean m)) := by simp
    change p ∈ convexHull ℝ (F : Set (Euclidean m))
    rw [← hr]
    exact affineCombination_mem_convexHull (fun _ _ => (inv_pos.mpr hc).le) hsum
  refine ⟨p, hp, fun f hf => ?_⟩
  have heq : f p = ∑ i : F, w i * f i := by
    change f (Finset.univ.affineCombination ℝ ((↑) : F → Euclidean m) w) = _
    rw [Finset.map_affineCombination Finset.univ _ _ hsum f,
      Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    rfl
  constructor
  · intro hz v hv
    have hzero : ∀ i : F, w i * f i = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ (Finset.univ : Finset F)) =>
          mul_nonneg (inv_pos.mpr hc).le (hf i i.property))).mp (heq.symm.trans hz)
      exact fun i => hh i (Finset.mem_univ i)
    exact (mul_eq_zero.mp (hzero ⟨v, hv⟩)).resolve_left (inv_ne_zero hc.ne')
  · intro hz
    exact affine_zero_on_span f hz (convexHull_subset_affineSpan (𝕜 := ℝ) _ hp)

/-- A codimension-one inclusion adds precisely one vertex. -/
theorem facet_coface_eq_insert {m n : ℕ} {F C : Finset (Euclidean m)}
    (hFC : F ⊆ C) (hF : F.card = n) (hC : C.card = n + 1) :
    ∃ v, v ∉ F ∧ C = insert v F := by
  classical
  have hd : (C \ F).card = 1 := by rw [Finset.card_sdiff_of_subset hFC, hC, hF]; omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hd
  have hvd : v ∈ C \ F := by rw [hv]; simp
  refine ⟨v, (Finset.mem_sdiff.mp hvd).2, ?_⟩
  have he := Finset.sdiff_union_of_subset hFC
  rw [hv] at he
  simpa using he.symm

namespace CellCoordinates
variable {m : ℕ} {C F : Finset (Euclidean m)} (c : CellCoordinates C)

/-- A functional zero on the common facet has only the transverse coordinate. -/
theorem eval_of_zero_on_facet {v : Euclidean m} (_hv : v ∉ F) (hC : C = insert v F)
    (f : Euclidean m →ᵃ[ℝ] ℝ) (hf : ∀ u ∈ F, f u = 0)
    {x : Euclidean m} (hx : x ∈ affineSpan ℝ (C : Set (Euclidean m))) :
    f x = c.coord ⟨v, hC ▸ Finset.mem_insert_self _ _⟩ x * f v := by
  rw [c.eval hx f]
  change ∑ i : C, c.coord i x * f i =
    (fun i : C => c.coord i x * f i) ⟨v, hC ▸ Finset.mem_insert_self _ _⟩
  apply Finset.sum_eq_single
  · intro i _ hi
    have hiF : (i : Euclidean m) ∈ F := by
      have him : (i : Euclidean m) ∈ insert v F := by simpa only [hC] using i.property
      rw [Finset.mem_insert] at him
      exact him.resolve_left (fun he => hi (Subtype.ext he))
    rw [hf i hiF, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem zero_on_facet {v : Euclidean m} (hv : v ∉ F) (hC : C = insert v F) :
    ∀ u ∈ F, c.coord ⟨v, hC ▸ Finset.mem_insert_self _ _⟩ u = 0 := by
  intro u hu
  have huC : u ∈ C := hC ▸ Finset.mem_insert_of_mem hu
  have hne : (⟨v, hC ▸ Finset.mem_insert_self _ _⟩ : C) ≠ ⟨u, huC⟩ := by
    intro h; exact hv ((Subtype.mk.inj h) ▸ hu)
  simpa [hne] using c.on_vertex ⟨v, hC ▸ Finset.mem_insert_self _ _⟩ ⟨u, huC⟩

/-- All non-transverse coordinates are positive at a positive facet point. -/
theorem positive_on_facet {v : Euclidean m} (_hv : v ∉ F) (hC : C = insert v F)
    {p : Euclidean m} (hp : p ∈ cellHull F)
    (hpos : ∀ f : Euclidean m →ᵃ[ℝ] ℝ, (∀ u ∈ F, 0 ≤ f u) →
      (f p = 0 ↔ ∀ u ∈ F, f u = 0)) :
    ∀ i : C, (i : Euclidean m) ∈ F → 0 < c.coord i p := by
  intro i hi
  have hFC : F ⊆ C := by rw [hC]; exact Finset.subset_insert _ _
  have hn : ∀ u ∈ F, 0 ≤ c.coord i u := by
    intro u hu
    simpa only [c.on_vertex] using (show 0 ≤ c.coord i (⟨u, hFC hu⟩ : C) by
      rw [c.on_vertex]; split_ifs <;> norm_num)
  have hnp := affine_nonneg_on_hull (c.coord i) hn hp
  apply lt_of_le_of_ne hnp
  intro hz
  have hzv := (hpos (c.coord i) hn).mp hz.symm i hi
  norm_num [c.on_vertex] at hzv

end CellCoordinates


namespace CellCoordinates
variable {m : ℕ} {C F : Finset (Euclidean m)} (c : CellCoordinates C)

/-- Near a positive facet point, all inequalities except the transverse one
are strict. The ambient ball is subsequently intersected with the affine span. -/
theorem exists_ball_facet {v : Euclidean m} (hv : v ∉ F) (hC : C = insert v F)
    {p : Euclidean m} (hp : p ∈ cellHull F)
    (hpos : ∀ f : Euclidean m →ᵃ[ℝ] ℝ, (∀ u ∈ F, 0 ≤ f u) →
      (f p = 0 ↔ ∀ u ∈ F, f u = 0)) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r,
      x ∈ affineSpan ℝ (C : Set (Euclidean m)) →
      (x ∈ cellHull C ↔ 0 ≤ c.coord ⟨v, hC ▸ Finset.mem_insert_self _ _⟩ x) := by
  classical
  let O : Set (Euclidean m) := ⋂ i : C, {x | (i : Euclidean m) ∈ F → 0 < c.coord i x}
  have hopen : IsOpen O := by
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : (i : Euclidean m) ∈ F
    · simpa only [hi, true_implies] using
        (isOpen_lt continuous_const (c.coord i).continuous_of_finiteDimensional)
    · simp [hi]
  have hpO : p ∈ O := by
    exact Set.mem_iInter.mpr (fun i => c.positive_on_facet hv hC hp hpos i)
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hopen p hpO
  refine ⟨r, hr, fun x hx hspan => ?_⟩
  rw [c.hull_iff hspan]
  constructor
  · exact fun h => h _
  · intro h i
    by_cases hi : (i : Euclidean m) ∈ F
    · exact ((Set.mem_iInter.mp (hrO hx) i) hi).le
    · have heq : i = ⟨v, hC ▸ Finset.mem_insert_self _ _⟩ := by
        apply Subtype.ext
        have him : (i : Euclidean m) ∈ insert v F := by simpa only [hC] using i.property
        rw [Finset.mem_insert] at him
        exact him.resolve_right hi
      simpa only [heq] using h

end CellCoordinates

/-- Arbitrarily short positive steps on a line, with an explicit bound. -/
theorem exists_small_line_step {m : ℕ} (p q : Euclidean m) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ AffineMap.lineMap p q t ∈ Metric.ball p r := by
  let t : ℝ := min (1 / 2) (r / (2 * (dist q p + 1)))
  have hden : 0 < 2 * (dist q p + 1) := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hr hden)
  refine ⟨t, ht, (min_le_left _ _).trans (by norm_num), ?_⟩
  change dist (AffineMap.lineMap p q t) p < r
  rw [AffineMap.lineMap_apply_module', dist_eq_norm, add_sub_cancel_right,
    norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← dist_eq_norm]
  have hbound : t ≤ r / (2 * (dist q p + 1)) := min_le_right _ _
  have hprod : t * (2 * (dist q p + 1)) ≤ r := (le_div_iff₀ hden).mp hbound
  nlinarith [dist_nonneg (x := q) (y := p)]

/-- Two distinct codimension-one cofaces have exactly their common facet in common. -/
theorem distinct_cofaces_inter {m n : ℕ} {F C D : Finset (Euclidean m)}
    (hFC : F ⊆ C) (hFD : F ⊆ D) (hF : F.card = n)
    (hC : C.card = n + 1) (hD : D.card = n + 1) (hne : C ≠ D) : C ∩ D = F := by
  classical
  obtain ⟨v, hv, hCv⟩ := facet_coface_eq_insert hFC hF hC
  have hvD : v ∉ D := by
    intro h
    apply hne
    apply Finset.eq_of_subset_of_card_le
    · rw [hCv]; exact Finset.insert_subset h hFD
    · omega
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hx
    rw [hCv, Finset.mem_insert] at hxC
    exact hxC.resolve_left (fun he => hvD (he ▸ hxD))
  · exact fun hx => Finset.mem_inter.mpr ⟨hFC hx, hFD hx⟩

/-- Distinct cells cannot occupy the same transverse side of their common facet. -/
theorem coface_coordinate_nonpos {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {F C D : Finset (Euclidean m)}
    (_hFcell : F ∈ T.complex.cells) (hF : F.card = n) (hn : 0 < n)
    (hC : C ∈ topCells T) (hD : D ∈ topCells T) (hFC : F ⊆ C) (hFD : F ⊆ D)
    (hne : C ≠ D) (c : CellCoordinates C) (d : CellCoordinates D)
    {v w : Euclidean m} (hv : v ∉ F) (hCv : C = insert v F)
    (hw : w ∉ F) (hDw : D = insert w F) :
    d.coord ⟨w, hDw ▸ Finset.mem_insert_self _ _⟩ v ≤ 0 := by
  classical
  by_contra hnpos
  have hsign : 0 < d.coord ⟨w, hDw ▸ Finset.mem_insert_self _ _⟩ v := lt_of_not_ge hnpos
  obtain ⟨p, hp, hpos⟩ := exists_point_detects_affine_zeros
    (Finset.card_pos.mp (hF ▸ hn))
  obtain ⟨r, hr, hlocal⟩ := d.exists_ball_facet hw hDw hp hpos
  obtain ⟨t, ht, ht1, hxt⟩ := exists_small_line_step p v hr
  let x := AffineMap.lineMap p v t
  have hpC : p ∈ cellHull C := cellHull_mono hFC hp
  have hvC : v ∈ cellHull C := subset_convexHull ℝ _ (hCv ▸ Finset.mem_insert_self _ _)
  have hxC : x ∈ cellHull C := by
    dsimp only [x]
    rw [AffineMap.lineMap_apply_module]
    exact (convex_convexHull ℝ _) hpC hvC (sub_nonneg.mpr ht1) ht.le (by ring)
  have hxspanD : x ∈ affineSpan ℝ (D : Set (Euclidean m)) := by
    rw [topCell_affineSpan T hD, ← topCell_affineSpan T hC]
    exact convexHull_subset_affineSpan (𝕜 := ℝ) _ hxC
  have hd0 : d.coord ⟨w, hDw ▸ Finset.mem_insert_self _ _⟩ p = 0 :=
    affine_zero_on_span _ (d.zero_on_facet hw hDw) (convexHull_subset_affineSpan (𝕜 := ℝ) _ hp)
  have hdpos : 0 ≤ d.coord ⟨w, hDw ▸ Finset.mem_insert_self _ _⟩ x := by
    dsimp [x]
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hd0]
    positivity
  have hxD := (hlocal x hxt hxspanD).mpr hdpos
  have hxF : x ∈ cellHull F := by
    have hi : cellHull C ∩ cellHull D = cellHull (C ∩ D) :=
      T.complex.inter_eq C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1
    rw [distinct_cofaces_inter hFC hFD hF (Finset.mem_filter.mp hC).2
      (Finset.mem_filter.mp hD).2 hne] at hi
    rw [← hi]
    exact ⟨hxC, hxD⟩
  have hc0 : c.coord ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩ p = 0 :=
    affine_zero_on_span _ (c.zero_on_facet hv hCv) (convexHull_subset_affineSpan (𝕜 := ℝ) _ hp)
  have hcx0 := affine_zero_on_span _ (c.zero_on_facet hv hCv)
    (convexHull_subset_affineSpan (𝕜 := ℝ) _ hxF)
  have hcx : c.coord ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩ x = t := by
    dsimp [x]
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hc0]
    have hcv := c.on_vertex ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩ ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩
    simp only [ite_true] at hcv
    simp [hcv]
  linarith


/-- Relative to either cell, the extra vertex of a distinct coface is strictly
on the opposite side. Nonvanishing follows from coordinate reconstruction. -/
theorem coface_coordinate_neg {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {F C D : Finset (Euclidean m)}
    (hFcell : F ∈ T.complex.cells) (hF : F.card = n) (hn : 0 < n)
    (hC : C ∈ topCells T) (hD : D ∈ topCells T) (hFC : F ⊆ C) (hFD : F ⊆ D)
    (hne : C ≠ D) (c : CellCoordinates C) (d : CellCoordinates D)
    {v w : Euclidean m} (hv : v ∉ F) (hCv : C = insert v F)
    (hw : w ∉ F) (hDw : D = insert w F) :
    c.coord ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩ w < 0 := by
  have hnp := coface_coordinate_nonpos T hFcell hF hn hD hC hFD hFC hne.symm d c hw hDw hv hCv
  have hvspan : v ∈ affineSpan ℝ (D : Set (Euclidean m)) := by
    rw [topCell_affineSpan T hD, ← topCell_affineSpan T hC]
    exact mem_affineSpan ℝ (hCv ▸ Finset.mem_insert_self _ _)
  have heq := d.eval_of_zero_on_facet hw hDw (c.coord ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩)
    (c.zero_on_facet hv hCv) hvspan
  have hcv := c.on_vertex ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩ ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩
  have hnz : c.coord ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩ w ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at heq
    simp only [ite_true] at hcv
    linarith
  exact lt_of_le_of_ne hnp hnz

/-- There are at most two top-dimensional cofaces of any triangulation facet. -/
theorem incidentTopCells_card_le_two {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {F : Finset (Euclidean m)} (hF : F ∈ facets T) :
    (incidentTopCells T F).card ≤ 2 := by
  classical
  obtain ⟨hFcell, hn, hFcard⟩ := Finset.mem_filter.mp hF
  by_contra hnot
  obtain ⟨C, D, E, hC, hD, hE, hCD, hCE, hDE⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge hnot)
  obtain ⟨hC, hFC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hD, hFD⟩ := Finset.mem_filter.mp hD
  obtain ⟨hE, hFE⟩ := Finset.mem_filter.mp hE
  obtain ⟨v, hv, hCv⟩ := facet_coface_eq_insert hFC hFcard (Finset.mem_filter.mp hC).2
  obtain ⟨w, hw, hDw⟩ := facet_coface_eq_insert hFD hFcard (Finset.mem_filter.mp hD).2
  obtain ⟨z, hz, hEz⟩ := facet_coface_eq_insert hFE hFcard (Finset.mem_filter.mp hE).2
  obtain ⟨c⟩ := exists_cellCoordinates (T.complex.independent C (Finset.mem_filter.mp hC).1)
  obtain ⟨d⟩ := exists_cellCoordinates (T.complex.independent D (Finset.mem_filter.mp hD).1)
  obtain ⟨e⟩ := exists_cellCoordinates (T.complex.independent E (Finset.mem_filter.mp hE).1)
  have hnw := coface_coordinate_neg T hFcell hFcard hn hC hD hFC hFD hCD c d hv hCv hw hDw
  have hnz := coface_coordinate_neg T hFcell hFcard hn hC hE hFC hFE hCE c e hv hCv hz hEz
  have hnzw := coface_coordinate_neg T hFcell hFcard hn hD hE hFD hFE hDE d e hw hDw hz hEz
  have hzspan : z ∈ affineSpan ℝ (D : Set (Euclidean m)) := by
    rw [topCell_affineSpan T hD, ← topCell_affineSpan T hE]
    exact mem_affineSpan ℝ (hEz ▸ Finset.mem_insert_self _ _)
  have heq := d.eval_of_zero_on_facet hw hDw (c.coord ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩)
    (c.zero_on_facet hv hCv) hzspan
  have hp := mul_pos_of_neg_of_neg hnzw hnw
  linarith


/-- Barycentric functionals of the original simplex, extended to the ambient
space. Such extensions exist even when its affine span is proper. -/
structure SimplexCoordinates {m n : ℕ} (S : AffineSimplex m n) where
  coord : Fin (n + 1) → (Euclidean m →ᵃ[ℝ] ℝ)
  on_vertex : ∀ i j, coord i (S.points j) = if i = j then 1 else 0

theorem exists_simplexCoordinates {m n : ℕ} (S : AffineSimplex m n) :
    Nonempty (SimplexCoordinates S) := by
  classical
  let V := Finset.univ.image S.points
  have hV : (V : Set (Euclidean m)) = Set.range S.points := by simp [V]
  have hi : AffineIndependent ℝ ((↑) : V → Euclidean m) := by
    have hh := S.independent.range
    rw [← hV] at hh
    exact hh
  obtain ⟨c⟩ := exists_cellCoordinates hi
  have hv : ∀ i, S.points i ∈ V := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  refine ⟨⟨fun i => c.coord ⟨S.points i, hv i⟩, ?_⟩⟩
  intro i j
  simpa only [Subtype.mk.injEq, S.independent.injective.eq_iff] using
    c.on_vertex ⟨S.points i, hv i⟩ ⟨S.points j, hv j⟩

namespace SimplexCoordinates
variable {m n : ℕ} {S : AffineSimplex m n} (c : SimplexCoordinates S)

theorem apply_combination {w : Fin (n + 1) → ℝ} (hw : ∑ i, w i = 1) (i : Fin (n + 1)) :
    c.coord i (Finset.univ.affineCombination ℝ S.points w) = w i := by
  rw [Finset.map_affineCombination Finset.univ _ _ hw (c.coord i),
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp [c.on_vertex]

theorem represents {x : Euclidean m} (hx : x ∈ affineSpan ℝ (Set.range S.points)) :
    ∑ i, c.coord i x = 1 ∧
      Finset.univ.affineCombination ℝ S.points (fun i => c.coord i x) = x := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  simpa only [c.apply_combination hw, and_true] using hw

theorem hull_iff {x : Euclidean m} (hx : x ∈ affineSpan ℝ (Set.range S.points)) :
    x ∈ simplexHull S ↔ ∀ i, 0 ≤ c.coord i x := by
  change x ∈ convexHull ℝ (Set.range S.points) ↔ _
  rw [mem_convexHull_range_weights]
  constructor
  · rintro ⟨w, hw, hsum, rfl⟩ i
    simpa only [c.apply_combination hsum] using hw i
  · intro h
    exact ⟨_, h, (c.represents hx).1, (c.represents hx).2⟩

theorem nonneg {x : Euclidean m} (hx : x ∈ simplexHull S) (i : Fin (n + 1)) :
    0 ≤ c.coord i x :=
  (c.hull_iff (convexHull_subset_affineSpan (𝕜 := ℝ) _ hx)).mp hx i

theorem face_iff {x : Euclidean m} (hx : x ∈ simplexHull S) (i : Fin (n + 1)) :
    x ∈ simplexFace S (Finset.univ.erase i) ↔ c.coord i x = 0 := by
  have hspan := convexHull_subset_affineSpan (𝕜 := ℝ) _ hx
  have hre := c.represents hspan
  conv_lhs => rw [← hre.2]
  rw [affineCombination_mem_simplexFace_iff S _ (fun j => c.nonneg hx j) hre.1]
  simp

end SimplexCoordinates

/-- The barycentric point used for half-ball arguments also detects cofaces. -/
theorem detects_cofaces_of_affine_zeros {m : ℕ} (K : GeometricComplex m)
    {F : Finset (Euclidean m)} (hF : F ∈ K.cells)
    {p : Euclidean m} (hp : p ∈ cellHull F)
    (hpos : ∀ f : Euclidean m →ᵃ[ℝ] ℝ, (∀ u ∈ F, 0 ≤ f u) →
      (f p = 0 ↔ ∀ u ∈ F, f u = 0)) :
    ∀ C ∈ K.cells, p ∈ cellHull C → F ⊆ C := by
  classical
  obtain ⟨c⟩ := exists_cellCoordinates (K.independent F hF)
  intro C hC hpC v hv
  by_contra hvC
  let i : F := ⟨v, hv⟩
  have hn : ∀ u ∈ F, 0 ≤ c.coord i u := by
    intro u hu
    have h := c.on_vertex i ⟨u, hu⟩
    rw [h]; split_ifs <;> norm_num
  have hpI : p ∈ cellHull (F ∩ C) := by
    have heq : cellHull F ∩ cellHull C = cellHull (F ∩ C) := K.inter_eq F hF C hC
    rw [← heq]; exact ⟨hp, hpC⟩
  have hz : c.coord i p = 0 := by
    apply affine_zero_on_span _ _ (convexHull_subset_affineSpan (𝕜 := ℝ) _ hpI)
    intro u hu
    obtain ⟨huF, huC⟩ := Finset.mem_inter.mp hu
    have hne : i ≠ (⟨u, huF⟩ : F) := by
      intro heq
      have heqv : v = u := congrArg Subtype.val heq
      exact hvC (heqv ▸ huC)
    simpa only [hne, ite_false] using c.on_vertex i ⟨u, huF⟩
  have hzv := (hpos _ hn).mp hz v hv
  have hone := c.on_vertex i i
  simp only [ite_true] at hone
  change c.coord i i = 0 at hzv
  linarith


/-- A boundary facet has only one inward coface. Its original supporting
coordinate is nonnegative throughout the simplex and zero on the whole facet. -/
theorem boundary_facet_incidence :
    Specs.D10Topology.Ch17.FacetIncidence.boundary_facet_incidence := by
  classical
  intro m n S T hn F hFB
  obtain ⟨hF, hboundary⟩ := Finset.mem_filter.mp hFB
  obtain ⟨hFcell, _, hFcard⟩ := Finset.mem_filter.mp hF
  have hnonempty := incidentTopCells_nonempty T hFcell
  have hle : (incidentTopCells T F).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro C hC D hD
    by_contra hne
    obtain ⟨hC, hFC⟩ := Finset.mem_filter.mp hC
    obtain ⟨hD, hFD⟩ := Finset.mem_filter.mp hD
    obtain ⟨v, hv, hCv⟩ := facet_coface_eq_insert hFC hFcard (Finset.mem_filter.mp hC).2
    obtain ⟨w, hw, hDw⟩ := facet_coface_eq_insert hFD hFcard (Finset.mem_filter.mp hD).2
    obtain ⟨c⟩ := exists_cellCoordinates (T.complex.independent C (Finset.mem_filter.mp hC).1)
    obtain ⟨d⟩ := exists_cellCoordinates (T.complex.independent D (Finset.mem_filter.mp hD).1)
    obtain ⟨e⟩ := exists_simplexCoordinates S
    obtain ⟨p, hp, hpos⟩ := exists_point_detects_affine_zeros (Finset.card_pos.mp (hFcard ▸ hn))
    have hpS := cellHull_subset_simplexHull T hFcell hp
    have hpB := hboundary hp
    change p ∈ ⋃ i, simplexFace S (Finset.univ.erase i) at hpB
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpB
    let f := e.coord i
    have hfp : f p = 0 := (e.face_iff hpS i).mp hpi
    have hnF : ∀ u ∈ F, 0 ≤ f u := fun u hu =>
      e.nonneg (cellHull_subset_simplexHull T hFcell (subset_convexHull ℝ _ hu)) i
    have hzF := (hpos f hnF).mp hfp
    have hvC : v ∈ C := hCv ▸ Finset.mem_insert_self _ _
    have hvS : v ∈ simplexHull S := cellHull_subset_simplexHull T (Finset.mem_filter.mp hC).1
      (subset_convexHull ℝ _ hvC)
    have hfv : 0 < f v := by
      apply lt_of_le_of_ne (e.nonneg hvS i)
      intro hz
      have hzC : ∀ u ∈ C, f u = 0 := by
        intro u hu
        rw [hCv, Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · exact hz.symm
        · exact hzF u hu
      have hzi : f (S.points i) = 0 := by
        apply affine_zero_on_span f hzC
        rw [topCell_affineSpan T hC]
        exact mem_affineSpan ℝ (Set.mem_range_self i)
      have hone := e.on_vertex i i
      simp only [ite_true] at hone
      change e.coord i (S.points i) = 0 at hzi
      linarith
    have hncoord := coface_coordinate_neg T hFcell hFcard hn hC hD hFC hFD hne c d hv hCv hw hDw
    have hwspan : w ∈ affineSpan ℝ (C : Set (Euclidean m)) := by
      rw [topCell_affineSpan T hC, ← topCell_affineSpan T hD]
      exact mem_affineSpan ℝ (hDw ▸ Finset.mem_insert_self _ _)
    have heval := c.eval_of_zero_on_facet hv hCv f hzF hwspan
    have hfw : 0 ≤ f w := e.nonneg
      (cellHull_subset_simplexHull T (Finset.mem_filter.mp hD).1
        (subset_convexHull ℝ _ (hDw ▸ Finset.mem_insert_self _ _))) i
    have hneg := mul_neg_of_neg_of_pos hncoord hfv
    linarith
  have hpos : 0 < (incidentTopCells T F).card := Finset.card_pos.mpr hnonempty
  change (incidentTopCells T F).card = 1
  exact Nat.le_antisymm hle hpos

/-- A positive facet point of an internal facet is in the relative interior
of the original simplex: all its original barycentric coordinates are positive. -/
theorem internal_facet_positive_coordinates {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {F : Finset (Euclidean m)} (hF : F ∈ internalFacets T)
    (e : SimplexCoordinates S) {p : Euclidean m} (hp : p ∈ cellHull F)
    (hpos : ∀ f : Euclidean m →ᵃ[ℝ] ℝ, (∀ u ∈ F, 0 ≤ f u) →
      (f p = 0 ↔ ∀ u ∈ F, f u = 0)) :
    ∀ i, 0 < e.coord i p := by
  obtain ⟨hFfacet, hnotB⟩ := Finset.mem_sdiff.mp hF
  have hFcell := (Finset.mem_filter.mp hFfacet).1
  have hsub := cellHull_subset_simplexHull T hFcell
  intro i
  apply lt_of_le_of_ne (e.nonneg (hsub hp) i)
  intro hz
  have hnF : ∀ u ∈ F, 0 ≤ e.coord i u := fun u hu =>
    e.nonneg (hsub (subset_convexHull ℝ _ hu)) i
  have hzF := (hpos (e.coord i) hnF).mp hz.symm
  apply hnotB
  apply Finset.mem_filter.mpr
  refine ⟨hFfacet, fun x hx => ?_⟩
  change x ∈ ⋃ j, simplexFace S (Finset.univ.erase j)
  apply Set.mem_iUnion.mpr
  refine ⟨i, (e.face_iff (hsub hx) i).mpr ?_⟩
  exact affine_zero_on_span _ hzF (convexHull_subset_affineSpan (𝕜 := ℝ) _ hx)

/-- Coverage of a small point across the facet produces a second actual top
cell. The point is constructed inside the original simplex, in its affine span. -/
theorem internal_facet_two_le_incidence {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) {F : Finset (Euclidean m)} (hF : F ∈ internalFacets T) :
    2 ≤ (incidentTopCells T F).card := by
  classical
  have hFfacet := (Finset.mem_sdiff.mp hF).1
  obtain ⟨hFcell, hn, hFcard⟩ := Finset.mem_filter.mp hFfacet
  obtain ⟨C, hC, hFC⟩ := exists_topCell_superset T hFcell
  obtain ⟨v, hv, hCv⟩ := facet_coface_eq_insert hFC hFcard (Finset.mem_filter.mp hC).2
  obtain ⟨c⟩ := exists_cellCoordinates (T.complex.independent C (Finset.mem_filter.mp hC).1)
  obtain ⟨e⟩ := exists_simplexCoordinates S
  obtain ⟨p, hp, hpos⟩ := exists_point_detects_affine_zeros (Finset.card_pos.mp (hFcard ▸ hn))
  have hdetect := detects_cofaces_of_affine_zeros T.complex hFcell hp hpos
  have hpe := internal_facet_positive_coordinates T hF e hp hpos
  let O : Set (Euclidean m) := ⋂ i, {x | 0 < e.coord i x}
  have hopen : IsOpen O := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (e.coord i).continuous_of_finiteDimensional
  have hpO : p ∈ O := Set.mem_iInter.mpr hpe
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hopen p hpO
  obtain ⟨r', hr', hav⟩ := exists_ball_avoiding_cells T.complex p
  let q := AffineMap.lineMap p v (-1 : ℝ)
  obtain ⟨t, ht, _, hxt⟩ := exists_small_line_step p q (lt_min hr hr')
  let x := AffineMap.lineMap p q t
  have hxball : x ∈ Metric.ball p r := Metric.ball_subset_ball (min_le_left _ _) hxt
  have hxball' : x ∈ Metric.ball p r' := Metric.ball_subset_ball (min_le_right _ _) hxt
  have hpSpan : p ∈ affineSpan ℝ (Set.range S.points) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) _ (cellHull_subset_simplexHull T hFcell hp)
  have hvSpan : v ∈ affineSpan ℝ (Set.range S.points) := by
    rw [← topCell_affineSpan T hC]
    exact mem_affineSpan ℝ (hCv ▸ Finset.mem_insert_self _ _)
  have hqSpan : q ∈ affineSpan ℝ (Set.range S.points) := AffineMap.lineMap_mem (-1 : ℝ) hpSpan hvSpan
  have hxSpan : x ∈ affineSpan ℝ (Set.range S.points) := AffineMap.lineMap_mem t hpSpan hqSpan
  have hxS : x ∈ simplexHull S := (e.hull_iff hxSpan).mpr
    (fun i => (Set.mem_iInter.mp (hrO hxball) i).le)
  have hxK : x ∈ complexSupport T.complex := by
    have hcov : complexSupport T.complex = simplexHull S := T.covers
    rwa [hcov]
  obtain ⟨D, hxD⟩ := Set.mem_iUnion.mp hxK
  obtain ⟨hD, hxD⟩ := Set.mem_iUnion.mp hxD
  have hpD : p ∈ cellHull D := by
    by_contra hnot
    exact Set.disjoint_left.mp (hav D hD hnot) hxball' hxD
  have hFD := hdetect D hD hpD
  obtain ⟨E, hE, hDE⟩ := exists_topCell_superset T hD
  have hFE : F ⊆ E := hFD.trans hDE
  have hxE : x ∈ cellHull E := cellHull_mono hDE hxD
  let vi : C := ⟨v, hCv ▸ Finset.mem_insert_self _ _⟩
  have hcp : c.coord vi p = 0 := affine_zero_on_span _ (c.zero_on_facet hv hCv)
    (convexHull_subset_affineSpan (𝕜 := ℝ) _ hp)
  have hcv : c.coord vi v = 1 := by simpa only [ite_true] using c.on_vertex vi vi
  have hcq : c.coord vi q = -1 := by
    dsimp only [q]
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hcp, hcv]
    norm_num
  have hcx : c.coord vi x < 0 := by
    dsimp only [x]
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hcp, hcq]
    nlinarith
  have hCE : C ≠ E := by
    intro heq
    have hnonneg := c.nonneg (heq ▸ hxE) vi
    linarith
  exact Finset.one_lt_card.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, hFC⟩,
    E, Finset.mem_filter.mpr ⟨hE, hFE⟩, hCE⟩

/-- Internal facets have exactly two actual incident top cells. -/
theorem internal_facet_incidence :
    Specs.D10Topology.Ch17.FacetIncidence.internal_facet_incidence := by
  intro m n S T _ F hF
  exact Nat.le_antisymm
    (incidentTopCells_card_le_two T (Finset.mem_sdiff.mp hF).1)
    (internal_facet_two_le_incidence T hF)

end D10Topology.Ch17
