import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.BarycentricSubdivision
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.SimplexTriangulation
import Mathlib.Analysis.SpecificLimits.Basic

/-! Barycentric subdivision of finite geometric complexes and arbitrarily fine
face-compatible triangulations of affine simplexes (`d10:17:subdivision`). -/
noncomputable section
open Set
open scoped BigOperators Topology
namespace D10Topology.Ch17
namespace Subdivision
open Specs.D10Topology.Ch17.BarycentricSubdivision

abbrev FaceCompatible : FaceCompatibleType := @FaceCompatibleValue
abbrev faceMean : faceMeanType := @faceMeanValue

theorem faceMean_mem {m : ℕ} (F : Finset (Euclidean m)) (hF : F.Nonempty) :
    faceMean F ∈ cellHull F := by
  apply F.centerMass_id_mem_convexHull (fun _ _ => zero_le_one)
  simpa using (Nat.cast_pos.mpr hF.card_pos : (0 : ℝ) < F.card)

theorem faceMean_card_smul {m : ℕ} (F : Finset (Euclidean m)) (hF : F.Nonempty) :
    (F.card : ℝ) • faceMean F = ∑ x ∈ F, x := by
  change (F.card : ℝ) • F.centerMass (fun _ => (1 : ℝ)) id = _
  simp only [Finset.centerMass, Finset.sum_const, nsmul_eq_mul, mul_one,
    one_smul, id_eq, smul_smul]
  rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hF.card_pos.ne'), one_smul]

/-- The sum of differences from the smaller face's mean only involves the
new vertices. No independence assumption is needed for this metric identity. -/
theorem faceMean_difference_sum {m : ℕ} (F G : Finset (Euclidean m))
    (hF : F.Nonempty) (hFG : F ⊆ G) :
    (G.card : ℝ) • (faceMean G - faceMean F) =
      ∑ x ∈ G \ F, (x - faceMean F) := by
  classical
  have hG := hF.mono hFG
  have hc := congrArg (fun k : ℕ => (k : ℝ)) (Finset.card_sdiff_add_card_eq_card hFG)
  simp only [Nat.cast_add] at hc
  have hs : (∑ x ∈ G \ F, x) + ∑ x ∈ F, x = ∑ x ∈ G, x :=
    Finset.sum_sdiff hFG
  rw [smul_sub, faceMean_card_smul G hG, ← hs,
    Finset.sum_sub_distrib, Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [← faceMean_card_smul F hF]
  rw [← hc, add_smul]
  module

theorem nested_faceMean_dist :
    Specs.D10Topology.Ch17.BarycentricSubdivision.nested_faceMean_dist := by
  intro m F G hF hFG
  have hG := hF.mono hFG
  have hg : (0 : ℝ) < G.card := Nat.cast_pos.mpr hG.card_pos
  have hc := congrArg (fun k : ℕ => (k : ℝ)) (Finset.card_sdiff_add_card_eq_card hFG)
  simp only [Nat.cast_add] at hc
  have hnorm : (G.card : ℝ) * ‖faceMean G - faceMean F‖ ≤
      (↑(G \ F).card : ℝ) * cellDiameter G := by
    calc
      _ = ‖(G.card : ℝ) • (faceMean G - faceMean F)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hg]
      _ = ‖∑ x ∈ G \ F, (x - faceMean F)‖ := by rw [faceMean_difference_sum F G hF hFG]
      _ ≤ ∑ x ∈ G \ F, ‖x - faceMean F‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ G \ F, cellDiameter G := by
        apply Finset.sum_le_sum
        intro x hx
        rw [← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem (cellHull_bounded G)
          (subset_convexHull ℝ _ (Finset.mem_sdiff.mp hx).1)
          (cellHull_mono hFG (faceMean_mem F hF))
      _ = _ := by simp
  rw [dist_comm, dist_eq_norm]
  apply (mul_le_mul_iff_right₀ hg).mp
  calc
    (G.card : ℝ) * ‖faceMean G - faceMean F‖ ≤
        (↑(G \ F).card : ℝ) * cellDiameter G := hnorm
    _ = (G.card : ℝ) * ((1 - (F.card : ℝ) / (G.card : ℝ)) * cellDiameter G) := by
      have hc' : (↑(G \ F).card : ℝ) = (G.card : ℝ) - F.card := by linarith
      rw [hc']
      field_simp

theorem nested_faceMean_contraction :
    Specs.D10Topology.Ch17.BarycentricSubdivision.nested_faceMean_contraction := by
  intro m n F G hF hFG hcard
  have hG := hF.mono hFG
  have hg : (0 : ℝ) < G.card := Nat.cast_pos.mpr hG.card_pos
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ha : (1 : ℝ) ≤ F.card := by exact_mod_cast hF.card_pos
  have hb : (G.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
  have hratio : 1 / ((n : ℝ) + 1) ≤ (F.card : ℝ) / (G.card : ℝ) :=
    (one_div_le_one_div_of_le hg hb).trans (div_le_div_of_nonneg_right ha hg.le)
  have hcoeff : 1 - (F.card : ℝ) / (G.card : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
    calc
      _ ≤ 1 - 1 / ((n : ℝ) + 1) := sub_le_sub_left hratio 1
      _ = _ := by field_simp; ring
  exact (nested_faceMean_dist F G hF hFG).trans
    (mul_le_mul_of_nonneg_right hcoeff Metric.diam_nonneg)

theorem mesh_nonneg {m : ℕ} (K : GeometricComplex m) : 0 ≤ mesh K := by
  obtain ⟨s, _, hs⟩ := mesh_attained K
  rw [hs]
  exact Metric.diam_nonneg

theorem barycentric_cell_diameter :
    Specs.D10Topology.Ch17.BarycentricSubdivision.barycentric_cell_diameter := by
  intro m n K hcard C hC
  have hq : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  change cellDiameter (C.image faceMean) ≤ _
  rw [cellDiameter_eq_vertex_diameter]
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg hq (mesh_nonneg K))
  intro x hx y hy
  obtain ⟨F, hFC, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨G, hGC, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hFK, hF⟩ := hC.1 F hFC
  obtain ⟨hGK, hG⟩ := hC.1 G hGC
  by_cases hFG : F = G
  · subst G
    simpa using mul_nonneg hq (mesh_nonneg K)
  obtain hsub | hsub := hC.2 hFC hGC hFG
  · exact (nested_faceMean_contraction F G hF hsub (hcard G hGK)).trans
      (mul_le_mul_of_nonneg_left (cellDiameter_le_mesh K G hGK) hq)
  · rw [dist_comm]
    exact (nested_faceMean_contraction G F hG hsub (hcard F hFK)).trans
      (mul_le_mul_of_nonneg_left (cellDiameter_le_mesh K F hFK) hq)

theorem triangulation_cell_card_le {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) (s : Finset (Euclidean m)) (hs : s ∈ T.complex.cells) :
    s.card ≤ n + 1 := by
  classical
  obtain ⟨t, ht, hmax⟩ := (T.complex.cells.filter (fun t => s ⊆ t)).exists_max_image
    Finset.card ⟨s, Finset.mem_filter.mpr ⟨hs, Finset.Subset.refl _⟩⟩
  obtain ⟨htK, hst⟩ := Finset.mem_filter.mp ht
  have htm : t ∈ maximalCells T.complex := by
    apply Finset.mem_filter.mpr
    refine ⟨htK, ?_⟩
    intro u hu htu
    exact Finset.eq_of_subset_of_card_le htu
      (hmax u (Finset.mem_filter.mpr ⟨hu, hst.trans htu⟩))
  exact (Finset.card_le_card hst).trans (T.pure t htm).le

theorem barycentric_mesh_contraction :
    Specs.D10Topology.Ch17.BarycentricSubdivision.barycentric_mesh_contraction := by
  classical
  intro m n S T L hL
  obtain ⟨s, hs, heq⟩ := mesh_attained L
  change mesh L ≤ (n : ℝ) / ((n : ℝ) + 1) * mesh T.complex
  rw [heq]
  rw [hL] at hs
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hs
  exact barycentric_cell_diameter T.complex (triangulation_cell_card_le T) C
    (Finset.mem_filter.mp hC).2

theorem originalVertices_coe {m n : ℕ} (S : AffineSimplex m n) :
    (originalVertices S : Set (Euclidean m)) = Set.range S.points := by
  simp [originalVertices]

theorem originalVertices_independent {m n : ℕ} (S : AffineSimplex m n) :
    AffineIndependent ℝ ((↑) : originalVertices S → Euclidean m) := by
  change AffineIndependent ℝ (fun x : (originalVertices S : Set (Euclidean m)) => (x : Euclidean m))
  rw [originalVertices_coe]
  exact S.independent.range

/-- The unsubdivided simplex and all its faces form a genuine finite geometric
complex. In particular its intersection axiom is proved for convex hulls. -/
def originalComplex {m n : ℕ} (S : AffineSimplex m n) : GeometricComplex m where
  cells := (originalVertices S).powerset
  empty_mem := Finset.mem_powerset.mpr (Finset.empty_subset _)
  independent := by
    intro s hs
    exact (originalVertices_independent S).mono (Finset.mem_powerset.mp hs)
  face_closed := by
    intro s hs t ht
    exact Finset.mem_powerset.mpr (ht.trans (Finset.mem_powerset.mp hs))
  inter_eq := by
    intro s hs t ht
    change convexHull ℝ (s : Set (Euclidean m)) ∩ convexHull ℝ (t : Set (Euclidean m)) = _
    rw [← (originalVertices_independent S).convexHull_inter
      (Finset.mem_powerset.mp hs) (Finset.mem_powerset.mp ht)]
    rw [← Finset.coe_inter]
    rfl

theorem originalComplex_support {m n : ℕ} (S : AffineSimplex m n) :
    complexSupport (originalComplex S) = simplexHull S := by
  have hv : cellHull (originalVertices S) = simplexHull S := by
    change convexHull ℝ (originalVertices S : Set (Euclidean m)) = _
    rw [originalVertices_coe]
    rfl
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [← hv]
    exact cellHull_mono (Finset.mem_powerset.mp hs) hx
  · rw [← hv]
    exact Set.subset_iUnion₂_of_subset (originalVertices S)
      (Finset.mem_powerset.mpr (Finset.Subset.refl _)) (Set.Subset.refl _)

theorem originalComplex_maximal {m n : ℕ} (S : AffineSimplex m n)
    (s : Finset (Euclidean m)) :
    s ∈ maximalCells (originalComplex S) ↔ s = originalVertices S := by
  change s ∈ (originalVertices S).powerset.filter _ ↔ _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hs, h⟩
    exact h _ (Finset.mem_powerset.mpr (Finset.Subset.refl _))
      (Finset.mem_powerset.mp hs)
  · rintro rfl
    refine ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_⟩
    intro t ht hst
    exact Finset.Subset.antisymm hst (Finset.mem_powerset.mp ht)

def originalTriangulation {m n : ℕ} (S : AffineSimplex m n) : Triangulation S where
  complex := originalComplex S
  covers := originalComplex_support S
  pure := by
    intro s hs
    rw [(originalComplex_maximal S s).mp hs]
    simp only [originalVertices, Finset.card_image_of_injective _ S.independent.injective,
      Finset.card_univ, Fintype.card_fin]

theorem originalFace_hull {m n : ℕ} (S : AffineSimplex m n)
    (I : Finset (Fin (n + 1))) : cellHull (I.image S.points) = simplexFace S I := by
  change convexHull ℝ (↑(I.image S.points) : Set (Euclidean m)) = _
  rw [Finset.coe_image]
  rfl

theorem originalFace_subset {m n : ℕ} (S : AffineSimplex m n)
    (I : Finset (Fin (n + 1))) : I.image S.points ⊆ originalVertices S :=
  Finset.image_subset_image (Finset.subset_univ _)

theorem original_induced_cells {m n : ℕ} (S : AffineSimplex m n)
    (I : Finset (Fin (n + 1))) :
    (inducedComplex (originalTriangulation S) I).cells = (I.image S.points).powerset := by
  ext s
  rw [inducedComplex_cells, inducedCells_iff, Finset.mem_powerset]
  change (s ∈ (originalComplex S).cells ∧ cellHull s ⊆ simplexFace S I) ↔ _
  constructor
  · rintro ⟨hs, hsub⟩
    apply (face_iff_hull_subset (originalComplex S) s (I.image S.points) hs
      (Finset.mem_powerset.mpr (originalFace_subset S I))).mpr
    rwa [originalFace_hull]
  · intro hs
    exact ⟨Finset.mem_powerset.mpr (hs.trans (originalFace_subset S I)),
      (cellHull_mono hs).trans (originalFace_hull S I).le⟩

/-- Any complex whose cells are exactly all subsets of V realizes hull(V). -/
theorem support_of_powerset {m : ℕ} (K : GeometricComplex m)
    (V : Finset (Euclidean m)) (hK : K.cells = V.powerset) :
    complexSupport K = cellHull V := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [hK] at hs
    exact cellHull_mono (Finset.mem_powerset.mp hs) hx
  · exact Set.subset_iUnion₂_of_subset V
      (hK.symm ▸ Finset.mem_powerset.mpr (Finset.Subset.refl _)) (Set.Subset.refl _)

theorem maximal_of_powerset {m : ℕ} (K : GeometricComplex m)
    (V : Finset (Euclidean m)) (hK : K.cells = V.powerset)
    (s : Finset (Euclidean m)) : s ∈ maximalCells K ↔ s = V := by
  change s ∈ K.cells.filter _ ↔ _
  simp only [Finset.mem_filter, hK, Finset.mem_powerset]
  constructor
  · rintro ⟨hs, h⟩
    exact h V (Finset.Subset.refl _) hs
  · rintro rfl
    exact ⟨Finset.Subset.refl _, fun t ht hV => Finset.Subset.antisymm hV ht⟩

theorem original_faceCompatible {m n : ℕ} (S : AffineSimplex m n) :
    FaceCompatible (originalTriangulation S) := by
  intro I
  constructor
  · change complexSupport (inducedComplex (originalTriangulation S) I) = simplexFace S I
    rw [support_of_powerset _ _ (original_induced_cells S I), originalFace_hull]
  · intro s hs
    rw [(maximal_of_powerset _ _ (original_induced_cells S I) s).mp hs]
    exact Finset.card_image_of_injective I S.independent.injective

theorem original_mesh {m n : ℕ} (S : AffineSimplex m n) :
    mesh (originalComplex S) = Metric.diam (simplexHull S) := by
  have hv : cellHull (originalVertices S) = simplexHull S := by
    change convexHull ℝ (originalVertices S : Set (Euclidean m)) = _
    rw [originalVertices_coe]
    rfl
  apply le_antisymm
  · obtain ⟨s, hs, heq⟩ := mesh_attained (originalComplex S)
    rw [heq, ← hv]
    exact Metric.diam_mono (cellHull_mono (Finset.mem_powerset.mp hs))
      (cellHull_bounded _)
  · rw [← hv]
    exact cellDiameter_le_mesh (originalComplex S) _
      (Finset.mem_powerset.mpr (Finset.Subset.refl _))

theorem initial_triangulation :
    Specs.D10Topology.Ch17.BarycentricSubdivision.initial_triangulation := by
  intro m n S
  exact ⟨originalTriangulation S, rfl, original_faceCompatible S, original_mesh S⟩

theorem zero_dimensional_fine_triangulations :
    Specs.D10Topology.Ch17.BarycentricSubdivision.zero_dimensional_fine_triangulations := by
  intro m S
  have hV : originalVertices S = {S.points 0} := by
    ext x
    simp only [originalVertices, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      congr 1
      apply Fin.ext
      omega
    · rintro rfl
      exact ⟨0, rfl⟩
  have hzero : mesh (originalComplex S) = 0 := by
    rw [original_mesh]
    change Metric.diam (convexHull ℝ (Set.range S.points)) = 0
    rw [← originalVertices_coe, hV, Finset.coe_singleton, convexHull_singleton,
      Metric.diam_singleton]
  refine ⟨fun _ => originalTriangulation S, fun _ => original_faceCompatible S,
    fun _ => hzero, ?_⟩
  simpa only [show (originalTriangulation S).complex = originalComplex S from rfl, hzero]
    using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))

/-- The affine-coordinate description of the mean uses the literal vertex
subtype, so it works for a simplex in any ambient dimension. -/
theorem faceMean_eq_affineCombination {m : ℕ} (F : Finset (Euclidean m))
    (hF : F.Nonempty) :
    faceMean F = Finset.univ.affineCombination ℝ ((↑) : F → Euclidean m)
      (fun _ => (F.card : ℝ)⁻¹) := by
  have hc : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF.card_pos.ne'
  have hw : ∑ _x : F, (F.card : ℝ)⁻¹ = 1 := by simp [hc]
  rw [affineCombination_eq_centerMass hw, Finset.centerMass_eq_of_sum_1 _ _ hw]
  change F.centerMass (fun _ => (1 : ℝ)) id = _
  simp only [Finset.centerMass, Finset.sum_const, nsmul_eq_mul, mul_one,
    one_smul, id_eq, ← Finset.smul_sum]
  congr 1
  simpa only [id_eq] using (Finset.sum_coe_sort F id).symm

/-- A mean has a nonzero affine coordinate at every vertex of its face.
Consequently it cannot lie in the affine span of a proper subface. -/
theorem faceMean_mem_affineSpan_iff {m : ℕ} (F G : Finset (Euclidean m))
    (hF : F.Nonempty) (hG : G ⊆ F)
    (hind : AffineIndependent ℝ ((↑) : F → Euclidean m)) :
    faceMean F ∈ affineSpan ℝ (G : Set (Euclidean m)) ↔ G = F := by
  classical
  constructor
  · intro hm
    apply Finset.Subset.antisymm hG
    intro x hx
    by_contra hxG
    let J : Set F := {x | (x : Euclidean m) ∈ G}
    have hJ : ((↑) : F → Euclidean m) '' J = (G : Set (Euclidean m)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hG hy⟩, hy, rfl⟩
    have hc : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF.card_pos.ne'
    have hw : ∑ _x : F, (F.card : ℝ)⁻¹ = 1 := by simp [hc]
    rw [faceMean_eq_affineCombination F hF, ← hJ] at hm
    have hz := hind.eq_zero_of_affineCombination_mem_affineSpan hw hm
      (Finset.mem_univ (⟨x, hx⟩ : F)) hxG
    exact (inv_ne_zero hc) hz
  · intro h
    subst G
    exact convexHull_subset_affineSpan (F : Set (Euclidean m)) (faceMean_mem F hF)

/-- A nonempty finite inclusion chain has a greatest member. -/
theorem inclusionChain_greatest {α : Type*} (C : Finset (Finset α))
    (hne : C.Nonempty)
    (hchain : (C : Set (Finset α)).Pairwise (fun F G => F ⊆ G ∨ G ⊆ F)) :
    ∃ G ∈ C, ∀ F ∈ C, F ⊆ G := by
  obtain ⟨G, hG, hmax⟩ := C.exists_max_image Finset.card hne
  refine ⟨G, hG, ?_⟩
  intro F hF
  by_cases heq : F = G
  · exact heq ▸ Finset.Subset.refl F
  rcases hchain hF hG heq with hFG | hGF
  · exact hFG
  · exact (Finset.eq_of_subset_of_card_le hGF (hmax F hF)).symm.subset

/-- The barycentres in an inclusion chain are affinely independent.
The proof successively removes its greatest face. The other barycentres
lie in the span of a proper subface, whereas the removed mean does not. -/
theorem chain_faceMean_affineIndepOn {m : ℕ}
    (C : Finset (Finset (Euclidean m)))
    (hne : ∀ F ∈ C, F.Nonempty)
    (hind : ∀ F ∈ C, AffineIndependent ℝ ((↑) : F → Euclidean m))
    (hchain : (C : Set (Finset (Euclidean m))).Pairwise
      (fun F G => F ⊆ G ∨ G ⊆ F)) :
    AffineIndepOn ℝ faceMean (C : Set (Finset (Euclidean m))) := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    rcases C.eq_empty_or_nonempty with hC | hC
    · subst C
      simpa only [Finset.coe_empty] using (affineIndepOn_empty ℝ (faceMean (m := m)))
    obtain ⟨G, hGC, hmax⟩ := inclusionChain_greatest C hC hchain
    have herase : (C.erase G : Set (Finset (Euclidean m))) ⊆ C :=
      Finset.erase_subset G C
    have hsmall := ih (C.erase G) (Finset.erase_ssubset hGC)
      (fun F hF => hne F (herase hF))
      (fun F hF => hind F (herase hF)) (hchain.mono herase)
    have hnot : faceMean G ∉
        affineSpan ℝ (faceMean '' (C.erase G : Set (Finset (Euclidean m)))) := by
      rcases (C.erase G).eq_empty_or_nonempty with he | he
      · simpa [he] using (AffineSubspace.notMem_bot ℝ (Euclidean m) (faceMean G))
      obtain ⟨H, hHC, hHmax⟩ := inclusionChain_greatest (C.erase G) he (hchain.mono herase)
      have hHG : H ⊆ G := hmax H (herase hHC)
      have hHGne : H ≠ G := (Finset.mem_erase.mp hHC).1
      have hle : affineSpan ℝ (faceMean '' (C.erase G : Set (Finset (Euclidean m)))) ≤
          affineSpan ℝ (H : Set (Euclidean m)) := by
        apply affineSpan_le_of_subset_coe
        rintro x ⟨F, hF, rfl⟩
        exact convexHull_subset_affineSpan _
          (cellHull_mono (hHmax F hF) (faceMean_mem F (hne F (herase hF))))
      intro hm
      exact hHGne ((faceMean_mem_affineSpan_iff G H (hne G hGC) hHG
        (hind G hGC)).mp (hle hm))
    have hi := hsmall.insert hnot
    simpa only [← Finset.coe_insert, Finset.insert_erase hGC] using hi

/-- In a geometric complex, every barycentric chain gives an actual simplex,
including the empty cell. -/
theorem faceChain_independent {m : ℕ} (K : GeometricComplex m)
    (C : Finset (Finset (Euclidean m))) (hC : FaceChain K C) :
    AffineIndependent ℝ ((↑) : C.image faceMean → Euclidean m) := by
  have hi := chain_faceMean_affineIndepOn C (fun F hF => (hC.1 F hF).2)
    (fun F hF => K.independent F (hC.1 F hF).1) hC.2
  change AffineIndepOn ℝ id (C.image faceMean : Set (Euclidean m))
  rw [Finset.coe_image]
  exact hi.id_image


/-- A barycentre of an old face lies in another old cell precisely when its
whole face is contained there. This uses the geometric intersection axiom. -/
theorem faceMean_mem_cellHull_iff {m : ℕ} (K : GeometricComplex m)
    (F G : Finset (Euclidean m)) (hFK : F ∈ K.cells) (hF : F.Nonempty)
    (hGK : G ∈ K.cells) : faceMean F ∈ cellHull G ↔ F ⊆ G := by
  constructor
  · intro hm
    have hboth : faceMean F ∈ cellHull (F ∩ G) := by
      have hi : cellHull F ∩ cellHull G = cellHull (F ∩ G) := K.inter_eq F hFK G hGK
      rw [← hi]
      exact ⟨faceMean_mem F hF, hm⟩
    have heq := (faceMean_mem_affineSpan_iff F (F ∩ G) hF Finset.inter_subset_left
      (K.independent F hFK)).mp (convexHull_subset_affineSpan _ hboth)
    rw [← heq]
    exact Finset.inter_subset_right
  · intro hFG
    exact cellHull_mono hFG (faceMean_mem F hF)

/-- Different nonempty old cells have different barycentres. -/
theorem faceMean_injective {m : ℕ} (K : GeometricComplex m) :
    Set.InjOn faceMean {F | F ∈ K.cells ∧ F.Nonempty} := by
  intro F hF G hG heq
  apply Finset.Subset.antisymm
  · apply (faceMean_mem_cellHull_iff K F G hF.1 hF.2 hG.1).mp
    rw [heq]
    exact faceMean_mem G hG.2
  · apply (faceMean_mem_cellHull_iff K G F hG.1 hG.2 hF.1).mp
    rw [← heq]
    exact faceMean_mem F hF.2

theorem mem_barycentricCells_iff {m : ℕ} (K : GeometricComplex m)
    (s : Finset (Euclidean m)) :
    s ∈ barycentricCells K ↔
      ∃ C : Finset (Finset (Euclidean m)), FaceChain K C ∧ C.image faceMean = s := by
  classical
  constructor
  · intro hs
    obtain ⟨C, hC, heq⟩ := Finset.mem_image.mp hs
    exact ⟨C, (Finset.mem_filter.mp hC).2, heq⟩
  · rintro ⟨C, hC, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hC⟩, rfl⟩
    intro F hF
    exact (hC.1 F hF).1

theorem faceChain_mono {m : ℕ} {K : GeometricComplex m}
    {C D : Finset (Finset (Euclidean m))} (hC : FaceChain K C) (hDC : D ⊆ C) :
    FaceChain K D :=
  ⟨fun F hF => hC.1 F (hDC hF), hC.2.mono hDC⟩

theorem barycentricCells_empty_mem {m : ℕ} (K : GeometricComplex m) :
    ∅ ∈ barycentricCells K := by
  rw [mem_barycentricCells_iff]
  refine ⟨∅, ?_, Finset.image_empty _⟩
  constructor
  · simp
  · simp

theorem barycentricCells_independent {m : ℕ} (K : GeometricComplex m)
    (s : Finset (Euclidean m)) (hs : s ∈ barycentricCells K) :
    AffineIndependent ℝ ((↑) : s → Euclidean m) := by
  obtain ⟨C, hC, rfl⟩ := (mem_barycentricCells_iff K s).mp hs
  exact faceChain_independent K C hC

/-- Every face of a raw barycentric cell is another raw barycentric cell. -/
theorem barycentricCells_face_closed {m : ℕ} (K : GeometricComplex m)
    (s : Finset (Euclidean m)) (hs : s ∈ barycentricCells K)
    (t : Finset (Euclidean m)) (ht : t ⊆ s) : t ∈ barycentricCells K := by
  classical
  obtain ⟨C, hC, rfl⟩ := (mem_barycentricCells_iff K s).mp hs
  let D := C.filter (fun F => faceMean F ∈ t)
  apply (mem_barycentricCells_iff K t).mpr
  refine ⟨D, faceChain_mono hC (Finset.filter_subset _ _), ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hF).2
  · intro hx
    obtain ⟨F, hFC, rfl⟩ := Finset.mem_image.mp (ht hx)
    exact Finset.mem_image.mpr ⟨F, Finset.mem_filter.mpr ⟨hFC, hx⟩, rfl⟩


/-- A finite chain of nonempty subsets of V extends to a full chain, with
one face for each positive cardinality up to |V|. -/
theorem exists_saturated_faceChain {α : Type*} [DecidableEq α]
    (V : Finset α) (C : Finset (Finset α))
    (hsub : ∀ F ∈ C, F ⊆ V ∧ F.Nonempty)
    (hchain : (C : Set (Finset α)).Pairwise (fun F G => F ⊆ G ∨ G ⊆ F)) :
    ∃ D : Finset (Finset α), C ⊆ D ∧ D.card = V.card ∧
      (∀ F ∈ D, F ⊆ V ∧ F.Nonempty) ∧
      (D : Set (Finset α)).Pairwise (fun F G => F ⊆ G ∨ G ⊆ F) := by
  classical
  induction V using Finset.strongInductionOn generalizing C with
  | _ V ih =>
    rcases V.eq_empty_or_nonempty with hV | hV
    · subst V
      have hC : C = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro F hF
        have he := Finset.subset_empty.mp (hsub F hF).1
        exact (hsub F hF).2.ne_empty he
      subst C
      exact ⟨∅, Finset.Subset.refl _, rfl, by simp, by simp⟩
    have hx : ∃ x ∈ V, ∀ F ∈ C.erase V, x ∉ F := by
      rcases (C.erase V).eq_empty_or_nonempty with he | he
      · obtain ⟨x, hx⟩ := hV
        exact ⟨x, hx, by simp [he]⟩
      obtain ⟨H, hHC, hHmax⟩ := inclusionChain_greatest (C.erase V) he
        (hchain.mono (Finset.erase_subset _ _))
      have hHV := (hsub H (Finset.mem_of_mem_erase hHC)).1
      have hne : H ≠ V := (Finset.mem_erase.mp hHC).1
      obtain ⟨x, hxV, hxH⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hHV hne)
      exact ⟨x, hxV, fun F hF hxF => hxH (hHmax F hF hxF)⟩
    obtain ⟨x, hxV, hx⟩ := hx
    have hC' : ∀ F ∈ C.erase V, F ⊆ V.erase x ∧ F.Nonempty := by
      intro F hF
      refine ⟨?_, (hsub F (Finset.mem_of_mem_erase hF)).2⟩
      intro y hy
      apply Finset.mem_erase.mpr
      exact ⟨fun hyx => hx F hF (hyx ▸ hy),
        (hsub F (Finset.mem_of_mem_erase hF)).1 hy⟩
    obtain ⟨D, hCD, hcard, hD, hDchain⟩ := ih (V.erase x) (Finset.erase_ssubset hxV)
      (C.erase V) hC' (hchain.mono (Finset.erase_subset _ _))
    have hVD : V ∉ D := by
      intro h
      exact (Finset.notMem_erase x V) ((hD V h).1 hxV)
    refine ⟨insert V D, ?_, ?_, ?_, ?_⟩
    · intro F hF
      by_cases he : F = V
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (hCD (Finset.mem_erase.mpr ⟨he, hF⟩))
    · rw [Finset.card_insert_of_notMem hVD, hcard, Finset.card_erase_of_mem hxV]
      have hp := hV.card_pos
      omega
    · intro F hF
      rcases Finset.mem_insert.mp hF with rfl | hF
      · exact ⟨Finset.Subset.refl _, hV⟩
      · exact ⟨(hD F hF).1.trans (Finset.erase_subset _ _), (hD F hF).2⟩
    · intro F hF G hG hne
      rcases Finset.mem_insert.mp hF with heF | hFD
      · subst F
        rcases Finset.mem_insert.mp hG with heG | hGD
        · exact (hne heG.symm).elim
        · exact Or.inr ((hD G hGD).1.trans (Finset.erase_subset _ _))
      · rcases Finset.mem_insert.mp hG with heG | hGD
        · subst G
          exact Or.inl ((hD F hFD).1.trans (Finset.erase_subset _ _))
        · exact hDchain hFD hGD hne


/-- Each chain has a carrier in the old complex. -/
theorem faceChain_carrier {m : ℕ} (K : GeometricComplex m)
    (C : Finset (Finset (Euclidean m))) (hC : FaceChain K C) :
    ∃ G ∈ K.cells, ∀ F ∈ C, F ⊆ G := by
  rcases C.eq_empty_or_nonempty with he | he
  · exact ⟨∅, K.empty_mem, by simp [he]⟩
  obtain ⟨G, hG, hmax⟩ := inclusionChain_greatest C he hC.2
  exact ⟨G, (hC.1 G hG).1, hmax⟩

theorem cell_subset_maximal {m : ℕ} (K : GeometricComplex m)
    (s : Finset (Euclidean m)) (hs : s ∈ K.cells) :
    ∃ t ∈ maximalCells K, s ⊆ t := by
  classical
  obtain ⟨t, ht, hmax⟩ := (K.cells.filter (fun t => s ⊆ t)).exists_max_image
    Finset.card ⟨s, Finset.mem_filter.mpr ⟨hs, Finset.Subset.refl _⟩⟩
  obtain ⟨htK, hst⟩ := Finset.mem_filter.mp ht
  refine ⟨t, Finset.mem_filter.mpr ⟨htK, ?_⟩, hst⟩
  intro u hu htu
  exact Finset.eq_of_subset_of_card_le htu
    (hmax u (Finset.mem_filter.mpr ⟨hu, hst.trans htu⟩))

/-- Purity is preserved by the raw barycentric construction, independently of
the still separate geometric covering and intersection obligations. -/
theorem barycentricCells_pure {m N : ℕ} (K : GeometricComplex m)
    (hpure : ∀ t ∈ maximalCells K, t.card = N)
    (s : Finset (Euclidean m)) (hs : s ∈ barycentricCells K)
    (hmax : ∀ t ∈ barycentricCells K, s ⊆ t → s = t) : s.card = N := by
  classical
  obtain ⟨C, hC, rfl⟩ := (mem_barycentricCells_iff K s).mp hs
  obtain ⟨G, hGK, hCG⟩ := faceChain_carrier K C hC
  obtain ⟨V, hVK, hGV⟩ := cell_subset_maximal K G hGK
  have hVcell : V ∈ K.cells := (Finset.mem_filter.mp hVK).1
  obtain ⟨D, hCD, hDcard, hDsub, hDchain⟩ := exists_saturated_faceChain V C
    (fun F hF => ⟨(hCG F hF).trans hGV, (hC.1 F hF).2⟩) hC.2
  have hDK : FaceChain K D :=
    ⟨fun F hF => ⟨K.face_closed V hVcell F (hDsub F hF).1, (hDsub F hF).2⟩, hDchain⟩
  have heq := hmax (D.image faceMean)
    ((mem_barycentricCells_iff K _).mpr ⟨D, hDK, rfl⟩) (Finset.image_subset_image hCD)
  rw [heq]
  have hinj : Set.InjOn faceMean (D : Set (Finset (Euclidean m))) :=
    (chain_faceMean_affineIndepOn D (fun F hF => (hDK.1 F hF).2)
      (fun F hF => K.independent F (hDK.1 F hF).1) hDK.2).injOn
  rw [Finset.card_image_of_injOn hinj, hDcard, hpure V hVK]


/-- Local coverage by barycentric chains. Subtract the least old vertex
coordinate, normalize the remainder on a proper face, and induct. No affine
independence is needed for this covering statement. -/
theorem exists_chain_cell_containing {m : ℕ} (V : Finset (Euclidean m))
    (x : Euclidean m) (hx : x ∈ cellHull V) :
    ∃ C : Finset (Finset (Euclidean m)),
      (∀ F ∈ C, F ⊆ V ∧ F.Nonempty) ∧
      (C : Set (Finset (Euclidean m))).Pairwise (fun F G => F ⊆ G ∨ G ⊆ F) ∧
      x ∈ cellHull (C.image faceMean) := by
  classical
  induction V using Finset.strongInductionOn generalizing x with
  | _ V ih =>
    have hV : V.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [he, cellHull, Specs.D10Topology.Ch17.SimplexTriangulation.cellHullValue,
        Specs.D10Topology.Ch17.SimplexTriangulation.cellHull] at hx
    obtain ⟨w, hw₀, hw₁, hwx⟩ := Finset.mem_convexHull'.mp hx
    obtain ⟨a, ha, hmin⟩ := V.exists_min_image w hV
    let δ := w a
    let r := 1 - (V.card : ℝ) * δ
    have hδ : 0 ≤ δ := hw₀ a ha
    have hres : ∀ v ∈ V, 0 ≤ w v - δ := fun v hv => sub_nonneg.mpr (hmin v hv)
    have hsumres : ∑ v ∈ V, (w v - δ) = r := by
      simp only [Finset.sum_sub_distrib, hw₁, Finset.sum_const, nsmul_eq_mul]
      rfl
    have hr : 0 ≤ r := hsumres ▸ Finset.sum_nonneg hres
    by_cases hrzero : r = 0
    · have hz : ∀ v ∈ V, w v - δ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hres).mp (hsumres.trans hrzero)
      have hδone : δ * (V.card : ℝ) = 1 := by dsimp [r] at hrzero; linarith
      have heq : x = faceMean V := by
        calc
          x = ∑ v ∈ V, δ • v := by
            rw [← hwx]
            apply Finset.sum_congr rfl
            intro v hv
            rw [sub_eq_zero.mp (hz v hv)]
          _ = δ • ((V.card : ℝ) • faceMean V) := by
            rw [faceMean_card_smul V hV, Finset.smul_sum]
          _ = faceMean V := by rw [smul_smul, hδone, one_smul]
      refine ⟨{V}, ?_, ?_, ?_⟩
      · intro F hF
        simpa only [Finset.mem_singleton.mp hF] using
          (show V ⊆ V ∧ V.Nonempty from ⟨Finset.Subset.refl _, hV⟩)
      · simp
      · rw [heq]
        exact subset_convexHull ℝ _ (by simp)
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
      let u : Euclidean m → ℝ := fun v => (w v - δ) / r
      have hua : u a = 0 := by simp [u, δ]
      have husum : ∑ v ∈ V.erase a, u v = 1 := by
        rw [Finset.sum_erase_eq_sub ha, hua, sub_zero]
        simp only [u, ← Finset.sum_div, hsumres, div_self hrzero]
      let y : Euclidean m := ∑ v ∈ V.erase a, u v • v
      have hy : y ∈ cellHull (V.erase a) := by
        apply Finset.mem_convexHull'.mpr
        exact ⟨u, fun v hv => div_nonneg (hres v (Finset.mem_of_mem_erase hv)) hr,
          husum, rfl⟩
      obtain ⟨D, hD, hDchain, hyD⟩ := ih (V.erase a) (Finset.erase_ssubset ha) y hy
      have hDsub : ∀ F ∈ D, F ⊆ V :=
        fun F hF => (hD F hF).1.trans (Finset.erase_subset _ _)
      have hDimage : D.image faceMean ⊆ (insert V D).image faceMean :=
        Finset.image_subset_image (Finset.subset_insert _ _)
      have hmean : faceMean V ∈ cellHull ((insert V D).image faceMean) :=
        subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨V, Finset.mem_insert_self _ _, rfl⟩)
      have hyE : y ∈ cellHull ((insert V D).image faceMean) := cellHull_mono hDimage hyD
      have hdecomp : ((V.card : ℝ) * δ) • faceMean V + r • y = x := by
        have hysum : r • y = ∑ v ∈ V, (w v - δ) • v := by
          dsimp [y]
          rw [Finset.smul_sum]
          have hzero : (w a - δ) • a = 0 := by simp [δ]
          have hsum : (∑ v ∈ V.erase a, (w v - δ) • v) =
              ∑ v ∈ V, (w v - δ) • v := by
            simpa only [hzero, sub_zero] using
              (Finset.sum_erase_eq_sub (f := fun v => (w v - δ) • v) ha)
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro v hv
          rw [smul_smul]
          congr 1
          dsimp [u]
          field_simp
        rw [mul_comm (V.card : ℝ) δ, mul_smul, faceMean_card_smul V hV,
          Finset.smul_sum, hysum, ← Finset.sum_add_distrib, ← hwx]
        apply Finset.sum_congr rfl
        intro v hv
        rw [← add_smul]
        congr 1
        ring
      refine ⟨insert V D, ?_, ?_, ?_⟩
      · intro F hF
        rcases Finset.mem_insert.mp hF with he | hFD
        · subst F
          exact ⟨Finset.Subset.refl _, hV⟩
        · exact ⟨hDsub F hFD, (hD F hFD).2⟩
      · intro F hF G hG hne
        rcases Finset.mem_insert.mp hF with heF | hFD
        · subst F
          rcases Finset.mem_insert.mp hG with heG | hGD
          · exact (hne heG.symm).elim
          · exact Or.inr (hDsub G hGD)
        · rcases Finset.mem_insert.mp hG with heG | hGD
          · subst G
            exact Or.inl (hDsub F hFD)
          · exact hDchain hFD hGD hne
      · rw [← hdecomp]
        exact (convex_convexHull ℝ _) hmean hyE (mul_nonneg (Nat.cast_nonneg _) hδ)
          hr (by dsimp [r]; ring)


/-- The raw barycentric cells have exactly the old geometric support. -/
theorem barycentricCells_support {m : ℕ} (K : GeometricComplex m) :
    (⋃ s ∈ barycentricCells K, cellHull s) = complexSupport K := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨C, hC, rfl⟩ := (mem_barycentricCells_iff K s).mp hs
    obtain ⟨G, hGK, hCG⟩ := faceChain_carrier K C hC
    have hsub : cellHull (C.image faceMean) ⊆ cellHull G := by
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      obtain ⟨F, hFC, rfl⟩ := Finset.mem_image.mp hy
      exact cellHull_mono (hCG F hFC) (faceMean_mem F (hC.1 F hFC).2)
    exact Set.mem_iUnion₂.mpr ⟨G, hGK, hsub hx⟩
  · intro x hx
    obtain ⟨V, hVK, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨C, hCsub, hCchain, hxC⟩ := exists_chain_cell_containing V x hx
    have hC : FaceChain K C :=
      ⟨fun F hFC => ⟨K.face_closed V hVK F (hCsub F hFC).1, (hCsub F hFC).2⟩,
        hCchain⟩
    exact Set.mem_iUnion₂.mpr ⟨C.image faceMean,
      (mem_barycentricCells_iff K _).mpr ⟨C, hC, rfl⟩, hxC⟩

/-- An old mean belongs to an original face exactly when all its old vertices
do, provided the old induced triangulation covers that face. -/
theorem faceMean_mem_originalFace_iff {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) (hT : FaceCompatible T)
    (I : Finset (Fin (n + 1))) (F : Finset (Euclidean m))
    (hFK : F ∈ T.complex.cells) (hF : F.Nonempty) :
    faceMean F ∈ simplexFace S I ↔ (F : Set (Euclidean m)) ⊆ simplexFace S I := by
  constructor
  · intro hm
    have hcover : complexSupport (inducedComplex T I) = simplexFace S I := (hT I).1
    rw [← hcover] at hm
    obtain ⟨G, hG, hmG⟩ := Set.mem_iUnion₂.mp hm
    have hG' : G ∈ T.complex.cells ∧ cellHull G ⊆ simplexFace S I :=
      (inducedCells_iff T I G).mp hG
    have hFG := (faceMean_mem_cellHull_iff T.complex F G hFK hF hG'.1).mp hmG
    exact fun x hx => hG'.2 (subset_convexHull ℝ _ (hFG hx))
  · intro hsub
    exact (convexHull_min hsub (convex_convexHull ℝ _)) (faceMean_mem F hF)

/-- Filtering a subdivided triangulation to an original face gives precisely
the raw subdivision of the old induced complex. -/
theorem barycentric_induced_cells {m n : ℕ} {S : AffineSimplex m n}
    (T U : Triangulation S) (hT : FaceCompatible T)
    (hU : U.complex.cells = barycentricCells T.complex)
    (I : Finset (Fin (n + 1))) :
    (inducedComplex U I).cells = barycentricCells (inducedComplex T I) := by
  classical
  ext s
  rw [inducedComplex_cells]
  change s ∈ U.complex.cells.filter _ ↔ _
  rw [Finset.mem_filter, hU, mem_barycentricCells_iff, mem_barycentricCells_iff]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, hs⟩
    refine ⟨C, ⟨?_, hC.2⟩, rfl⟩
    intro F hFC
    obtain ⟨hFK, hF⟩ := hC.1 F hFC
    refine ⟨?_, hF⟩
    change F ∈ T.complex.cells.filter _
    apply Finset.mem_filter.mpr
    refine ⟨hFK, (faceMean_mem_originalFace_iff T hT I F hFK hF).mp ?_⟩
    exact hs (Finset.mem_image.mpr ⟨F, hFC, rfl⟩)
  · rintro ⟨C, hC, rfl⟩
    have hCold : FaceChain T.complex C := by
      refine ⟨?_, hC.2⟩
      intro F hFC
      exact ⟨(Finset.mem_filter.mp (hC.1 F hFC).1).1, (hC.1 F hFC).2⟩
    refine ⟨⟨C, hCold, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨F, hFC, rfl⟩ := Finset.mem_image.mp hx
    have hF := hC.1 F hFC
    have hFF : F ∈ T.complex.cells ∧ (F : Set (Euclidean m)) ⊆ simplexFace S I :=
      Finset.mem_filter.mp hF.1
    exact (faceMean_mem_originalFace_iff T hT I F hFF.1 hF.2).mpr hFF.2

/-- Once the raw subdivision is a triangulation, compatibility on all original
faces follows from exact cell filtering, coverage, and saturated-chain purity. -/
theorem barycentric_faceCompatible {m n : ℕ} {S : AffineSimplex m n}
    (T U : Triangulation S) (hT : FaceCompatible T)
    (hU : U.complex.cells = barycentricCells T.complex) : FaceCompatible U := by
  intro I
  have heq := barycentric_induced_cells T U hT hU I
  constructor
  · change (⋃ s ∈ (inducedComplex U I).cells, cellHull s) = simplexFace S I
    rw [heq, barycentricCells_support]
    exact (hT I).1
  · intro s hs
    obtain ⟨hs, hmax⟩ := Finset.mem_filter.mp hs
    change s ∈ (inducedComplex U I).cells at hs
    rw [heq] at hs
    apply barycentricCells_pure (inducedComplex T I) (hT I).2 s hs
    intro t ht hst
    have ht' : t ∈ (inducedComplex U I).cells := by rwa [heq]
    exact hmax t ht' hst


/-- Original-vertex coordinates of a linear combination of face means. -/
def chainCoordinates {m : ℕ} (C : Finset (Finset (Euclidean m)))
    (a : Finset (Euclidean m) → ℝ) (v : Euclidean m) : ℝ :=
  ∑ F ∈ C, if v ∈ F then a F / (F.card : ℝ) else 0

theorem sum_chainCoordinates {m : ℕ} (V : Finset (Euclidean m))
    (C : Finset (Finset (Euclidean m))) (a : Finset (Euclidean m) → ℝ)
    (hC : ∀ F ∈ C, F ⊆ V ∧ F.Nonempty) :
    ∑ v ∈ V, chainCoordinates C a v = ∑ F ∈ C, a F := by
  classical
  unfold chainCoordinates
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hFC
  have hFV := (hC F hFC).1
  have hFn : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hC F hFC).2.card_pos.ne'
  rw [← Finset.sum_filter]
  have hfilter : V.filter (fun v => v ∈ F) = F := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hFV h, h⟩⟩
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem sum_smul_chainCoordinates {m : ℕ} (V : Finset (Euclidean m))
    (C : Finset (Finset (Euclidean m))) (a : Finset (Euclidean m) → ℝ)
    (hC : ∀ F ∈ C, F ⊆ V ∧ F.Nonempty) :
    ∑ v ∈ V, chainCoordinates C a v • v = ∑ F ∈ C, a F • faceMean F := by
  classical
  simp only [chainCoordinates, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hFC
  have hFV := (hC F hFC).1
  have hFn : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hC F hFC).2.card_pos.ne'
  simp only [ite_smul, zero_smul]
  rw [← Finset.sum_filter]
  have hfilter : V.filter (fun v => v ∈ F) = F := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hFV h, h⟩⟩
  rw [hfilter, ← Finset.smul_sum, ← faceMean_card_smul F (hC F hFC).2, smul_smul,
    div_mul_cancel₀ _ hFn]

theorem chainCoordinates_nonneg {m : ℕ} (C : Finset (Finset (Euclidean m)))
    (a : Finset (Euclidean m) → ℝ) (ha : ∀ F ∈ C, 0 ≤ a F) (v : Euclidean m) :
    0 ≤ chainCoordinates C a v := by
  apply Finset.sum_nonneg
  intro F hF
  split_ifs
  · exact div_nonneg (ha F hF) (Nat.cast_nonneg _)
  · exact le_refl 0

/-- Every point of a chain cell admits nonnegative coefficients indexed by the
old faces themselves. -/
theorem exists_chain_coefficients {m : ℕ} (K : GeometricComplex m)
    (C : Finset (Finset (Euclidean m))) (hC : FaceChain K C)
    (x : Euclidean m) (hx : x ∈ cellHull (C.image faceMean)) :
    ∃ a : Finset (Euclidean m) → ℝ, (∀ F ∈ C, 0 ≤ a F) ∧
      ∑ F ∈ C, a F = 1 ∧ ∑ F ∈ C, a F • faceMean F = x := by
  classical
  obtain ⟨w, hw₀, hw₁, hwx⟩ := Finset.mem_convexHull'.mp hx
  have hinj : Set.InjOn faceMean (C : Set (Finset (Euclidean m))) :=
    (chain_faceMean_affineIndepOn C (fun F hF => (hC.1 F hF).2)
      (fun F hF => K.independent F (hC.1 F hF).1) hC.2).injOn
  refine ⟨fun F => w (faceMean F), ?_, ?_, ?_⟩
  · exact fun F hF => hw₀ _ (Finset.mem_image.mpr ⟨F, hF, rfl⟩)
  · rwa [Finset.sum_image hinj] at hw₁
  · rwa [Finset.sum_image hinj] at hwx


/-- A point of a chain cell lying in an old cell has zero coefficient at every
chain face not contained in that old cell. -/
theorem chain_coefficients_vanish_outside {m : ℕ} (K : GeometricComplex m)
    (C : Finset (Finset (Euclidean m))) (hC : FaceChain K C)
    (G : Finset (Euclidean m)) (hGK : G ∈ K.cells)
    (a : Finset (Euclidean m) → ℝ) (ha : ∀ F ∈ C, 0 ≤ a F)
    (hasum : ∑ F ∈ C, a F = 1)
    (hxG : (∑ F ∈ C, a F • faceMean F) ∈ cellHull G) :
    ∀ F ∈ C, ¬ F ⊆ G → a F = 0 := by
  classical
  obtain ⟨V, hVK, hCV⟩ := faceChain_carrier K C hC
  have hsub : ∀ F ∈ C, F ⊆ V ∧ F.Nonempty :=
    fun F hF => ⟨hCV F hF, (hC.1 F hF).2⟩
  let z := ∑ F ∈ C, a F • faceMean F
  have hzV : z ∈ cellHull V := by
    change (∑ F ∈ C, a F • faceMean F) ∈ cellHull V
    rw [← Finset.centerMass_eq_of_sum_1 C faceMean hasum]
    exact (convex_convexHull ℝ (V : Set (Euclidean m))).centerMass_mem ha
      (by rw [hasum]; norm_num)
      (fun F hF => cellHull_mono (hCV F hF) (faceMean_mem F (hC.1 F hF).2))
  let J : Set V := {v | (v : Euclidean m) ∈ G}
  have hJ : ((↑) : V → Euclidean m) '' J = (↑(V ∩ G) : Set (Euclidean m)) := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Finset.mem_inter.mpr ⟨y.property, hy⟩
    · intro hv
      obtain ⟨hvV, hvG⟩ := Finset.mem_inter.mp hv
      exact ⟨⟨v, hvV⟩, hvG, rfl⟩
  have hzJ : z ∈ affineSpan ℝ (((↑) : V → Euclidean m) '' J) := by
    rw [hJ]
    apply convexHull_subset_affineSpan
    have hi : cellHull V ∩ cellHull G = cellHull (V ∩ G) := K.inter_eq V hVK G hGK
    change z ∈ cellHull (V ∩ G)
    rw [← hi]
    exact ⟨hzV, hxG⟩
  have hw : ∑ v : V, chainCoordinates C a v = 1 := by
    rw [Finset.sum_coe_sort]
    exact (sum_chainCoordinates V C a hsub).trans hasum
  have hcombo : Finset.univ.affineCombination ℝ ((↑) : V → Euclidean m)
      (fun v => chainCoordinates C a v) = z := by
    rw [affineCombination_eq_centerMass hw, Finset.centerMass_eq_of_sum_1 _ _ hw]
    exact (Finset.sum_coe_sort V (fun v => chainCoordinates C a v • v)).trans
      (sum_smul_chainCoordinates V C a hsub)
  rw [← hcombo] at hzJ
  intro F hFC hFG
  obtain ⟨v, hvF, hvG⟩ : ∃ v ∈ F, v ∉ G := by
    simpa only [Finset.subset_iff, not_forall, exists_prop] using hFG
  have hzv : chainCoordinates C a v = 0 :=
    (K.independent V hVK).eq_zero_of_affineCombination_mem_affineSpan hw hzJ
      (Finset.mem_univ (⟨v, hCV F hFC hvF⟩ : V)) hvG
  have hterms : ∀ H ∈ C, 0 ≤ (if v ∈ H then a H / (H.card : ℝ) else 0) := by
    intro H hH
    split_ifs
    · exact div_nonneg (ha H hH) (Nat.cast_nonneg _)
    · exact le_refl 0
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hzv F hFC
  simp only [ite_eq_left hvF] at hzero
  exact (div_eq_zero_iff).mp hzero |>.resolve_right
    (Nat.cast_ne_zero.mpr (hC.1 F hFC).2.card_pos.ne')

/-- Exact restriction of a barycentric chain cell to an old geometric cell. -/
theorem chain_cell_inter_old_cell {m : ℕ} (K : GeometricComplex m)
    (C : Finset (Finset (Euclidean m))) (hC : FaceChain K C)
    (G : Finset (Euclidean m)) (hGK : G ∈ K.cells) :
    cellHull (C.image faceMean) ∩ cellHull G =
      cellHull ((C.filter (fun F => F ⊆ G)).image faceMean) := by
  classical
  let D := C.filter (fun F => F ⊆ G)
  have hDC : D ⊆ C := Finset.filter_subset _ _
  apply Set.Subset.antisymm
  · rintro x ⟨hxC, hxG⟩
    obtain ⟨a, ha, hasum, hax⟩ := exists_chain_coefficients K C hC x hxC
    have hz := chain_coefficients_vanish_outside K C hC G hGK a ha hasum
      (hax.symm ▸ hxG)
    have hout : ∀ F ∈ C, F ∉ D → a F = 0 := by
      intro F hFC hFD
      apply hz F hFC
      intro hFG
      exact hFD (Finset.mem_filter.mpr ⟨hFC, hFG⟩)
    have hsumD : ∑ F ∈ D, a F = 1 := by
      rw [Finset.sum_subset hDC hout, hasum]
    have hxD : ∑ F ∈ D, a F • faceMean F = x := by
      rw [Finset.sum_subset hDC (fun F hFC hFD => by rw [hout F hFC hFD, zero_smul]), hax]
    apply mem_convexHull_of_exists_fintype (fun F : D => a F) (fun F : D => faceMean F)
    · exact fun F => ha F (hDC F.property)
    · rw [Finset.sum_coe_sort]
      exact hsumD
    · exact fun F => Finset.mem_image.mpr ⟨F, F.property, rfl⟩
    · exact (Finset.sum_coe_sort D (fun F => a F • faceMean F)).trans hxD
  · intro x hxD
    refine ⟨cellHull_mono (Finset.image_subset_image hDC) hxD, ?_⟩
    have hsub : cellHull (D.image faceMean) ⊆ cellHull G := by
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      obtain ⟨F, hFD, rfl⟩ := Finset.mem_image.mp hy
      exact cellHull_mono (Finset.mem_filter.mp hFD).2
        (faceMean_mem F (hC.1 F (hDC hFD)).2)
    exact hsub hxD


/-- For a chain with positive coefficients, coordinate support is its greatest
face, and its least coordinate on that face is the greatest-face coefficient
normalized by cardinality. -/
theorem positive_chain_coordinates_top {m : ℕ}
    (C : Finset (Finset (Euclidean m))) (hC : C.Nonempty)
    (hne : ∀ F ∈ C, F.Nonempty)
    (hchain : (C : Set (Finset (Euclidean m))).Pairwise
      (fun F G => F ⊆ G ∨ G ⊆ F))
    (a : Finset (Euclidean m) → ℝ) (ha : ∀ F ∈ C, 0 < a F) :
    ∃ G ∈ C, (∀ F ∈ C, F ⊆ G) ∧
      (∀ v, 0 < chainCoordinates C a v ↔ v ∈ G) ∧
      (∀ v ∈ G, a G / (G.card : ℝ) ≤ chainCoordinates C a v) ∧
      ∃ v ∈ G, chainCoordinates C a v = a G / (G.card : ℝ) := by
  classical
  obtain ⟨G, hGC, hmax⟩ := inclusionChain_greatest C hC hchain
  have hterms (v : Euclidean m) :
      ∀ F ∈ C, 0 ≤ (if v ∈ F then a F / (F.card : ℝ) else 0) := by
    intro F hF
    split_ifs
    · exact div_nonneg (ha F hF).le (Nat.cast_nonneg _)
    · exact le_refl 0
  have hlow : ∀ v ∈ G, a G / (G.card : ℝ) ≤ chainCoordinates C a v := by
    intro v hv
    simpa only [chainCoordinates, ite_eq_left hv] using Finset.single_le_sum (hterms v) hGC
  refine ⟨G, hGC, hmax, ?_, hlow, ?_⟩
  · intro v
    constructor
    · intro hp
      by_contra hvG
      have hz : chainCoordinates C a v = 0 := by
        apply Finset.sum_eq_zero
        intro F hF
        exact ite_eq_right (fun hvF => hvG (hmax F hF hvF))
      linarith
    · intro hvG
      exact (div_pos (ha G hGC) (Nat.cast_pos.mpr (hne G hGC).card_pos)).trans_le
        (hlow v hvG)
  · have hprivate : ∃ v ∈ G, ∀ F ∈ C.erase G, v ∉ F := by
      rcases (C.erase G).eq_empty_or_nonempty with he | he
      · obtain ⟨v, hv⟩ := hne G hGC
        exact ⟨v, hv, by simp [he]⟩
      obtain ⟨H, hHC, hHmax⟩ := inclusionChain_greatest (C.erase G) he
        (hchain.mono (Finset.erase_subset _ _))
      have hHG := hmax H (Finset.mem_of_mem_erase hHC)
      have hHne : H ≠ G := (Finset.mem_erase.mp hHC).1
      obtain ⟨v, hvG, hvH⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hHG hHne)
      exact ⟨v, hvG, fun F hF hvF => hvH (hHmax F hF hvF)⟩
    obtain ⟨v, hvG, hv⟩ := hprivate
    refine ⟨v, hvG, ?_⟩
    unfold chainCoordinates
    rw [Finset.sum_eq_single G]
    · simp only [ite_eq_left hvG]
    · intro F hFC hFG
      exact ite_eq_right (hv F (Finset.mem_erase.mpr ⟨hFG, hFC⟩))
    · intro h
      exact (h hGC).elim

/-- Positive chain decompositions of the same vertex-coordinate vector have
exactly the same face support. -/
theorem positive_chain_coordinates_unique {m : ℕ}
    (C D : Finset (Finset (Euclidean m)))
    (a b : Finset (Euclidean m) → ℝ)
    (hCn : ∀ F ∈ C, F.Nonempty) (hDn : ∀ F ∈ D, F.Nonempty)
    (hCc : (C : Set (Finset (Euclidean m))).Pairwise (fun F G => F ⊆ G ∨ G ⊆ F))
    (hDc : (D : Set (Finset (Euclidean m))).Pairwise (fun F G => F ⊆ G ∨ G ⊆ F))
    (ha : ∀ F ∈ C, 0 < a F) (hb : ∀ F ∈ D, 0 < b F)
    (heq : ∀ v, chainCoordinates C a v = chainCoordinates D b v) : C = D := by
  classical
  induction C using Finset.strongInductionOn generalizing D with
  | _ C ih =>
    rcases C.eq_empty_or_nonempty with hC | hC
    · subst C
      by_contra hD
      obtain ⟨G, hGD, _, hpos, _, _⟩ := positive_chain_coordinates_top D
        (Finset.nonempty_iff_ne_empty.mpr (Ne.symm hD)) hDn hDc b hb
      obtain ⟨v, hv⟩ := hDn G hGD
      have hp := (hpos v).mpr hv
      have hz := heq v
      simp only [chainCoordinates, Finset.sum_empty] at hz hp
      linarith
    rcases D.eq_empty_or_nonempty with hD | hD
    · subst D
      obtain ⟨G, hGC, _, hpos, _, _⟩ := positive_chain_coordinates_top C hC hCn hCc a ha
      obtain ⟨v, hv⟩ := hCn G hGC
      have hp := (hpos v).mpr hv
      have hz := heq v
      simp only [chainCoordinates, Finset.sum_empty] at hz hp
      linarith
    obtain ⟨G, hGC, hGmax, hGpos, hGlow, v, hvG, hvval⟩ :=
      positive_chain_coordinates_top C hC hCn hCc a ha
    obtain ⟨H, hHD, hHmax, hHpos, hHlow, w, hwH, hwval⟩ :=
      positive_chain_coordinates_top D hD hDn hDc b hb
    have hGH : G = H := by
      ext z
      rw [← hGpos, ← hHpos, heq]
    subst H
    have hcoef : a G / (G.card : ℝ) = b G / (G.card : ℝ) := by
      have h₁ := hHlow v hvG
      have h₂ := hGlow w hwH
      rw [← heq v, hvval] at h₁
      rw [heq w, hwval] at h₂
      exact le_antisymm h₂ h₁
    have heq' : ∀ z, chainCoordinates (C.erase G) a z = chainCoordinates (D.erase G) b z := by
      intro z
      unfold chainCoordinates
      rw [Finset.sum_erase_eq_sub hGC, Finset.sum_erase_eq_sub hHD]
      have hz := heq z
      unfold chainCoordinates at hz
      rw [hz, hcoef]
    have hCD := ih (C.erase G) (Finset.erase_ssubset hGC) (D.erase G)
      (fun F hF => hCn F (Finset.mem_of_mem_erase hF))
      (fun F hF => hDn F (Finset.mem_of_mem_erase hF))
      (hCc.mono (Finset.erase_subset _ _)) (hDc.mono (Finset.erase_subset _ _))
      (fun F hF => ha F (Finset.mem_of_mem_erase hF))
      (fun F hF => hb F (Finset.mem_of_mem_erase hF)) heq'
    have hh := congrArg (insert G) hCD
    simpa only [Finset.insert_erase hGC, Finset.insert_erase hHD] using hh


theorem chainCoordinates_filter_pos {m : ℕ} (C : Finset (Finset (Euclidean m)))
    (a : Finset (Euclidean m) → ℝ) (ha : ∀ F ∈ C, 0 ≤ a F) (v : Euclidean m) :
    chainCoordinates (C.filter (fun F => 0 < a F)) a v = chainCoordinates C a v := by
  classical
  unfold chainCoordinates
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro F hFC hFfilter
  have hn : ¬ 0 < a F := fun hp => hFfilter (Finset.mem_filter.mpr ⟨hFC, hp⟩)
  have hz : a F = 0 := le_antisymm (le_of_not_gt hn) (ha F hFC)
  simp [hz]

theorem mem_chain_cell_of_coefficients {m : ℕ}
    (C : Finset (Finset (Euclidean m))) (a : Finset (Euclidean m) → ℝ)
    (ha : ∀ F ∈ C, 0 ≤ a F) (hasum : ∑ F ∈ C, a F = 1) :
    (∑ F ∈ C, a F • faceMean F) ∈ cellHull (C.image faceMean) := by
  apply mem_convexHull_of_exists_fintype (fun F : C => a F) (fun F : C => faceMean F)
  · exact fun F => ha F F.property
  · exact (Finset.sum_coe_sort C a).trans hasum
  · exact fun F => Finset.mem_image.mpr ⟨F, F.property, rfl⟩
  · exact Finset.sum_coe_sort C (fun F => a F • faceMean F)

/-- Within one old simplex, two chain cells intersect only in the convex hull
of their common barycentres. Positive chain-coordinate support is intrinsic. -/
theorem chain_cells_inter_same_carrier {m : ℕ} (K : GeometricComplex m)
    (V : Finset (Euclidean m)) (hVK : V ∈ K.cells)
    (C D : Finset (Finset (Euclidean m))) (hC : FaceChain K C) (hD : FaceChain K D)
    (hCV : ∀ F ∈ C, F ⊆ V) (hDV : ∀ F ∈ D, F ⊆ V) :
    cellHull (C.image faceMean) ∩ cellHull (D.image faceMean) ⊆
      cellHull (C.image faceMean ∩ D.image faceMean) := by
  classical
  rintro x ⟨hxC, hxD⟩
  obtain ⟨a, ha, hasum, hax⟩ := exists_chain_coefficients K C hC x hxC
  obtain ⟨b, hb, hbsum, hbx⟩ := exists_chain_coefficients K D hD x hxD
  have hCsub : ∀ F ∈ C, F ⊆ V ∧ F.Nonempty := fun F hF => ⟨hCV F hF, (hC.1 F hF).2⟩
  have hDsub : ∀ F ∈ D, F ⊆ V ∧ F.Nonempty := fun F hF => ⟨hDV F hF, (hD.1 F hF).2⟩
  have hcoords : ∀ v, chainCoordinates C a v = chainCoordinates D b v := by
    intro v
    by_cases hvV : v ∈ V
    · apply (K.independent V hVK).eq_of_sum_eq_sum_subtype
        (w₁ := chainCoordinates C a) (w₂ := chainCoordinates D b) _ _ v hvV
      · rw [sum_chainCoordinates V C a hCsub, sum_chainCoordinates V D b hDsub, hasum, hbsum]
      · rw [sum_smul_chainCoordinates V C a hCsub, sum_smul_chainCoordinates V D b hDsub,
          hax, hbx]
    · have hzC : chainCoordinates C a v = 0 := by
        apply Finset.sum_eq_zero
        intro F hFC
        exact ite_eq_right (fun hvF => hvV (hCV F hFC hvF))
      have hzD : chainCoordinates D b v = 0 := by
        apply Finset.sum_eq_zero
        intro F hFD
        exact ite_eq_right (fun hvF => hvV (hDV F hFD hvF))
      exact hzC.trans hzD.symm
  let C' := C.filter (fun F => 0 < a F)
  let D' := D.filter (fun F => 0 < b F)
  have hC'C : C' ⊆ C := Finset.filter_subset _ _
  have hD'D : D' ⊆ D := Finset.filter_subset _ _
  have hsame : C' = D' := by
    apply positive_chain_coordinates_unique C' D' a b
      (fun F hF => (hC.1 F (hC'C hF)).2) (fun F hF => (hD.1 F (hD'D hF)).2)
      (hC.2.mono hC'C) (hD.2.mono hD'D)
      (fun F hF => (Finset.mem_filter.mp hF).2) (fun F hF => (Finset.mem_filter.mp hF).2)
    intro v
    exact (chainCoordinates_filter_pos C a ha v).trans
      ((hcoords v).trans (chainCoordinates_filter_pos D b hb v).symm)
  have hout : ∀ F ∈ C, F ∉ C' → a F = 0 := by
    intro F hFC hFC'
    apply le_antisymm _ (ha F hFC)
    by_contra hn
    have hp : 0 < a F := lt_of_not_ge hn
    exact hFC' (Finset.mem_filter.mpr ⟨hFC, hp⟩)
  have hsum' : ∑ F ∈ C', a F = 1 := by rw [Finset.sum_subset hC'C hout, hasum]
  have hx' : ∑ F ∈ C', a F • faceMean F = x := by
    rw [Finset.sum_subset hC'C (fun F hFC hFC' => by rw [hout F hFC hFC', zero_smul]), hax]
  have hmem := mem_chain_cell_of_coefficients C' a (fun F hF => ha F (hC'C hF)) hsum'
  rw [hx'] at hmem
  apply cellHull_mono _ hmem
  intro y hy
  obtain ⟨F, hFC', rfl⟩ := Finset.mem_image.mp hy
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_image.mpr ⟨F, hC'C hFC', rfl⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨F, hD'D (hsame ▸ hFC'), rfl⟩

/-- The full geometric common-face intersection axiom for the raw barycentric
cells of an arbitrary finite geometric complex. -/
theorem barycentricCells_inter_eq {m : ℕ} (K : GeometricComplex m)
    (s : Finset (Euclidean m)) (hs : s ∈ barycentricCells K)
    (t : Finset (Euclidean m)) (ht : t ∈ barycentricCells K) :
    cellHull s ∩ cellHull t = cellHull (s ∩ t) := by
  classical
  apply Set.Subset.antisymm _
    (Set.subset_inter (cellHull_mono Finset.inter_subset_left)
      (cellHull_mono Finset.inter_subset_right))
  obtain ⟨C, hC, rfl⟩ := (mem_barycentricCells_iff K s).mp hs
  obtain ⟨D, hD, rfl⟩ := (mem_barycentricCells_iff K t).mp ht
  obtain ⟨V, hVK, hCV⟩ := faceChain_carrier K C hC
  obtain ⟨W, hWK, hDW⟩ := faceChain_carrier K D hD
  let C' := C.filter (fun F => F ⊆ W)
  let D' := D.filter (fun F => F ⊆ V)
  have hC'C : C' ⊆ C := Finset.filter_subset _ _
  have hD'D : D' ⊆ D := Finset.filter_subset _ _
  have hRK : V ∩ W ∈ K.cells := K.face_closed V hVK _ Finset.inter_subset_left
  intro x hx
  have hxV : x ∈ cellHull V := by
    have hh : cellHull (C.image faceMean) ⊆ cellHull V := by
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      obtain ⟨F, hFC, rfl⟩ := Finset.mem_image.mp hy
      exact cellHull_mono (hCV F hFC) (faceMean_mem F (hC.1 F hFC).2)
    exact hh hx.1
  have hxW : x ∈ cellHull W := by
    have hh : cellHull (D.image faceMean) ⊆ cellHull W := by
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      obtain ⟨F, hFD, rfl⟩ := Finset.mem_image.mp hy
      exact cellHull_mono (hDW F hFD) (faceMean_mem F (hD.1 F hFD).2)
    exact hh hx.2
  have hxC' : x ∈ cellHull (C'.image faceMean) := by
    rw [← chain_cell_inter_old_cell K C hC W hWK]
    exact ⟨hx.1, hxW⟩
  have hxD' : x ∈ cellHull (D'.image faceMean) := by
    rw [← chain_cell_inter_old_cell K D hD V hVK]
    exact ⟨hx.2, hxV⟩
  have hsubC : ∀ F ∈ C', F ⊆ V ∩ W := by
    intro F hF
    exact Finset.subset_inter (hCV F (hC'C hF)) (Finset.mem_filter.mp hF).2
  have hsubD : ∀ F ∈ D', F ⊆ V ∩ W := by
    intro F hF
    exact Finset.subset_inter (Finset.mem_filter.mp hF).2 (hDW F (hD'D hF))
  have hxcommon := chain_cells_inter_same_carrier K (V ∩ W) hRK C' D'
    (faceChain_mono hC hC'C) (faceChain_mono hD hD'D) hsubC hsubD ⟨hxC', hxD'⟩
  apply cellHull_mono _ hxcommon
  exact Finset.inter_subset_inter (Finset.image_subset_image hC'C) (Finset.image_subset_image hD'D)


/-- Barycentric subdivision as a genuine finite geometric complex. All fields,
including the convex-hull intersection axiom, have been proved above. -/
def barycentricComplex {m : ℕ} (K : GeometricComplex m) : GeometricComplex m where
  cells := barycentricCells K
  empty_mem := barycentricCells_empty_mem K
  independent := barycentricCells_independent K
  face_closed := barycentricCells_face_closed K
  inter_eq := barycentricCells_inter_eq K

theorem barycentricComplex_support {m : ℕ} (K : GeometricComplex m) :
    complexSupport (barycentricComplex K) = complexSupport K :=
  barycentricCells_support K

theorem barycentric_complex_exists :
    Specs.D10Topology.Ch17.BarycentricSubdivision.barycentric_complex_exists := by
  intro m K
  exact ⟨barycentricComplex K, rfl, barycentricComplex_support K⟩

/-- Subdivide each old cell, with the same induced subdivision on shared faces. -/
def barycentricTriangulation {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) : Triangulation S where
  complex := barycentricComplex T.complex
  covers := (barycentricComplex_support T.complex).trans T.covers
  pure := by
    intro s hs
    obtain ⟨hs, hmax⟩ := Finset.mem_filter.mp hs
    exact barycentricCells_pure T.complex T.pure s hs hmax

theorem barycentricTriangulation_faceCompatible {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) (hT : FaceCompatible T) :
    FaceCompatible (barycentricTriangulation T) :=
  barycentric_faceCompatible T (barycentricTriangulation T) hT rfl

theorem barycentricTriangulation_mesh {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) :
    mesh (barycentricTriangulation T).complex ≤
      ((n : ℝ) / ((n : ℝ) + 1)) * mesh T.complex :=
  barycentric_mesh_contraction T _ rfl

/-- Iterated genuine geometric subdivision, starting from the original simplex. -/
def subdivisionSequence {m n : ℕ} (S : AffineSimplex m n) : ℕ → Triangulation S
  | 0 => originalTriangulation S
  | r + 1 => barycentricTriangulation (subdivisionSequence S r)

theorem subdivisionSequence_faceCompatible {m n : ℕ} (S : AffineSimplex m n) :
    ∀ r, FaceCompatible (subdivisionSequence S r) := by
  intro r
  induction r with
  | zero => exact original_faceCompatible S
  | succ r ih => exact barycentricTriangulation_faceCompatible _ ih

theorem subdivisionSequence_mesh_bound {m n : ℕ} (S : AffineSimplex m n) :
    ∀ r, mesh (subdivisionSequence S r).complex ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ r * Metric.diam (simplexHull S) := by
  have hq : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  intro r
  induction r with
  | zero =>
    change mesh (originalComplex S) ≤ _
    rw [original_mesh, pow_zero, one_mul]
  | succ r ih =>
    calc
      mesh (subdivisionSequence S (r + 1)).complex ≤
          (n : ℝ) / ((n : ℝ) + 1) * mesh (subdivisionSequence S r).complex :=
        barycentricTriangulation_mesh _
      _ ≤ (n : ℝ) / ((n : ℝ) + 1) *
          (((n : ℝ) / ((n : ℝ) + 1)) ^ r * Metric.diam (simplexHull S)) :=
        mul_le_mul_of_nonneg_left ih hq
      _ = _ := by rw [pow_succ]; ring

theorem subdivisionSequence_mesh_tendsto {m n : ℕ} (S : AffineSimplex m n) :
    Filter.Tendsto (fun r => mesh (subdivisionSequence S r).complex) Filter.atTop (𝓝 0) := by
  have hq₀ : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hq₁ : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  have hlim : Filter.Tendsto
      (fun r : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) ^ r * Metric.diam (simplexHull S))
      Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).mul_const
        (Metric.diam (simplexHull S))
  exact squeeze_zero (fun r => mesh_nonneg _) (subdivisionSequence_mesh_bound S) hlim

theorem fine_triangulations :
    Specs.D10Topology.Ch17.BarycentricSubdivision.fine_triangulations := by
  intro m n S
  exact ⟨subdivisionSequence S, subdivisionSequence_faceCompatible S,
    subdivisionSequence_mesh_tendsto S⟩

theorem arbitrarily_fine_triangulation :
    Specs.D10Topology.Ch17.BarycentricSubdivision.arbitrarily_fine_triangulation := by
  intro m n S ε hε
  obtain ⟨T, hT, hlim⟩ := fine_triangulations S
  have hevent : ∀ᶠ r in Filter.atTop, mesh (T r).complex < ε :=
    hlim.eventually (gt_mem_nhds hε)
  obtain ⟨r, hr⟩ := hevent.exists
  exact ⟨T r, hT r, hr⟩


end Subdivision
end D10Topology.Ch17
