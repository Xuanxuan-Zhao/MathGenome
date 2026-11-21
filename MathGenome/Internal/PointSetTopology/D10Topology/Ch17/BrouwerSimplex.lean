import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.BrouwerSimplex
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.BarycentricSubdivision
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.Sperner
import Mathlib.Topology.Sequences

/-! Brouwer on the actual Euclidean standard simplex, by fine geometric
triangulations, Sperner's lemma, and sequential compactness. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace D10Topology.Ch17
namespace BrouwerSimplex

theorem standardSimplex_isCompact (n : ℕ) : IsCompact (standardSimplex n) := by
  rw [← standardAffineSimplex_hull]
  exact (Set.finite_range (standardAffineSimplex n).points).isCompact_convexHull ℝ

theorem vertex_mem_simplex {n : ℕ} (T : Triangulation (standardAffineSimplex n))
    {v : Euclidean (n + 1)} (hv : v ∈ vertices T.complex) :
    v ∈ standardSimplex n := by
  obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
  rw [← standardAffineSimplex_hull]
  apply T.covers.subset
  exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hC,
    subset_convexHull ℝ (C : Set (Euclidean (n + 1))) hvC⟩⟩

theorem face_coordinate_zero {n : ℕ} (I : Finset (Fin (n + 1)))
    {v : Euclidean (n + 1)} (hv : v ∈ simplexFace (standardAffineSimplex n) I)
    {i : Fin (n + 1)} (hi : i ∉ I) : v i = 0 := by
  apply convexHull_min (t := {x : Euclidean (n + 1) | x i = 0}) ?_ ?_ hv
  · rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
    change EuclideanSpace.basisFun (Fin (n + 1)) ℝ j i = 0
    simp [EuclideanSpace.basisFun_apply, hji]
  · exact convex_hyperplane (EuclideanSpace.projₗ i).isLinear 0

theorem exists_decreased_coordinate {n : ℕ}
    (x y : standardSimplex n) (h : x ≠ y) :
    ∃ i : Fin (n + 1), (y : Euclidean (n + 1)) i < (x : Euclidean (n + 1)) i := by
  by_contra! hn
  apply h
  apply Subtype.ext
  apply PiLp.ext
  have he : ∑ i, (x : Euclidean (n + 1)) i = ∑ i, (y : Euclidean (n + 1)) i :=
    x.property.2.trans y.property.2.symm
  intro i
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hn i)).mp he i (Finset.mem_univ i)

/- A fully labeled cell supplies, for each coordinate, a vertex where that
coordinate strictly decreases. All these vertices lie within one mesh. -/
theorem decreasing_vertices {n : ℕ}
    (f : standardSimplex n → standardSimplex n)
    (hne : ∀ x, x ≠ f x) (T : Triangulation (standardAffineSimplex n)) :
    ∃ v : Fin (n + 1) → standardSimplex n,
      (∀ i, (f (v i) : Euclidean (n + 1)) i < (v i : Euclidean (n + 1)) i) ∧
      ∀ i j, dist (v i) (v j) ≤ mesh T.complex := by
  classical
  let point (v : {v : Euclidean (n + 1) // v ∈ vertices T.complex}) :
      standardSimplex n := ⟨v.val, vertex_mem_simplex T v.property⟩
  let ℓ : VertexLabeling T := fun v =>
    Classical.choose (exists_decreased_coordinate (point v) (f (point v)) (hne _))
  have hℓ (v) : (f (point v) : Euclidean (n + 1)) (ℓ v) < v.val (ℓ v) :=
    Classical.choose_spec (exists_decreased_coordinate (point v) (f (point v)) (hne _))
  have hface : FaceRespecting T ℓ := by
    intro I v hvI
    by_contra hi
    have hz := face_coordinate_zero I hvI hi
    have hpos := hℓ v
    have hnonneg := (f (point v)).property.1 (ℓ v)
    linarith
  obtain ⟨C, _, hs, _, hlabels⟩ := sperner_exists T ℓ hface
  change cellLabels T ℓ C hs = Finset.univ at hlabels
  have hvertex : ∀ i : Fin (n + 1),
      ∃ v : {v : Euclidean (n + 1) // v ∈ vertices T.complex},
        v.val ∈ C ∧ ℓ v = i := by
    intro i
    have hi : i ∈ cellLabels T ℓ C hs := by rw [hlabels]; exact Finset.mem_univ i
    change i ∈ C.attach.image _ at hi
    obtain ⟨v, _, hvi⟩ := Finset.mem_image.mp hi
    exact ⟨⟨v.val, SpernerCounting.vertex_of_cell _ hs v.property⟩, v.property, hvi⟩
  choose w hwC hwlabel using hvertex
  refine ⟨fun i => point (w i), ?_, ?_⟩
  · intro i
    simpa only [hwlabel i] using hℓ (w i)
  · intro i j
    exact dist_le_mesh T.complex C hs _ (subset_convexHull ℝ _ (hwC i))
      _ (subset_convexHull ℝ _ (hwC j))

end BrouwerSimplex

/-- Every continuous self-map of the Euclidean standard simplex has a fixed
point, in every finite dimension including zero. -/
theorem brouwer_simplex : Specs.D10Topology.Ch17.BrouwerSimplex.brouwer_simplex := by
  intro n f hf
  classical
  by_contra hfix
  have hne : ∀ x, x ≠ f x := fun x h => hfix ⟨x, h.symm⟩
  obtain ⟨T, _, hmesh⟩ := Subdivision.fine_triangulations (standardAffineSimplex n)
  choose v hdecrease hdist using fun r => BrouwerSimplex.decreasing_vertices f hne (T r)
  let : CompactSpace (standardSimplex n) :=
    isCompact_iff_compactSpace.mp (BrouwerSimplex.standardSimplex_isCompact n)
  obtain ⟨x, φ, hφ, hx⟩ := CompactSpace.tendsto_subseq (fun r => v r 0)
  have hv (i : Fin (n + 1)) : Tendsto (fun r => v (φ r) i) atTop (𝓝 x) := by
    apply hx.congr_dist
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun r => hdist (φ r) 0 i) (hmesh.comp hφ.tendsto_atTop)
  have hcoord (i : Fin (n + 1)) :
      (f x : Euclidean (n + 1)) i ≤ (x : Euclidean (n + 1)) i := by
    have hc : Continuous (fun y : standardSimplex n => (y : Euclidean (n + 1)) i) :=
      (EuclideanSpace.proj i).continuous.comp continuous_subtype_val
    exact le_of_tendsto_of_tendsto ((hc.comp hf).tendsto x |>.comp (hv i))
      (hc.tendsto x |>.comp (hv i))
      (Filter.Eventually.of_forall (fun r => (hdecrease (φ r) i).le))
  apply hfix
  refine ⟨x, Subtype.ext (PiLp.ext ?_)⟩
  have he : ∑ i, (f x : Euclidean (n + 1)) i = ∑ i, (x : Euclidean (n + 1)) i :=
    (f x).property.2.trans x.property.2.symm
  intro i
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hcoord i)).mp he i (Finset.mem_univ i)

end D10Topology.Ch17
