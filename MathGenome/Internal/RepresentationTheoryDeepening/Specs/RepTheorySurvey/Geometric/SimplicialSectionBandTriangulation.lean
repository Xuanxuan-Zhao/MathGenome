import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

namespace RepTheorySurvey.Geometric.SimplicialSectionBandTriangulationSpecs

universe u

variable {σ : Type u}

/-- A face together with its membership in the base complex. -/
abbrev Face (K : Geometry.SimplicialComplex ℝ (σ → ℝ)) := ↥K.faces

/-- The closed hull of a base face. -/
abbrev faceHull {K : Geometry.SimplicialComplex ℝ (σ → ℝ)} (s : Face K) : Set (σ → ℝ) :=
  convexHull ℝ (s.val : Set (σ → ℝ))

/-- Continuous levels on the closed base faces with compatible restrictions. -/
structure LevelFamily (K : Geometry.SimplicialComplex ℝ (σ → ℝ)) (a b : ℝ) where
  count : Face K → ℕ
  level : (s : Face K) → Fin (count s + 2) → faceHull s → Set.Icc a b
  continuous_level : ∀ s i, Continuous (level s i)
  first_level : ∀ s x, (level s 0 x : ℝ) = a
  last_level : ∀ s x, (level s (Fin.last (count s + 1)) x : ℝ) = b
  monotone_level : ∀ s x, Monotone (fun i => (level s i x : ℝ))
  strictMono_level : ∀ s (x : faceHull s),
    (x : σ → ℝ) ∈ intrinsicInterior ℝ (faceHull s) →
      StrictMono (fun i => (level s i x : ℝ))
  separates_at_vertex : ∀ (s : Face K) i j, i ≠ j →
    ∃ (v : σ → ℝ) (hv : v ∈ s.val), level s i ⟨v, subset_convexHull ℝ _ hv⟩ ≠
      level s j ⟨v, subset_convexHull ℝ _ hv⟩
  restrict_levels : ∀ (r s : Face K) (h : r.val ⊆ s.val),
    ∃ q : Fin (count s + 2) → Fin (count r + 2),
      Monotone q ∧ Function.Surjective q ∧
        ∀ i (x : faceHull r),
          level s i ⟨x.val, convexHull_mono (Finset.coe_subset.mpr h) x.property⟩ =
            level r (q i) x

variable {K : Geometry.SimplicialComplex ℝ (σ → ℝ)} {a b : ℝ}

/-- The graph of one level above the intrinsic interior of its base face. -/
def sectionGraph (D : LevelFamily K a b) (s : Face K) (i : Fin (D.count s + 2)) :
    Set ((σ → ℝ) × ℝ) :=
  {p | ∃ hx : p.1 ∈ intrinsicInterior ℝ (faceHull s),
    p.2 = (D.level s i ⟨p.1, intrinsicInterior_subset hx⟩ : ℝ)}

/-- The open vertical band between consecutive levels above the intrinsic interior of a face. -/
def openBand (D : LevelFamily K a b) (s : Face K) (i : Fin (D.count s + 1)) :
    Set ((σ → ℝ) × ℝ) :=
  {p | ∃ hx : p.1 ∈ intrinsicInterior ℝ (faceHull s),
    (D.level s i.castSucc ⟨p.1, intrinsicInterior_subset hx⟩ : ℝ) < p.2 ∧
      p.2 < (D.level s i.succ ⟨p.1, intrinsicInterior_subset hx⟩ : ℝ)}

/-- The cylinder has a finite triangulation over the base in which each open simplex maps
into a single section graph or open band. -/
def SimplicialSectionBandTriangulation : Prop :=
  ∀ (σ : Type u) [Finite σ] (K : Geometry.SimplicialComplex ℝ (σ → ℝ)),
    K.faces.Finite → ∀ (a b : ℝ), a < b → ∀ (D : LevelFamily K a b),
      ∃ (L : Geometry.SimplicialComplex ℝ ((σ → ℝ) × ℝ))
        (e : L.space ≃ₜ ↥(K.space ×ˢ Set.Icc a b)),
        L.faces.Finite ∧
          (∀ x : L.space, (e x).val.1 = x.val.1) ∧
          ∀ t ∈ L.faces,
            let interior := intrinsicInterior ℝ (convexHull ℝ (t : Set ((σ → ℝ) × ℝ)))
            let image := (fun x : L.space => (e x).val) '' (Subtype.val ⁻¹' interior)
            ∃ s : Face K,
              (∃ i, image ⊆ sectionGraph D s i) ∨ (∃ i, image ⊆ openBand D s i)

end RepTheorySurvey.Geometric.SimplicialSectionBandTriangulationSpecs
