import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

namespace RepTheorySurvey.Geometric.GeometricBarycentricSubdivisionSpecs

open Geometry

universe u

/-- A finite geometric complex admits a subdivision with the same space. Each subdivided
face lies in the closed hull of its assigned original face. Its relative interior and at
least one of its vertices lie in the relative interior of that original face. -/
def ExistsBarycentricSubdivision : Prop :=
  ∀ (σ : Type u) [Finite σ] (K : SimplicialComplex ℝ (σ → ℝ)), K.faces.Finite →
    ∃ (L : SimplicialComplex ℝ (σ → ℝ)) (carrier : L.faces → K.faces),
      L.faces.Finite ∧ L.space = K.space ∧ Monotone carrier ∧
        ∀ s : L.faces,
          convexHull ℝ (s.val : Set (σ → ℝ)) ⊆ convexHull ℝ ((carrier s).val : Set (σ → ℝ)) ∧
          intrinsicInterior ℝ (convexHull ℝ (s.val : Set (σ → ℝ))) ⊆
            intrinsicInterior ℝ (convexHull ℝ ((carrier s).val : Set (σ → ℝ))) ∧
          ∃ v ∈ s.val, v ∈ intrinsicInterior ℝ (convexHull ℝ ((carrier s).val : Set (σ → ℝ)))

/-- The relative interiors of two distinct faces of a geometric complex are disjoint. -/
def DisjointFaceIntrinsicInteriors : Prop :=
  ∀ (σ : Type u) [Finite σ] (K : SimplicialComplex ℝ (σ → ℝ)) (s t : Finset (σ → ℝ)),
    s ∈ K.faces → t ∈ K.faces → s ≠ t →
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set (σ → ℝ))))
        (intrinsicInterior ℝ (convexHull ℝ (t : Set (σ → ℝ))))

end RepTheorySurvey.Geometric.GeometricBarycentricSubdivisionSpecs
