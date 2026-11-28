import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

namespace RepTheorySurvey.Geometric.RealPolynomialChartTriangulationSpecs

universe u v

/-- The simultaneous zero locus of a finite system of real polynomial equations. -/
def zeroLocus {σ : Type u} (equations : Finset (MvPolynomial σ ℝ)) : Set (σ → ℝ) :=
  {x | ∀ p ∈ equations, MvPolynomial.aeval x p = 0}

/-- The strict coordinate interior of the box, with both inequalities at every coordinate. -/
def strictBox {σ : Type u} (a b : σ → ℝ) : Set (σ → ℝ) :=
  {x | ∀ i, a i < x i ∧ x i < b i}

/-- A subset of the realization is a union of relative interiors of faces. -/
def IsUnionOfFaceInteriors {σ : Type u} (K : Geometry.SimplicialComplex ℝ (σ → ℝ))
    (A : Set K.space) : Prop :=
  ∃ faces : Set (Finset (σ → ℝ)), faces ⊆ K.faces ∧
    A = ⋃ s ∈ faces,
      (Subtype.val : K.space → σ → ℝ) ⁻¹' intrinsicInterior ℝ (convexHull ℝ (s : Set (σ → ℝ)))

/-- A polynomial zero locus in a closed box has a finite triangulation compatible with the
other zero loci and with the coordinate boundary of the box. -/
def RealPolynomialChartTriangulation : Prop :=
  ∀ (σ : Type u) [Finite σ] (ι : Type v) [Finite ι]
    (equations : ι → Finset (MvPolynomial σ ℝ)) (base : ι) (a b : σ → ℝ),
    (∀ i, a i < b i) →
      let X : Set (σ → ℝ) := zeroLocus (equations base) ∩ Set.Icc a b
      ∃ (K : Geometry.SimplicialComplex ℝ (σ → ℝ)) (e : K.space ≃ₜ X),
        K.faces.Finite ∧
          (∀ j, IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' zeroLocus (equations j))) ∧
          IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' (Set.Icc a b \ strictBox a b))

end RepTheorySurvey.Geometric.RealPolynomialChartTriangulationSpecs
