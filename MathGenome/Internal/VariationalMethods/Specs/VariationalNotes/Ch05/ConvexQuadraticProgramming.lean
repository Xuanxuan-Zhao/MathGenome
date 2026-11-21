import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.QuadraticProgramAttainment
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedralTangentNormal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Theorem `thm:convex-qp` in paper.tex. Coordinates of Euclidean vectors
are passed to the shared quadratic objective. The normal is the shared
continuous-dual normal, with vectors identified by the Riesz map.
Finite index types and the ambient dimension are allowed to be empty. -/
noncomputable section
open Set Matrix
namespace VariationalNotes.Ch05.Specs

/-- Finite real infima are attained, including singular Q and dimension zero. -/
def convexQP_attainment : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (P : Set (EuclideanSpace ℝ (Fin n))) (p : ℝ),
    Q.PosSemidef → ConvexGeometry.Specs.IsPolyhedron P → P.Nonempty →
    IsGLB ((fun x : EuclideanSpace ℝ (Fin n) => quadraticObjective Q c x.ofLp) '' P) p →
    ∃ x ∈ P, quadraticObjective Q c x.ofLp = p

def convexQP_optimal_iff_normal : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (P : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)),
    Q.PosSemidef → ConvexGeometry.Specs.IsPolyhedron P → x ∈ P →
    ((∀ y ∈ P, quadraticObjective Q c x.ofLp ≤ quadraticObjective Q c y.ofLp) ↔
      InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
        (-(WithLp.toLp 2 (Q *ᵥ x.ofLp + c))) ∈ ConvexGeometry.Specs.normalCone P x)

def convexQP_normal_iff_kkt : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    {I J : Type} [Fintype I] [Fintype J]
    (a : I → EuclideanSpace ℝ (Fin n)) (b : I → ℝ)
    (e : J → EuclideanSpace ℝ (Fin n)) (d : J → ℝ)
    (x : EuclideanSpace ℝ (Fin n)),
    x ∈ ConvexGeometry.Specs.polyhedralSet a b e d →
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
        (-(WithLp.toLp 2 (Q *ᵥ x.ofLp + c))) ∈
          ConvexGeometry.Specs.normalCone (ConvexGeometry.Specs.polyhedralSet a b e d) x ↔
      ∃ (lam : I → ℝ) (nu : J → ℝ),
        (∀ i, 0 ≤ lam i) ∧
        WithLp.toLp 2 (Q *ᵥ x.ofLp + c) +
          (∑ i, lam i • a i) + (∑ j, nu j • e j) = 0 ∧
        (∀ i, lam i * (inner ℝ (a i) x - b i) = 0))

def convexQP_optimal_iff_kkt : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    {I J : Type} [Fintype I] [Fintype J]
    (a : I → EuclideanSpace ℝ (Fin n)) (b : I → ℝ)
    (e : J → EuclideanSpace ℝ (Fin n)) (d : J → ℝ)
    (x : EuclideanSpace ℝ (Fin n)),
    Q.PosSemidef → x ∈ ConvexGeometry.Specs.polyhedralSet a b e d →
    ((∀ y ∈ ConvexGeometry.Specs.polyhedralSet a b e d,
        quadraticObjective Q c x.ofLp ≤ quadraticObjective Q c y.ofLp) ↔
      ∃ (lam : I → ℝ) (nu : J → ℝ),
        (∀ i, 0 ≤ lam i) ∧
        WithLp.toLp 2 (Q *ᵥ x.ofLp + c) +
          (∑ i, lam i • a i) + (∑ j, nu j • e j) = 0 ∧
        (∀ i, lam i * (inner ℝ (a i) x - b i) = 0))

end VariationalNotes.Ch05.Specs
