import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleModel
import Mathlib.Analysis.Convex.Hull

/-! The geometric conclusions for the very same affine cells occurring in the
finite shuffle chain. These propositions do not assume a triangulation. -/
noncomputable section
namespace P202Specs.ShuffleTriangulation
open P202Specs.ShuffleModel

/-- Ordered product of the usual ordered simplex edge bases
`e₁-e₀,…,eₚ-e₀`, followed by `f₁-f₀,…,f_q-f₀`. -/
def standardProductVector (p q : ℕ) (j : Fin (p+q)) : Ambient p × Ambient q :=
  if j.val < p then
    (fun k => (if k.val = j.val+1 then 1 else 0) - (if k.val = 0 then 1 else 0), 0)
  else
    (0, fun k => (if k.val = j.val-p+1 then 1 else 0) - (if k.val = 0 then 1 else 0))

/-- Coordinates in the standard ordered simplex edge bases, with the first
factor preceding the second. On a difference of simplex points, the omitted
zeroth coordinates are minus the sums of these coordinates. -/
def standardProductCoordinates (p q : ℕ) (a : Ambient p × Ambient q) : Fin (p+q) → ℝ :=
  fun i => if hi : i.val < p then a.1 ⟨i.val+1, by omega⟩
    else a.2 ⟨i.val-p+1, by have := i.isLt; omega⟩

/-- The actual ordered vertex-difference matrix in the standard product basis. -/
def standardOrientationMatrix {p q : ℕ} (s : LatticePath p q) :
    Matrix (Fin (p+q)) (Fin (p+q)) ℝ :=
  fun i j => standardProductCoordinates p q (vertex s j.succ) i -
    standardProductCoordinates p q (vertex s 0) i

def standard_orientation_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  Matrix.det (standardOrientationMatrix s) = (s.sign : ℝ)

def injectivity_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  Function.Injective (parametrization s)

def coverage_type : Prop := ∀ (p q : ℕ) (z : StdSimplex p × StdSimplex q),
  ∃ (s : LatticePath p q) (x : StdSimplex (p+q)), parametrization s x = z

def common_face_type : Prop := ∀ {p q : ℕ} (s t : LatticePath p q),
  cell s ∩ cell t = convexHull ℝ (commonVertices s t)

def triangulation_type : Prop := ∀ (p q : ℕ),
  (∀ s : LatticePath p q, Function.Injective (parametrization s)) ∧
  (∀ z : StdSimplex p × StdSimplex q,
    ∃ (s : LatticePath p q) (x : StdSimplex (p+q)), parametrization s x = z) ∧
  (∀ s t : LatticePath p q,
    cell s ∩ cell t = convexHull ℝ (commonVertices s t))

/-- Determinant in the canonical shared tail coordinates. -/
def orientation_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  Matrix.det (orientationMatrix s) = (s.sign : ℝ)

/-- These coordinates give determinant one on the standard ordered product
basis. Thus the preceding determinant uses the standard product orientation. -/
def standard_basis_orientation_type : Prop := ∀ (p q : ℕ),
  Matrix.det (fun i j : Fin (p+q) =>
    productCoordinates p q (standardProductVector p q j) i) = 1

end P202Specs.ShuffleTriangulation
