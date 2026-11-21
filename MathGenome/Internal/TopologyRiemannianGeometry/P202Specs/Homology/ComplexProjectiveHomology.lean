import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularComparison
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! The complex projective quotient, its standard coordinate filtration, and
    the integral homology obligation of paper.tex 1599–1602, 1630–1635.
    The topology is the quotient of the nonzero complex vectors. -/
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits

namespace P202.ComplexProjective

/-- Actual complex projective m-space, before any cell structure is chosen. -/
def Space (m : ℕ) := Projectivization ℂ (Fin (m+1) → ℂ)

instance (m : ℕ) : TopologicalSpace (Space m) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (Fin (m+1) → ℂ))))

def mk {m : ℕ} (v : Fin (m+1) → ℂ) (hv : v ≠ 0) : Space m :=
  Projectivization.mk ℂ v hv

def quotientMap (m : ℕ) : {v : Fin (m+1) → ℂ // v ≠ 0} → Space m :=
  fun v => mk v.val v.property

/-- The coordinate projective r-plane, expressed without choosing a representative.
    r = -1 is encoded by `lowerSpace m 0`; `lowerSpace m (r+1)` is CP^r. -/
def lowerSpace (m k : ℕ) : Set (Space m) :=
  {p | ∃ (v : Fin (m+1) → ℂ) (hv : v ≠ 0), mk v hv = p ∧
    ∀ i, k ≤ i.val → v i = 0}

def stratum (m r : ℕ) : Set (Space m) := lowerSpace m (r+1) \ lowerSpace m r

/-- Zero-padding an affine chart in the coordinate projective r-plane. -/
def coordinateVector (m r : ℕ) (z : Fin r → ℂ) (t : ℂ) : Fin (m+1) → ℂ :=
  fun i => if h : i.val < r then z ⟨i.val, h⟩ else if i.val = r then t else 0

lemma coordinateVector_nonzero (m r : ℕ) (h : r ≤ m) (z : Fin r → ℂ) :
    coordinateVector m r z 1 ≠ 0 := by
  intro hz
  have := congrFun hz ⟨r, by omega⟩
  simpa [coordinateVector] using this

def affineChart (m r : ℕ) (h : r ≤ m) (z : Fin r → ℂ) : Space m :=
  mk (coordinateVector m r z 1) (coordinateVector_nonzero m r h z)

abbrev ComplexDisk (r : ℕ) := Metric.closedBall (0 : EuclideanSpace ℂ (Fin r)) 1

/-- The homogeneous vector (z, sqrt(1-|z|^2), 0, ..., 0). -/
def diskVector (m r : ℕ) (z : ComplexDisk r) : Fin (m+1) → ℂ :=
  coordinateVector m r (fun i => z.val i) (Real.sqrt (1 - ‖z.val‖ ^ 2))

lemma diskVector_nonzero (m r : ℕ) (h : r ≤ m) (z : ComplexDisk r) :
    diskVector m r z ≠ 0 := by
  intro hz
  have hz0 : z.val = 0 := by
    ext i
    have hi := congrFun hz ⟨i.val, by omega⟩
    simpa [diskVector, coordinateVector, i.isLt] using hi
  have hi := congrFun hz ⟨r, by omega⟩
  simpa [diskVector, coordinateVector, hz0] using hi

def characteristic (m r : ℕ) (h : r ≤ m) (z : ComplexDisk r) : Space m :=
  mk (diskVector m r z) (diskVector_nonzero m r h z)

/-- Linear zero-padding gives the specified nested projective subspaces. -/
def inclusionVector (m r : ℕ) (h : r ≤ m) : (Fin (r+1) → ℂ) →ₗ[ℂ] (Fin (m+1) → ℂ) where
  toFun v i := if hi : i.val < r+1 then v ⟨i.val, hi⟩ else 0
  map_add' v w := by ext i; dsimp; split <;> simp
  map_smul' a v := by ext i; dsimp; split <;> simp

lemma inclusionVector_injective (m r : ℕ) (h : r ≤ m) :
    Function.Injective (inclusionVector m r h) := by
  intro v w hvw
  ext i
  have hi := congrFun hvw ⟨i.val, by omega⟩
  simpa [inclusionVector, Nat.le_of_lt_succ i.isLt] using hi

def inclusion (m r : ℕ) (h : r ≤ m) : Space r → Space m :=
  Projectivization.map (inclusionVector m r h) (inclusionVector_injective m r h)

/-- Cell labels for the required standard finite CW decomposition. -/
def CellIndex (m n : ℕ) := {r : Fin (m+1) // n = 2 * r.val}

namespace Expected
open P202.Cellular P202Specs.SingularChains

/-- The actual coordinate subspaces, with their subspace topology. -/
def nestedSubspaces : Prop := ∀ m r (h : r ≤ m),
  IsEmbedding (inclusion m r h) ∧ range (inclusion m r h) = lowerSpace m (r+1)

/-- The last nonzero homogeneous coordinate is normalized to one. -/
def coordinateCells : Prop := ∀ m r (h : r ≤ m),
  IsEmbedding (affineChart m r h) ∧ range (affineChart m r h) = stratum m r

/-- Standard characteristic balls, boundary landing, and the actual CW structure
    on the quotient topology. The real isometries identify C^r with R^(2r). -/
def cellStructure : Prop := ∀ m,
  ∃ (C : CWStructure (Space m))
    (labels : ∀ n, C.toCellStructure.Cell n ≃ CellIndex m n),
    letI : CWStructure (Space m) := C
    (∀ n (c : Cell (Space m) n), openCell (Space m) n c =
      stratum m ((labels n c).val.val)) ∧
    (∀ r (h : r ≤ m), ∃ e : EuclideanSpace ℝ (Fin (2*r)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℂ (Fin r),
      ∀ c : Cell (Space m) (2*r), ∀ z : Disk (2*r),
        P202.Cellular.characteristic (Space m) (2*r) c z =
          characteristic m r h ⟨e z.val, by
            simpa only [Metric.mem_closedBall, dist_zero_right, e.norm_map] using z.property⟩) ∧
    (∀ r (h : r ≤ m) (z : ComplexDisk r), ‖z.val‖ = 1 →
      characteristic m r h z ∈ lowerSpace m r)

/-- Includes m=0; integral coefficients on the actual quotient. -/
def homology : Prop := ∀ m j : ℕ,
  ( (∃ r ≤ m, j = 2*r) →
      Nonempty (P202Specs.SingularChains.homology ℤ ℤ (TopCat.of (Space m)) (j : ℤ)
        ≃ₗ[ℤ] ℤ)) ∧
  ( (¬ ∃ r ≤ m, j = 2*r) →
      IsZero (P202Specs.SingularChains.homology ℤ ℤ (TopCat.of (Space m)) (j : ℤ)))

/-- The boundary case is explicitly a point as a topological space. -/
def pointCase : Prop := Nonempty (Space 0 ≃ₜ PUnit.{1})

end Expected
end P202.ComplexProjective
