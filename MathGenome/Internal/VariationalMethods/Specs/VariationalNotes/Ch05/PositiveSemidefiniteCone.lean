import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.OrthantLorentzCones
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Independent scope for paper.tex, Proposition `prop:standard-self-dual-cones`.
Symmetric matrices carry the Euclidean norm of their entries. This is the
Frobenius inner product, whose restriction is proved to equal `trace (S * T)`.
All dimensions, including zero, are allowed. The cone uses native `PosSemidef`;
the quadratic-form bridge fixes its interpretation on the symmetric subspace. -/
noncomputable section
open Matrix
universe u v
namespace VariationalNotes.Ch05.PositiveSemidefiniteCone.Specs

/-- Symmetric arrays, realized as a subspace of the Euclidean space of entries. -/
def symmetricMatrices (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n)) where
  carrier := {x | ∀ i j, x (i, j) = x (j, i)}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i j; simp [hx i j, hy i j]
  smul_mem' := by intro r x hx i j; simp [hx i j]

abbrev SymmetricMatrix (n : ℕ) : Type := symmetricMatrices n

def matrix {n : ℕ} (S : SymmetricMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => S.val (i, j)

def psdCone (n : ℕ) : Set (SymmetricMatrix n) := {S | (matrix S).PosSemidef}

def symmetricMatricesType := (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n))
def SymmetricMatrixType : Type 1 := ℕ → Type
def matrixType := ∀ {n : ℕ}, SymmetricMatrix n → Matrix (Fin n) (Fin n) ℝ
def psdConeType := (n : ℕ) → Set (SymmetricMatrix n)

def matrix_symmetric : Prop := ∀ {n : ℕ} (S : SymmetricMatrix n), (matrix S).IsSymm

/-- The entry realization includes exactly all real symmetric matrices. -/
def matrix_range : Prop := ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ),
  (∃ S : SymmetricMatrix n, matrix S = M) ↔ M.IsSymm

def mem_psdCone_iff : Prop := ∀ {n : ℕ} (S : SymmetricMatrix n),
  S ∈ psdCone n ↔ ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (matrix S *ᵥ v)

def trace_inner : Prop := ∀ {n : ℕ} (S T : SymmetricMatrix n),
  inner ℝ S T = Matrix.trace (matrix S * matrix T)

def psd_properties : Prop := ∀ n : ℕ,
  IsClosed (psdCone n) ∧ Convex ℝ (psdCone n) ∧
  VariationalNotes.ConvexGeometry.Specs.IsCone (psdCone n) ∧
  ConicProgramModels.Specs.innerPositiveDual (psdCone n) = psdCone n

/-- The complete proposition, with each cone's own space and pairing. -/
def standard_self_dual_cones : Prop :=
  OrthantLorentzCones.Specs.orthant_properties.{u} ∧
  OrthantLorentzCones.Specs.lorentz_properties.{v} ∧ psd_properties

end VariationalNotes.Ch05.PositiveSemidefiniteCone.Specs
