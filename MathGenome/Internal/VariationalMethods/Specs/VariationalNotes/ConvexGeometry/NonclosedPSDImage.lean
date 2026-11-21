import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent specification of the example in paper.tex:601–614.
The ambient space is the space of real 2 by 2 matrices; symmetry is explicitly
part of membership in the cone. Positivity is tested on every real vector.
The example is thus available in matrix form to the later SDP discussion. -/

noncomputable section
open Set

namespace VariationalNotes.ConvexGeometry.Specs.PSDImage

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

def symmetricMatrixType := ℝ → ℝ → ℝ → Matrix2

def symmetricMatrix (a b c : ℝ) : Matrix2 := !![a, b; b, c]

def quadraticFormType := Matrix2 → ℝ → ℝ → ℝ

def quadraticForm (M : Matrix2) (u v : ℝ) : ℝ :=
  M 0 0 * u ^ 2 + (M 0 1 + M 1 0) * u * v + M 1 1 * v ^ 2

def psdConeType := Set Matrix2

def psdCone : Set Matrix2 := {M | M.IsSymm ∧ ∀ u v : ℝ, 0 ≤ quadraticForm M u v}

def projectionType := Matrix2 →ₗ[ℝ] (ℝ × ℝ)

def projection : Matrix2 →ₗ[ℝ] (ℝ × ℝ) where
  toFun M := (M 0 0, M 0 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projectedConeType := Set (ℝ × ℝ)

def projectedCone : Set (ℝ × ℝ) := projection '' psdCone

def symmetricMatrix_isSymm : Prop := ∀ a b c : ℝ, (symmetricMatrix a b c).IsSymm

def symmetricMatrix_representation : Prop :=
  ∀ M : Matrix2, M.IsSymm → M = symmetricMatrix (M 0 0) (M 0 1) (M 1 1)

/-- This identifies the polynomial with the full matrix quadratic form. -/
def quadraticForm_eq_matrix_sum : Prop := ∀ (M : Matrix2) (w : Fin 2 → ℝ),
  quadraticForm M (w 0) (w 1) = ∑ i, ∑ j, w i * M i j * w j

def psdCone_closed : Prop := IsClosed psdCone

def psdCone_isCone : Prop := VariationalNotes.ConvexGeometry.Specs.IsCone psdCone

def psdCone_convex : Prop := Convex ℝ psdCone

def psd_first_entry_nonneg : Prop := ∀ M ∈ psdCone, 0 ≤ M 0 0

def psd_zero_first_entry : Prop := ∀ M ∈ psdCone, M 0 0 = 0 → M 0 1 = 0

def positive_psd_lift : Prop :=
  ∀ a b : ℝ, 0 < a → symmetricMatrix a b (b ^ 2 / a) ∈ psdCone

def projectedCone_description : Prop :=
  projectedCone = {p : ℝ × ℝ | 0 < p.1} ∪ {(0, 0)}

def target_mem_closure : Prop := (0, 1) ∈ closure projectedCone

def target_not_mem : Prop := (0, 1) ∉ projectedCone

def projectedCone_not_closed : Prop := ¬ IsClosed projectedCone

end VariationalNotes.ConvexGeometry.Specs.PSDImage
