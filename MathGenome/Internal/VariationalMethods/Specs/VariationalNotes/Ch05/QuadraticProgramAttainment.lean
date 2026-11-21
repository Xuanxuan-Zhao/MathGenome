import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedraElimination
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Bounds.Basic

/-! The attainment assertion of paper.tex, Theorem `thm:convex-qp`
(lines 2312–2347). `Matrix.PosSemidef` includes Hermitian symmetry,
which over ℝ is precisely symmetry. `IsGLB` specifies a finite real
infimum without the default value of the conditional real `sInf`.
Neither the matrix rank nor the boundedness of the polyhedron is restricted. -/

noncomputable section
open Set Matrix
namespace VariationalNotes.Ch05.Specs

/-- The original objective, including its factor of one half. -/
def quadraticObjective {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (c x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ (Q *ᵥ x)) / 2 + c ⬝ᵥ x

/-- Finite-value attainment, including singular Q and dimension zero. -/
def quadraticProgram_attains_infimum : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (P : Set (Fin n → ℝ)) (p : ℝ),
    Q.PosSemidef → ConvexGeometry.Specs.IsPolyhedron P → P.Nonempty →
    IsGLB (quadraticObjective Q c '' P) p →
    ∃ x ∈ P, quadraticObjective Q c x = p

end VariationalNotes.Ch05.Specs
