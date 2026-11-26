import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

open Module

namespace LinearAlgebraicGroups.Arithmetic.RealLatticeReduction

/-- Euclidean length in the coordinate model. The underlying space of functions carries
the usual product topology. -/
noncomputable def euclideanLength {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 x‖

/-- The columns of the real matrix are the given integral basis vectors. -/
noncomputable def basisMatrix {n : ℕ} {L : Submodule ℤ (Fin n → ℝ)}
    (b : Basis (Fin n) ℤ L) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (b j : Fin n → ℝ) i

/-- A coordinate box for a matrix and its inverse. -/
def entriesBounded {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, |A i j| ≤ C

end LinearAlgebraicGroups.Arithmetic.RealLatticeReduction

namespace LinearAlgebraicGroups.Specs.RealLatticeReduction
open Arithmetic.RealLatticeReduction

/-- Uniform reduction of full real integer lattices, with Haar covolume and with
the resulting basis oriented to have determinant one. Coordinate bounds on the matrix
and its inverse are bounds in their finite-dimensional Euclidean spaces. -/
def boundedRealLatticeBasis : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
        ZLattice.covolume L = 1 →
        (∀ x ∈ L, x ≠ 0 → ε ≤ euclideanLength x) →
        ∃ b : Basis (Fin n) ℤ L, (basisMatrix b).det = 1 ∧
          entriesBounded C (basisMatrix b) ∧ entriesBounded C (basisMatrix b)⁻¹

/-- The same reduction starting with a real basis matrix. The change of columns is in
the integer general linear group, including when the input orientation is negative. -/
def boundedRealMatrixBasis : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ g : Matrix.GeneralLinearGroup (Fin n) ℝ, |g.val.det| = 1 →
        (∀ z : Fin n → ℤ, z ≠ 0 →
          ε ≤ euclideanLength (g.val.mulVec fun i => (z i : ℝ))) →
        ∃ γ : Matrix.GeneralLinearGroup (Fin n) ℤ,
          let h := g * Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ
          h.val.det = 1 ∧ entriesBounded C h.val ∧ entriesBounded C h⁻¹.val

end LinearAlgebraicGroups.Specs.RealLatticeReduction
