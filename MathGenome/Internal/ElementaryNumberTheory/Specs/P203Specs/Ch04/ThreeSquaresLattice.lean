import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Int.GCD

/-! The lattice stage of Theorem 4.10, paper.tex:1944–1967.
The parameters n and b are positive natural numbers; r,s,t,u,v are integers.
All lengths and volumes are those of Euclidean three-space. -/
noncomputable section
namespace P203Specs.Ch04
open MeasureTheory

def latticeW (b : ℕ) (u r s : ℤ) : ℤ := b * r + u * s

def latticeX (n b : ℕ) (u v r s t : ℤ) : ℤ := v * latticeW b u r s + n * t

def latticeS (n b : ℕ) (u r s : ℤ) : ℤ :=
  b * r ^ 2 + 2 * u * r * s + ((u ^ 2 + n) / b) * s ^ 2

def threeSquaresMatrix (n b : ℕ) (u v : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(v : ℝ) * b, (v : ℝ) * u, n;
     (b : ℝ) / Real.sqrt b, (u : ℝ) / Real.sqrt b, 0;
     0, Real.sqrt ((n : ℝ) / b), 0]

def threeSquaresPoint (n b : ℕ) (u v r s t : ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(latticeX n b u v r s t : ℝ),
    (latticeW b u r s : ℝ) / Real.sqrt b,
    Real.sqrt ((n : ℝ) / b) * s]

def threeSquaresLatticeGeometry : Prop :=
  ∀ (n b : ℕ) (u v : ℤ), 0 < n → 0 < b →
    (∀ r s t : ℤ,
      WithLp.toLp 2 ((threeSquaresMatrix n b u v).mulVec
        (fun i ↦ (![r, s, t] i : ℝ))) = threeSquaresPoint n b u v r s t) ∧
    (threeSquaresMatrix n b u v).det =
      (n : ℝ) * Real.sqrt b * Real.sqrt ((n : ℝ) / b) ∧
    (threeSquaresMatrix n b u v).det = (n : ℝ) * Real.sqrt n ∧
    0 < (threeSquaresMatrix n b u v).det ∧
    |(threeSquaresMatrix n b u v).det| = (n : ℝ) ^ (3 / 2 : ℝ) ∧
    volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3))
      (Real.sqrt (2 * (n : ℝ)))) =
      (8 * Real.sqrt 2 * Real.pi / 3) * (n : ℝ) ^ (3 / 2 : ℝ) ∧
    8 * (n : ℝ) ^ (3 / 2 : ℝ) <
      volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3))
        (Real.sqrt (2 * (n : ℝ))))

def threeSquaresLattice : Prop :=
  ∀ (n b : ℕ) (u v : ℤ), 0 < n → 0 < b → n.Coprime b →
    (b : ℤ) ∣ u ^ 2 + n → (n : ℤ) ∣ (b : ℤ) * v ^ 2 + 1 →
    ∃ r s t : ℤ,
      let S := latticeS n b u r s
      let X := latticeX n b u v r s t
      let W := latticeW b u r s
      threeSquaresPoint n b u v r s t ≠ 0 ∧
      threeSquaresPoint n b u v r s t ∈
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * (n : ℝ))) ∧
      ((threeSquaresPoint n b u v r s t) 0 : ℝ) = X ∧
      (S : ℝ) = ((threeSquaresPoint n b u v r s t) 1) ^ 2 +
        ((threeSquaresPoint n b u v r s t) 2) ^ 2 ∧
      (S : ℝ) = ((W : ℝ) ^ 2 + n * (s : ℝ) ^ 2) / b ∧
      (n : ℤ) ∣ X ^ 2 + S ∧
      0 < X ^ 2 + S ∧ X ^ 2 + S < 2 * (n : ℤ) ∧
      X ^ 2 + S = n ∧ 0 ≤ S ∧ S ≤ n ∧
      (b : ℤ) * S = W ^ 2 + n * s ^ 2
end P203Specs.Ch04
