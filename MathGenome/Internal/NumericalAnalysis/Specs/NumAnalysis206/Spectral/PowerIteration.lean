import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped BigOperators NNReal
open Filter

namespace NumAnalysis206.PowerIterationDefinitions
open MatrixDefinitions
variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]

/-- Normalization in the actual norm on the vector space. -/
def unitVector (x : E) : E := ((‖x‖ : K)⁻¹) • x

/-- The source's unit power iterates with the complex phase (or real sign) removed. -/
def correctedDirection (T : Module.End K E) (lam : K) (x : E) (j : ℕ) : E :=
  (((‖lam‖ : K) / lam) ^ j) • unitVector (K := K) ((T ^ j) x)

variable [FiniteDimensional K E]

/-- Distinct eigenvalues other than the dominant one; no basis choices or multiplicities. -/
def otherEigenvalues (T : Module.End K E) (lam : K) : Finset K := by
  classical
  exact T.finite_hasEigenvalue.toFinset.erase lam

/-- Maximum of the nonnegative ratios; the maximum of the empty set is zero. -/
def convergenceRatio (T : Module.End K E) (lam : K) : ℝ :=
  ((otherEigenvalues T lam).sup (fun μ => ‖μ / lam‖₊) : ℝ≥0)

/-- Sum of norms of the complete nondominant spectral components. -/
def remainderSize (T : Module.End K E) (hT : IsDiagonalizable T) (lam : K) (x : E) : ℝ :=
  ∑ μ ∈ otherEigenvalues T lam, ‖spectralComponent T hT μ x‖

end NumAnalysis206.PowerIterationDefinitions

namespace Specs.NumAnalysis206.PowerIteration
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.PowerIterationDefinitions

/-- W44, uniformly for real and complex matrices, with the explicit geometric bound. -/
def power_iteration : Prop :=
  ∀ {K : Type} [RCLike K] {n : ℕ} (A : Mat K n n)
    (hA : IsDiagonalizable A.toEuclideanLin) (lam : K) (x : Vec K n),
    lam ≠ 0 → (∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → μ ≠ lam → ‖μ‖ < ‖lam‖) →
    spectralComponent A.toEuclideanLin hA lam x ≠ 0 →
    (∀ j : ℕ, (A.toEuclideanLin ^ j) x ≠ 0) ∧
    (0 ≤ convergenceRatio A.toEuclideanLin lam ∧ convergenceRatio A.toEuclideanLin lam < 1) ∧
    (∀ j : ℕ, 1 ≤ j →
      ‖correctedDirection A.toEuclideanLin lam x j -
        unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x)‖ ≤
      2 * convergenceRatio A.toEuclideanLin lam ^ j *
        remainderSize A.toEuclideanLin hA lam x / ‖spectralComponent A.toEuclideanLin hA lam x‖) ∧
    Tendsto (correctedDirection A.toEuclideanLin lam x) atTop
      (nhds (unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x))) ∧
    Asymptotics.IsBigO atTop
      (fun j : ℕ => correctedDirection A.toEuclideanLin lam x j -
        unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x))
      (fun j : ℕ => convergenceRatio A.toEuclideanLin lam ^ j)

/-- This includes the empty set of other eigenvalues and hence the single-distinct-eigenvalue case. -/
def exact_when_other_eigenvalues_zero : Prop :=
  ∀ {K : Type} [RCLike K] {n : ℕ} (A : Mat K n n)
    (hA : IsDiagonalizable A.toEuclideanLin) (lam : K) (x : Vec K n),
    lam ≠ 0 → (∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → μ ≠ lam → μ = 0) →
    spectralComponent A.toEuclideanLin hA lam x ≠ 0 →
    convergenceRatio A.toEuclideanLin lam = 0 ∧
    ∀ j : ℕ, 1 ≤ j → correctedDirection A.toEuclideanLin lam x j =
      unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x)

/-- With only one distinct eigenvalue the corrected directions are exact even at j = 0. -/
def exact_single_eigenvalue : Prop :=
  ∀ {K : Type} [RCLike K] {n : ℕ} (A : Mat K n n)
    (hA : IsDiagonalizable A.toEuclideanLin) (lam : K) (x : Vec K n),
    lam ≠ 0 → (∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → μ = lam) →
    spectralComponent A.toEuclideanLin hA lam x ≠ 0 →
    convergenceRatio A.toEuclideanLin lam = 0 ∧
    ∀ j : ℕ, correctedDirection A.toEuclideanLin lam x j =
      unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x)

/-- For real data the phase is the usual sign, including a negative dominant eigenvalue. -/
def real_phase_is_sign : Prop :=
  ∀ lam : ℝ, lam ≠ 0 → ‖lam‖ / lam = if 0 < lam then (1 : ℝ) else -1

end Specs.NumAnalysis206.PowerIteration
