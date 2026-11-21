import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.PowerIteration
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Residual
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped BigOperators NNReal
open Filter

namespace NumAnalysis206.InverseIterationDefinitions
open MatrixDefinitions PowerIterationDefinitions
variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]
  [FiniteDimensional K E]

/-- The shifted map, with its actual finite dimensional norm topology. -/
def shiftedEquiv (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T) : E ≃L[K] E := by
  have hk : LinearMap.ker (T - μ • 1) = ⊥ := by
    rw [← Module.End.eigenspace_def]
    exact not_ne_iff.mp (fun h => hμ (Module.End.HasEigenvalue.mem_spectrum h))
  have hi := LinearMap.ker_eq_bot.mp hk
  exact (LinearEquiv.ofBijective (T - μ • 1)
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv

/-- Inverse of the shifted map; this is an exact solve. -/
def inverseMap (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T) : Module.End K E :=
  (shiftedEquiv T μ hμ).symm.toLinearMap

/-- Each step solves and normalizes. At index zero we record the initial direction. -/
def normalizedIterate (B : Module.End K E) (x : E) : ℕ → E
  | 0 => unitVector (K := K) x
  | j + 1 => unitVector (K := K) (B (normalizedIterate B x j))

/-- The phase is that of the dominant eigenvalue of the inverse, (λ - μ)⁻¹. -/
def inverseDirection (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T)
    (lam : K) (x : E) (j : ℕ) : E :=
  (((‖(lam - μ)⁻¹‖ : K) / (lam - μ)⁻¹) ^ j) •
    normalizedIterate (inverseMap T μ hμ) x j

/-- The maximum runs over distinct eigenvalues of A other than λ, with empty max zero. -/
def inverseRatio (T : Module.End K E) (μ lam : K) : ℝ :=
  ((otherEigenvalues T lam).sup (fun ν => ‖(lam - μ) / (ν - μ)‖₊) : ℝ≥0)

end NumAnalysis206.InverseIterationDefinitions

namespace Specs.NumAnalysis206.InverseIteration
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.PowerIterationDefinitions
open _root_.NumAnalysis206.InverseIterationDefinitions

/-- W45: exact solves are defined, repeated normalization preserves the power direction,
and the corrected directions converge with the stated original-spectrum factor. -/
def inverse_iteration : Prop :=
  ∀ {K : Type} [RCLike K] {n : ℕ} (A : Mat K n n)
    (hA : IsDiagonalizable A.toEuclideanLin) (μ : K) (hμ : μ ∉ spectrum K A.toEuclideanLin)
    (lam : K) (x : Vec K n),
    (∀ ν, Module.End.HasEigenvalue A.toEuclideanLin ν → ν ≠ lam → ‖lam - μ‖ < ‖ν - μ‖) →
    spectralComponent A.toEuclideanLin hA lam x ≠ 0 →
    (∀ j : ℕ,
      (inverseMap A.toEuclideanLin μ hμ ^ j) x ≠ 0 ∧
      normalizedIterate (inverseMap A.toEuclideanLin μ hμ) x j =
        unitVector (K := K) ((inverseMap A.toEuclideanLin μ hμ ^ j) x) ∧
      inverseMap A.toEuclideanLin μ hμ
        (normalizedIterate (inverseMap A.toEuclideanLin μ hμ) x j) ≠ 0 ∧
      A.toEuclideanLin (inverseMap A.toEuclideanLin μ hμ
          (normalizedIterate (inverseMap A.toEuclideanLin μ hμ) x j)) -
        μ • inverseMap A.toEuclideanLin μ hμ
          (normalizedIterate (inverseMap A.toEuclideanLin μ hμ) x j) =
        normalizedIterate (inverseMap A.toEuclideanLin μ hμ) x j) ∧
    (0 ≤ inverseRatio A.toEuclideanLin μ lam ∧ inverseRatio A.toEuclideanLin μ lam < 1) ∧
    (∀ j : ℕ,
      ‖inverseDirection A.toEuclideanLin μ hμ lam x j -
          unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x)‖ ≤
        2 * inverseRatio A.toEuclideanLin μ lam ^ j *
          remainderSize A.toEuclideanLin hA lam x / ‖spectralComponent A.toEuclideanLin hA lam x‖) ∧
    Tendsto (inverseDirection A.toEuclideanLin μ hμ lam x) atTop
      (nhds (unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x))) ∧
    Asymptotics.IsBigO atTop
      (fun j : ℕ => inverseDirection A.toEuclideanLin μ hμ lam x j -
        unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x))
      (fun j : ℕ => inverseRatio A.toEuclideanLin μ lam ^ j)

/-- One distinct eigenvalue: exact phase-adjusted direction, including index zero. -/
def exact_single_eigenvalue : Prop :=
  ∀ {K : Type} [RCLike K] {n : ℕ} (A : Mat K n n)
    (hA : IsDiagonalizable A.toEuclideanLin) (μ : K) (hμ : μ ∉ spectrum K A.toEuclideanLin)
    (lam : K) (x : Vec K n),
    (∀ ν, Module.End.HasEigenvalue A.toEuclideanLin ν → ν = lam) →
    spectralComponent A.toEuclideanLin hA lam x ≠ 0 →
    inverseRatio A.toEuclideanLin μ lam = 0 ∧
    ∀ j : ℕ, inverseDirection A.toEuclideanLin μ hμ lam x j =
      unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x)

/-- A rounded shifted solve has the W14 absolute residual certificate, even for zero data. -/
def rounded_solve_bound : Prop :=
  ∀ {K : Type} [RCLike K] {n : ℕ} (A : Mat K n n)
    (μ : K) (hμ : μ ∉ spectrum K A.toEuclideanLin) (x y yhat r : Vec K n),
    A.toEuclideanLin y - μ • y = x →
    A.toEuclideanLin yhat - μ • yhat = x - r →
    ‖yhat - y‖ ≤ ‖(shiftedEquiv A.toEuclideanLin μ hμ).symm.toContinuousLinearMap‖ * ‖r‖

end Specs.NumAnalysis206.InverseIteration
