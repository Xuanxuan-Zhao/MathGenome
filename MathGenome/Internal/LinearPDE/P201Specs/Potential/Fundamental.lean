import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Set TopologicalSpace MeasureTheory Metric
namespace P201Specs

/-- Radial profile of the fundamental solution for the positive Laplacian. -/
def fundamentalProfile (n : ℕ) (r : ℝ) : ℝ :=
  if n = 1 then -r / 2
  else if n = 2 then -(1 / (2 * Real.pi)) * Real.log r
  else r ^ (2 - (n : ℝ)) / (((n : ℝ) - 2) * omega n)

/-- The norm is Euclidean; the totalized real logarithm/power fixes the value at zero. -/
def fundamentalKernel (n : ℕ) (x : Space n) : ℝ := fundamentalProfile n ‖x‖

/-- Evaluation at the origin in the shared scalar-linear distribution space. -/
def originDirac (n : ℕ) : Distribution ℝ (⊤ : Domain n) where
  toFun φ := φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

def fundamentalKernelType := (n : ℕ) → Space n → ℝ
def fundamentalProfileType := ℕ → ℝ → ℝ
def originDiracType := (n : ℕ) → Distribution ℝ (⊤ : Domain n)

def fundamentalLocalIntegrabilityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → LocallyIntegrable (fundamentalKernel n) volume

def fundamentalSolutionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    -distributionLaplacian (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) =
      originDirac n

/-- Outward radial derivative and the total outward flux through every positive sphere. -/
def fundamentalFluxStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r →
    HasDerivAt (fundamentalProfile n) (-1 / (omega n * r ^ (n - 1))) r ∧
    deriv (fundamentalProfile n) r * (sphereSurface (0 : Space n) r).real univ = -1

/-- The two slopes at zero, including their signed jump. -/
def fundamentalJumpStatement : Prop :=
  (∀ t : ℝ, t < 0 → HasDerivAt (fun s : ℝ => -|s| / 2) (1 / 2) t) ∧
  (∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => -|s| / 2) (-1 / 2) t) ∧
  (-1 / 2 : ℝ) - (1 / 2) = -1

/-- Any value at the singular point gives the same locally integrable solution. -/
def fundamentalRepresentativeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : ℝ,
    let f := Function.update (fundamentalKernel n) 0 c
    LocallyIntegrable f volume ∧
      -distributionLaplacian (regularDistribution (⊤ : Domain n) f) = originDirac n

/-- Flux against the actual geometric outward normal x/r on the radius-r sphere. -/
def fundamentalOutwardFluxStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r →
    (∀ x : Space n, ‖x‖ = r →
      fderiv ℝ (fundamentalKernel n) x (r⁻¹ • x) = -1 / (omega n * r ^ (n - 1))) ∧
    (∫ x, fderiv ℝ (fundamentalKernel n) x (r⁻¹ • x)
      ∂sphereSurface (0 : Space n) r) = -1

end P201Specs
