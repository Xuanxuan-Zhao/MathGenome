import MathGenome.Internal.LinearPDE.P201Specs.Heat.GaussianKernel
import Mathlib.MeasureTheory.Integral.Prod

/-! Causal fundamental solution in the common Euclidean spatial coordinates.
Tests below are arbitrary smooth compactly supported real functions on space-time.
The integral is an ordinary absolutely integrable Lebesgue pairing. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace P201Specs.Heat

abbrev causalKernelType := (n : ℕ) → Space n × ℝ → ℝ

/-- The value at time zero is zero, as on the entire past half-space. -/
def causalKernel : causalKernelType := fun n z =>
  if 0 < z.2 then gaussianKernel n z.2 z.1 else 0

/-- The formal transpose of ∂ₜ − Δₓ on a real space-time test. -/
def adjointHeatTest {n : ℕ} (φ : Space n × ℝ → ℝ) (z : Space n × ℝ) : ℝ :=
  -deriv (fun t => φ (z.1, t)) z.2 - laplacian (fun x => φ (x, z.2)) z.1

def causalLocallyIntegrableStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → LocallyIntegrable (causalKernel n)

/-- Both product and iterated integral forms of the distribution equation.
Integrability is asserted explicitly, so the integral cannot be a default value
of the Bochner integral of a nonintegrable function. -/
def causalFundamentalStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ φ : Space n × ℝ → ℝ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Integrable (fun z => causalKernel n z * adjointHeatTest φ z) ∧
    (∫ z, causalKernel n z * adjointHeatTest φ z) = φ (0, 0) ∧
    (∫ t : ℝ, ∫ x : Space n,
      causalKernel n (x, t) * adjointHeatTest φ (x, t) ∂spatialMeasure n) = φ (0, 0)

end P201Specs.Heat
