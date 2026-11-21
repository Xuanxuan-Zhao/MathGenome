import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.Flow
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.Determinant

/-! Independent specifications for the density part of
`prop:pde-transport-jacobian`, paper.tex:3687–3723.
The local transverse-data assertion is allocated to W01_transverse.
No variational equation, determinant formula, or transport certificate is
included in the hypotheses. The initial datum is merely locally integrable.
All functions below are real-valued representatives; time-zero values are
specified by the explicit construction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace P201Specs.Hyperbolic

abbrev flowJacobianType := {n : ℕ} →
  (ℝ → ℝ → Space n → Space n) → ℝ → Space n → ℝ

abbrev transportedDensityType := {n : ℕ} →
  (ℝ → ℝ → Space n → Space n) → (Space n → ℝ) → ℝ → Space n → ℝ

/-- The determinant of the actual spatial derivative of the supplied flow. -/
def flowJacobian {n : ℕ} (X : ℝ → ℝ → Space n → Space n)
    (t : ℝ) (y : Space n) : ℝ := (fderiv ℝ (X t 0) y).det

/-- Eulerian representative of the pushforward initial density. -/
def transportedDensity {n : ℕ} (X : ℝ → ℝ → Space n → Space n)
    (g : Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  g (X 0 t x) / flowJacobian X t (X 0 t x)

/-- Compact smooth tests may be nonzero at the initial time. They vanish in
a neighborhood of the terminal time in the slab. -/
structure ContinuityTest (n : ℕ) (T : ℝ) where
  toFun : ℝ × Space n → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  terminal : ∃ ε : ℝ, 0 < ε ∧
    ∀ t ∈ Icc (T - ε) T, ∀ x, toFun (t, x) = 0

/-- This is φ_t + b·∇φ, with the spatial differential applied to b. -/
def continuityTestDerivative {n : ℕ} {T : ℝ} (b : SlabField n T)
    (φ : ℝ × Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  deriv (fun r => φ (r, x)) t +
    fderiv ℝ (fun y => φ (t, y)) x (b.velocity (t, x))

/-- Weak initial-value continuity equation, including local integrability in
space-time and of every spatial slice. All integrals use Lebesgue measure.
The two integrability clauses ensure the displayed weak formula is an
identity of genuine integrals, including for data that are not globally L¹. -/
def IsDistributionalContinuitySolution {n : ℕ} {T : ℝ}
    (b : SlabField n T) (g : Space n → ℝ) (ρ : ℝ → Space n → ℝ) : Prop :=
  LocallyIntegrableOn (fun q : ℝ × Space n => ρ q.1 q.2)
    (Icc 0 T ×ˢ univ) (volume.prod volume) ∧
  (∀ t ∈ Icc 0 T, LocallyIntegrable (ρ t) volume) ∧
  ρ 0 = g ∧
  ∀ φ : ContinuityTest n T,
    Integrable (fun x => g x * φ.toFun (0, x)) volume ∧
    IntegrableOn (fun q : ℝ × Space n =>
      ρ q.1 q.2 * continuityTestDerivative b φ.toFun q.1 q.2)
      (Icc 0 T ×ˢ univ) (volume.prod volume) ∧
    IntegrableOn (fun t => ∫ x, ρ t x * continuityTestDerivative b φ.toFun t x)
      (Icc 0 T) volume ∧
    (∫ t in Icc 0 T, ∫ x, ρ t x * continuityTestDerivative b φ.toFun t x) =
      -(∫ x, g x * φ.toFun (0, x))

/-- Liouville's identity and positivity under precisely the upstream flow
hypotheses. X is any flow satisfying the proved upstream properties. -/
def flowJacobianStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ (b : SlabField n T)
    (X : ℝ → ℝ → Space n → Space n), SlabFlowProperties b X →
    ∀ t ∈ Icc 0 T, ∀ y,
      flowJacobian X t y = Real.exp
        (∫ r in (0 : ℝ)..t, divergence (fun x => b.velocity (r, x)) (X r 0 y)) ∧
      0 < flowJacobian X t y

/-- The explicit density is a locally integrable weak solution and has the
source's pointwise characteristic formula for the chosen representatives. -/
def transportedDensityStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ (b : SlabField n T)
    (X : ℝ → ℝ → Space n → Space n), SlabFlowProperties b X →
    ∀ g : Space n → ℝ, LocallyIntegrable g volume →
      IsDistributionalContinuitySolution b g (transportedDensity X g) ∧
      ∀ t ∈ Icc 0 T, ∀ y,
        transportedDensity X g t (X t 0 y) = g y / flowJacobian X t y

/-- Existence uses only the original coefficient hypotheses: a flow with all
the density conclusions must be constructed, not assumed as input data. -/
def densityFlowStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ b : SlabField n T,
    ∃ X : ℝ → ℝ → Space n → Space n,
      SlabFlowProperties b X ∧
      (∀ t ∈ Icc 0 T, ∀ y,
        flowJacobian X t y = Real.exp
          (∫ r in (0 : ℝ)..t, divergence (fun x => b.velocity (r, x)) (X r 0 y)) ∧
        0 < flowJacobian X t y) ∧
      ∀ g : Space n → ℝ, LocallyIntegrable g volume →
        IsDistributionalContinuitySolution b g (transportedDensity X g) ∧
        ∀ t ∈ Icc 0 T, ∀ y,
          transportedDensity X g t (X t 0 y) = g y / flowJacobian X t y

/-- Full assigned density obligation, independent of candidate proofs. -/
def continuityEquationStatement : Prop :=
  flowJacobianStatement ∧ transportedDensityStatement ∧ densityFlowStatement

end P201Specs.Hyperbolic
