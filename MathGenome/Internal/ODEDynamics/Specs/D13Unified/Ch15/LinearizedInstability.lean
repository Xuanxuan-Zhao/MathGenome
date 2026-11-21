import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.AdaptedNorm
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Independent local first-exit statement for paper.tex, Theorem
`d13:15:linearized-instability`. A total function represents its restriction
on `V`. No continuity, differentiability, or dynamical assumption is imposed
outside a neighborhood of `p`; the conclusion only evaluates it at points
of `V`. In particular `F V ⊆ V` is not assumed, and the exiting point need
not belong to `V`. -/
noncomputable section
open Module Set
namespace D13Unified.Ch15.LinearizedInstability

/-- A finite first exit. Each input at which `F` is evaluated belongs to `V`. -/
def FirstExit {E : Type} [NormedAddCommGroup E]
    (F : E → E) (V : Set E) (p x : E) (ε : ℝ) (N : ℕ) : Prop :=
  0 < N ∧ ε ≤ ‖F^[N] x - p‖ ∧
    ∀ n : ℕ, n < N → ‖F^[n] x - p‖ < ε ∧ F^[n] x ∈ V

/-- Instability with a fixed ball and arbitrarily small perturbations. -/
def LocallyUnstable {E : Type} [NormedAddCommGroup E]
    (F : E → E) (V : Set E) (p : E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ V ∧
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ V, ‖x - p‖ < δ ∧
      ∃ N : ℕ, FirstExit F V p x ε N

/-- Two projected norms with a strict expansion gap. This is proof data,
not an additional hypothesis of the linearized-instability theorem. -/
structure ConeData {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) where
  unstable : Seminorm ℝ E
  complementary : Seminorm ℝ E
  a : ℝ
  b : ℝ
  a_gt_one : 1 < a
  b_nonneg : 0 ≤ b
  gap : b < a
  C : ℝ
  D : ℝ
  C_pos : 0 < C
  D_pos : 0 < D
  lower : ∀ v, ‖v‖ ≤ C * (unstable v + complementary v)
  upper : ∀ v, unstable v + complementary v ≤ D * ‖v‖
  expands : ∀ v, a * unstable v ≤ unstable (A v)
  controls : ∀ v, complementary (A v) ≤ b * complementary v
  direction : E
  direction_pos : 0 < unstable direction
  direction_complementary : complementary direction = 0

end D13Unified.Ch15.LinearizedInstability
namespace Specs.D13Unified.Ch15.LinearizedInstability
open _root_.D13Unified.Ch15.LinearizedInstability
open _root_.D13Unified.Ch08.MatrixPowerCriteria

/-- The complex eigenvalue condition refers to the complexification of
all real coordinates, including nonreal pairs and nontrivial Jordan blocks.
The remaining spectral values have no restrictions. -/
def linearizedInstability : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (basis : Basis (Fin d) ℝ E)
    (F : E → E) (V : Set E) (p : E) (A : E →L[ℝ] E),
    IsOpen V → p ∈ V → F p = p → ContDiffAt ℝ 1 F p → HasFDerivAt F A p →
    (∃ z : ℂ, Module.End.HasEigenvalue
      (complexify (LinearMap.toMatrix basis basis A.toLinearMap)).toLin' z ∧ 1 < ‖z‖) →
    LocallyUnstable F V p

end Specs.D13Unified.Ch15.LinearizedInstability
