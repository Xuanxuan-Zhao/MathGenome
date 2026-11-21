import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Local classical wave data on a closed, truncated backward cone.
The velocity is an explicit first time derivative. All time derivatives are within
[0,T], so the hypotheses put no condition on values at negative times or after T.
There is no global Sobolev or integrability hypothesis. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff
namespace P201Specs.SmoothCone

variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Spatial gradient, with the Euclidean norm also for complex-valued solutions. -/
def spatialGradient (w : Space n → 𝕜) (x : Space n) : EuclideanSpace 𝕜 (Fin n) :=
  WithLp.toLp 2 (fun i => fderiv ℝ w x (coordinate n i))

/-- The time slice of the backward cone. -/
def coneBall (c : ℝ) (a : Space n) (R s : ℝ) : Set (Space n) :=
  ball a (R - c * s)

/-- Includes the lateral boundary and both time endpoints. -/
def closedCone (c : ℝ) (a : Space n) (R T : ℝ) : Set (ℝ × Space n) :=
  {z | z.1 ∈ Icc 0 T ∧ z.2 ∈ closedBall a (R - c * z.1)}

/-- The ambient relative time slab for one-sided endpoint regularity. -/
def timeSlab (T : ℝ) : Set (ℝ × Space n) := Icc 0 T ×ˢ univ

/-- A local C² wave and its C¹ velocity. The derivative equalities are the PDE
and the identification v = u_t, rather than an energy certificate. Spatial
regularity at the lateral boundary is included by using the ambient time slab. -/
structure IsLocalSmoothWave (c : ℝ) (a : Space n) (R T : ℝ)
    (u v f : ℝ → Space n → 𝕜) : Prop where
  displacement_regular : ∀ z ∈ closedCone c a R T,
    ContDiffWithinAt ℝ 2 (Function.uncurry u) (timeSlab T) z
  velocity_regular : ∀ z ∈ closedCone c a R T,
    ContDiffWithinAt ℝ 1 (Function.uncurry v) (timeSlab T) z
  forcing_continuous : ContinuousOn (Function.uncurry f) (closedCone c a R T)
  displacement_derivative : ∀ s ∈ Icc 0 T, ∀ x ∈ closedBall a (R - c * s),
    HasDerivWithinAt (fun r => u r x) (v s x) (Icc 0 T) s
  wave_equation : ∀ s ∈ Icc 0 T, ∀ x ∈ closedBall a (R - c * s),
    HasDerivWithinAt (fun r => v r x)
      (c ^ 2 • laplacian (u s) x + f s x) (Icc 0 T) s

/-- Exactly one half the integral of kinetic plus spatial-gradient energy. -/
def localEnergy (c : ℝ) (a : Space n) (R : ℝ)
    (u v : ℝ → Space n → 𝕜) (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in coneBall c a R s,
    (‖v s x‖ ^ 2 + c ^ 2 * ‖spatialGradient (u s) x‖ ^ 2)

/-- The local L² forcing norm, written by its square-integral formula.
Local continuity on the compact cone makes these finite local integrals. -/
def localForcingNorm (c : ℝ) (a : Space n) (R : ℝ)
    (f : ℝ → Space n → 𝕜) (s : ℝ) : ℝ :=
  Real.sqrt (∫ x in coneBall c a R s, ‖f s x‖ ^ 2)

/-- Quantitative local energy estimate at every time of the truncated cone,
including time zero. The explicit velocity is linked to u by IsLocalSmoothWave. -/
def localEnergyEstimateStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
    ∀ (c : ℝ) (a : Space n) (R T : ℝ) (u v f : ℝ → Space n → 𝕜),
      0 < c → 0 < R → 0 ≤ T → T < R / c →
      IsLocalSmoothWave c a R T u v f → ∀ t ∈ Icc 0 T,
      Real.sqrt (2 * localEnergy c a R u v t) ≤
        Real.sqrt (2 * localEnergy c a R u v 0) +
          ∫ s in (0 : ℝ)..t, localForcingNorm c a R f s

/-- Pointwise domain of dependence for zero displacement AND zero velocity. -/
def vanishingStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
    ∀ (c : ℝ) (a : Space n) (R T : ℝ) (u v f : ℝ → Space n → 𝕜),
      0 < c → 0 < R → 0 ≤ T → T < R / c →
      IsLocalSmoothWave c a R T u v f →
      (∀ x ∈ coneBall c a R 0, u 0 x = 0) →
      (∀ x ∈ coneBall c a R 0, v 0 x = 0) →
      (∀ s ∈ Icc 0 T, ∀ x ∈ coneBall c a R s, f s x = 0) →
      ∀ t ∈ Icc 0 T, ∀ x ∈ coneBall c a R t, u t x = 0

/-- The same domain of dependence for two classical solutions with matching
initial displacement, initial velocity and source in the backward cone. -/
def localUniquenessStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
    ∀ (c : ℝ) (a : Space n) (R T : ℝ)
      (u₁ v₁ f₁ u₂ v₂ f₂ : ℝ → Space n → 𝕜),
      0 < c → 0 < R → 0 ≤ T → T < R / c →
      IsLocalSmoothWave c a R T u₁ v₁ f₁ →
      IsLocalSmoothWave c a R T u₂ v₂ f₂ →
      (∀ x ∈ coneBall c a R 0, u₁ 0 x = u₂ 0 x) →
      (∀ x ∈ coneBall c a R 0, v₁ 0 x = v₂ 0 x) →
      (∀ s ∈ Icc 0 T, ∀ x ∈ coneBall c a R s, f₁ s x = f₂ s x) →
      ∀ t ∈ Icc 0 T, ∀ x ∈ coneBall c a R t, u₁ t x = u₂ t x

end P201Specs.SmoothCone
