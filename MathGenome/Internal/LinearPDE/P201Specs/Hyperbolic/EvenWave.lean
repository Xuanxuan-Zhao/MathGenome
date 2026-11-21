import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.OddWave
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent specifications for the even-dimensional part of
`thm:pde-classical-wave`, paper.tex:3746–3783 and 3830–3840.
The scalar is real or complex, the data are globally smooth with no support
or growth restriction, and the velocity extension is defined on all real times.
The ball formulas use Euclidean Lebesgue measure and the common surface mass. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace P201Specs.EvenWave

abbrev ProjectionType := (n : ℕ) → Space (n + 1) →L[ℝ] Space n
/-- Discard the last coordinate. -/
def projection : ProjectionType := fun n =>
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun i : Fin n => y i.castSucc)
      map_add' := by intro x y; rfl
      map_smul' := by intro a y; rfl }

abbrev InclusionType := (n : ℕ) → Space n →L[ℝ] Space (n + 1)
/-- Append a zero last coordinate. -/
def inclusion : InclusionType := fun n =>
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Fin.snoc (fun i => x i) 0)
      map_add' := by
        intro x y
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      map_smul' := by
        intro a x
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }

abbrev LiftType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Space n → 𝕜) → Space (n + 1) → 𝕜
def lift : LiftType := fun {n} {_𝕜} _ h y => h (projection n y)

abbrev LiftedMeanType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Space n → 𝕜) → Space n → ℝ → 𝕜
def liftedMean : LiftedMeanType := fun {n} {_𝕜} _ h x r =>
  OddWave.sphericalMean (lift h) (inclusion n x) r

abbrev WeightedBallMeanType := LiftedMeanType
/-- The weight is integrable on the open unit ball; no boundary value of
its totalized inverse square root enters the integral. -/
def weightedBallMean : WeightedBallMeanType := fun {n} {_𝕜} _ h x r =>
  (2 / omega (n + 1)) •
    ∫ z in Metric.ball (0 : Space n) 1,
      (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • h (x + r • z)

abbrev VelocityEvenType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → ℝ → (Space n → 𝕜) → ℝ → Space n → 𝕜
/-- Descent from the odd-dimensional velocity propagator. -/
def velocityEven : VelocityEvenType := fun {n} {_𝕜} _ c h t x =>
  OddWave.velocityOdd c (lift h) t (inclusion n x)

abbrev VelocityTwoBallType :=
  {𝕜 : Type} → [RCLike 𝕜] → ℝ → (Space 2 → 𝕜) → ℝ → Space 2 → 𝕜
/-- The positive-time Poisson integral, with its continuous value at zero. -/
def velocityTwoBall : VelocityTwoBallType := fun c h t x =>
  if t = 0 then 0 else
    (2 * Real.pi * c)⁻¹ • ∫ y in Metric.ball x (c * t),
      (Real.sqrt (c ^ 2 * t ^ 2 - ‖y - x‖ ^ 2))⁻¹ • h y

/-- Agreement of the lifted probability mean and the explicitly weighted
ball integral, for all real radii including zero. -/
def LiftedMeanBallStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → Even n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (h : Space n → 𝕜), ContDiff ℝ (⊤ : ℕ∞) h →
    ∀ (x : Space n) (r : ℝ),
      IntegrableOn (fun z => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • h (x + r • z))
        (Metric.ball (0 : Space n) 1) ∧
      liftedMean h x r = weightedBallMean h x r

/-- A geometric integration lemma sufficient for the remaining mean identity.
This is a proof obligation, not a field or assumed certificate of the propagator. -/
def SphereProjectionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (f : Space n → 𝕜), Continuous f →
    IntegrableOn (fun z => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f z)
      (Metric.ball (0 : Space n) 1) ∧
    (∫ θ : Space (n + 1), f (projection n θ) ∂unitSurface (n + 1)) =
      (2 : ℝ) • ∫ z in Metric.ball (0 : Space n) 1,
        (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f z

/-- The radial formula away from zero and its specified zero-time value. -/
def VelocityEvenFormulaStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → Even n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ), 0 < c → ∀ (h : Space n → 𝕜) (t : ℝ) (x : Space n),
    (t ≠ 0 → velocityEven c h t x =
      (c * (Nat.doubleFactorial (n - 1) : ℝ))⁻¹ •
        OddWave.radialIterate ((n - 2) / 2)
          (fun r => r ^ (n - 1) • liftedMean h x r) (c * t)) ∧
    velocityEven c h 0 x = 0

/-- Smoothness through zero, the n-dimensional wave equation, and all
three initial identities. -/
def VelocityEvenStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → Even n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ), 0 < c → ∀ (h : Space n → 𝕜), ContDiff ℝ (⊤ : ℕ∞) h →
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space n => velocityEven c h p.1 p.2) ∧
    (∀ (t : ℝ) (x : Space n),
      deriv (deriv (fun s => velocityEven c h s x)) t =
        c ^ 2 • laplacian (velocityEven c h t) x) ∧
    (∀ x : Space n, velocityEven c h 0 x = 0 ∧
      deriv (fun t => velocityEven c h t x) 0 = h x ∧
      deriv (deriv (fun t => velocityEven c h t x)) 0 = 0)

/-- The constants needed to identify the two-dimensional Poisson formula
under the shared Euclidean normalization. -/
def SurfaceBallConstantsStatement : Prop :=
  omega 3 = 4 * Real.pi ∧
    (volume : Measure (Space 2)).real (Metric.ball 0 1) = Real.pi ∧
    (volume : Measure (Space 3)).real (Metric.ball 0 1) = 4 * Real.pi / 3

/-- Positive-time Poisson formula and the continuous zero-time value. -/
def VelocityTwoBallStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (h : Space 2 → 𝕜), ContDiff ℝ (⊤ : ℕ∞) h →
    (∀ (t : ℝ) (x : Space 2), 0 < t →
      velocityEven c h t x = velocityTwoBall c h t x) ∧
    (∀ x : Space 2, velocityTwoBall c h 0 x = 0 ∧
      ContinuousWithinAt (fun t => velocityTwoBall c h t x) (Ici 0) 0)

/-- Assembly interfaces deriving the explicit mean and Poisson formulas. -/
def LiftedMeanBallFromProjectionStatement : Prop :=
  SphereProjectionStatement → LiftedMeanBallStatement

def VelocityTwoBallFromMeanStatement : Prop :=
  LiftedMeanBallStatement → VelocityTwoBallStatement

end P201Specs.EvenWave
