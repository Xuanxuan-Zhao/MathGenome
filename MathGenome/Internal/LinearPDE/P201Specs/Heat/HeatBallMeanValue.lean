import MathGenome.Internal.LinearPDE.P201Specs.Heat.GaussianKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Independent statements for the heat-ball definition and mean-value theorem,
`paper.tex`, definition at 2852–2862 and theorem/proof at 2864–2929.
The space coordinate comes first in space-time; measure is Lebesgue product measure.
No regularity at times later than the top is required in the second formulation.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace P201Specs.Heat

abbrev SpaceTime (n : ℕ) := Space n × ℝ

abbrev spaceTimeMeasure (n : ℕ) : Measure (SpaceTime n) :=
  (spatialMeasure n).prod (volume : Measure ℝ)

/-- The canonical Gaussian superlevel set, with strict backward time. -/
def heatBall (n : ℕ) (r : ℝ) (z₀ : SpaceTime n) : Set (SpaceTime n) :=
  {z | z.2 < z₀.2 ∧ r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2 - z.2) (z₀.1 - z.1)}

/-- The nonnegative density, without its heat-ball indicator. -/
def heatBallWeight (n : ℕ) (r : ℝ) (z₀ z : SpaceTime n) : ℝ :=
  (1 / (4 * r ^ n)) * (‖z₀.1 - z.1‖ ^ 2 / (z₀.2 - z.2) ^ 2)

/-- Classical C^{2,1} regularity and u_t = Δu on a set. Continuity of the
space-time fields is joint; no second time derivative or mixed derivative is imposed.
Derivatives at points of a closed set are actual ambient derivatives. -/
def IsClassicalCaloricOn {n : ℕ} (u : SpaceTime n → ℝ)
    (S : Set (SpaceTime n)) : Prop :=
  ContinuousOn u S ∧
  ContinuousOn (fun z => deriv (fun t => u (z.1, t)) z.2) S ∧
  ContinuousOn (fun z => fderiv ℝ (fun x => u (x, z.2)) z.1) S ∧
  ContinuousOn (fun z => fderiv ℝ (fun x => fderiv ℝ (fun y => u (y, z.2)) x) z.1) S ∧
  ∀ z ∈ S,
    DifferentiableAt ℝ (fun t => u (z.1, t)) z.2 ∧
    ContDiffAt ℝ 2 (fun x => u (x, z.2)) z.1 ∧
    deriv (fun t => u (z.1, t)) z.2 = laplacian (fun x => u (x, z.2)) z.1

/-- The exact displayed normalization in the source. -/
def HeatBallMeanValueIdentity {n : ℕ} (u : SpaceTime n → ℝ)
    (r : ℝ) (z₀ : SpaceTime n) : Prop :=
  u z₀ = (1 / (4 * r ^ n)) *
    ∫ z in heatBall n r z₀,
      u z * (‖z₀.1 - z.1‖ ^ 2 / (z₀.2 - z.2) ^ 2) ∂spaceTimeMeasure n

abbrev heatBallType := (n : ℕ) → ℝ → SpaceTime n → Set (SpaceTime n)
abbrev heatBallWeightType := (n : ℕ) → ℝ → SpaceTime n → SpaceTime n → ℝ
abbrev isClassicalCaloricOnType := {n : ℕ} → (SpaceTime n → ℝ) → Set (SpaceTime n) → Prop
abbrev heatBallMeanValueIdentityType := {n : ℕ} → (SpaceTime n → ℝ) → ℝ → SpaceTime n → Prop

def heatBallOpenStatement : Prop :=
  ∀ n : ℕ, ∀ r : ℝ, ∀ z₀ : SpaceTime n, IsOpen (heatBall n r z₀)

def heatBallTopInClosureStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r → ∀ z₀ : SpaceTime n,
    z₀ ∈ closure (heatBall n r z₀)

def heatBallWeightNonnegativeStatement : Prop :=
  ∀ n : ℕ, ∀ r : ℝ, 0 < r → ∀ z₀ z : SpaceTime n,
    0 ≤ heatBallWeight n r z₀ z

def heatBallWeightIntegrableStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r → ∀ z₀ : SpaceTime n,
    Integrable (heatBallWeight n r z₀) ((spaceTimeMeasure n).restrict (heatBall n r z₀))

def heatBallWeightMassStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r → ∀ z₀ : SpaceTime n,
    (∫ z in heatBall n r z₀, heatBallWeight n r z₀ z ∂spaceTimeMeasure n) = 1

/-- Bounded measurable functions, in particular the bounded classical functions of
the source, have absolutely convergent integrals. -/
def heatBallBoundedIntegralStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r → ∀ z₀ : SpaceTime n,
    ∀ u : SpaceTime n → ℝ,
    AEStronglyMeasurable u ((spaceTimeMeasure n).restrict (heatBall n r z₀)) →
    (∃ M : ℝ, ∀ z ∈ heatBall n r z₀, ‖u z‖ ≤ M) →
    Integrable (fun z => u z *
      (‖z₀.1 - z.1‖ ^ 2 / (z₀.2 - z.2) ^ 2))
      ((spaceTimeMeasure n).restrict (heatBall n r z₀))

def heatBallMeanValueNeighborhoodStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r → ∀ z₀ : SpaceTime n,
    ∀ u : SpaceTime n → ℝ,
    (∃ U : Set (SpaceTime n), IsOpen U ∧ closure (heatBall n r z₀) ⊆ U ∧
      IsClassicalCaloricOn u U) →
    HeatBallMeanValueIdentity u r z₀

/-- Classical at all closure points strictly below the top, and continuous up to
the top. In particular this permits the top time of a caloric cylinder. -/
def heatBallMeanValueOneSidedStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 < r → ∀ z₀ : SpaceTime n,
    ∀ u : SpaceTime n → ℝ,
    ContinuousOn u (closure (heatBall n r z₀)) →
    IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2} →
    HeatBallMeanValueIdentity u r z₀

end P201Specs.Heat
