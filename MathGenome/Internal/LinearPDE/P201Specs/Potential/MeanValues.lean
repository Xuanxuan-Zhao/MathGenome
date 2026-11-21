import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-! Independent statements for the mean-value part of paper.tex:644–683.
The distributional assertion of the same source theorem belongs to L02_weyl.
All derivatives are real derivatives, including for complex-valued functions.
The canonical Laplacian and measures are those of the spatial interface.
-/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace P201Specs.MeanValues

abbrev IsHarmonicType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → Domain n → (Space n → 𝕜) → Prop

/-- Harmonicity on an open set: C² and the coordinate Laplacian vanishes.
No connectedness, boundary regularity, or global integrability is imposed. -/
def IsHarmonic : IsHarmonicType := fun Ω u =>
  ContDiffOn ℝ 2 u Ω ∧ ∀ x ∈ Ω, laplacian u x = 0

abbrev HasBallMeanValueType := IsHarmonicType

/-- Only strictly positive radii whose entire closed ball lies in the open set. -/
def HasBallMeanValue : HasBallMeanValueType := fun Ω u =>
  ∀ (a : Space _) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    u a = ballAverage u a r

abbrev HasSphereMeanValueType := IsHarmonicType

def HasSphereMeanValue : HasSphereMeanValueType := fun Ω u =>
  ∀ (a : Space _) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    u a = sphereAverage u a r

abbrev UnitSphereMeanType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Space n → 𝕜) → Space n → ℝ → 𝕜

/-- The function M(s) used in the source proof; its definition includes s=0. -/
def unitSphereMean : UnitSphereMeanType := fun {n} {_𝕜} _ u a s =>
  (omega n)⁻¹ • ∫ θ, u (a + s • θ) ∂unitSurface n

/-- Both mean-value identities, in arbitrary dimension at least one. -/
def MeanValuesStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), IsHarmonic Ω u →
    ∀ (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
      u a = sphereAverage u a r ∧ u a = ballAverage u a r

/-- The ball converse includes smoothness, with no extra regularity premise. -/
def BallConverseStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContinuousOn u Ω →
    HasBallMeanValue Ω u → ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧ IsHarmonic Ω u

/-- The sphere converse is separate; neither identity is assumed from the other. -/
def SphereConverseStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContinuousOn u Ω →
    HasSphereMeanValue Ω u → ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧ IsHarmonic Ω u

/-- The spherical-mean derivative for C² functions, without harmonicity. -/
def SphericalMeanDerivativeStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContDiffOn ℝ 2 u Ω →
    ∀ (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
      HasDerivAt (unitSphereMean u a)
        ((omega n * r ^ (n - 1))⁻¹ • ∫ x in ball a r, laplacian u x) r

/-- Identification of M(s) with the shared normalized surface integral. -/
def SphereMeanNormalizationStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (u : Space n → 𝕜) (a : Space n) (r : ℝ), 0 < r →
    sphereAverage u a r = unitSphereMean u a r

/-- The unit surface has positive total mass in every required dimension. -/
def OmegaPositiveStatement : Prop := ∀ {n : ℕ}, 1 ≤ n → 0 < omega n

/-- In dimension one the shared surface average is the arithmetic endpoint mean. -/
def SphereMeanOneStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (u : Space 1 → 𝕜) (a : Space 1) (r : ℝ),
    0 < r → sphereAverage u a r =
      (2 : ℝ)⁻¹ • (u (a + r • coordinate 1 0) + u (a - r • coordinate 1 0))

/-- The source's limit at zero, requiring continuity only near the center. -/
def UnitSphereMeanLimitStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (a : Space n), ContinuousOn u Ω → a ∈ Ω →
      Tendsto (unitSphereMean u a) (𝓝 0) (𝓝 (u a))

/-- Bridge to the library Laplacian, proved from the actual second derivatives. -/
def LaplacianBridgeStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (u : Space n → 𝕜) (x : Space n),
    ContDiffAt ℝ 2 u x → laplacian u x = Laplacian.laplacian u x

/-- On an open domain the library's neighborhood harmonicity is equivalent. -/
def HarmonicBridgeStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜),
    IsHarmonic Ω u ↔ InnerProductSpace.HarmonicOnNhd u (Ω : Set _)

/-- Differentiation under the fixed unit-surface integral, before the flux step. -/
def AngularDerivativeStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜),
    ContDiffOn ℝ 1 u Ω → ∀ (a : Space n) (r : ℝ), 0 ≤ r →
    closedBall a r ⊆ (Ω : Set _) →
    HasDerivAt (unitSphereMean u a)
      ((omega n)⁻¹ • ∫ θ, fderiv ℝ u (a + r • θ) θ ∂unitSurface n) r

/-- The cone measure also equals endpoint counting in dimension one. -/
def UnitSurfaceConeBridgeStatement : Prop :=
  ∀ n : ℕ, unitSurface n = Measure.map
    (Subtype.val : sphere (0 : Space n) 1 → Space n) (volume : Measure (Space n)).toSphere

/-- Radial integration, expressed with the actual shared unit surface. -/
def IntegralBallPolarStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    {u : Space n → 𝕜} (a : Space n) (r : ℝ), IntegrableOn u (ball a r) →
      (∫ x in ball a r, u x) = ∫ s in Ioo (0 : ℝ) r, s ^ (n - 1) •
        ∫ θ, u (a + s • θ) ∂unitSurface n

/-- Continuous sphere mean values imply the ball identities. -/
def SphereImpliesBallStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContinuousOn u Ω →
      HasSphereMeanValue Ω u → HasBallMeanValue Ω u

/-- Continuous ball mean values imply the sphere identities. -/
def BallImpliesSphereStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContinuousOn u Ω →
      HasBallMeanValue Ω u → HasSphereMeanValue Ω u

/-- The radial FTC requires continuity, without a C¹ hypothesis. -/
def BallIntegralDerivativeStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContinuousOn u Ω →
    ∀ (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
      HasDerivAt (fun s : ℝ => ∫ x in ball a s, u x)
        (r ^ (n - 1) • ∫ θ, u (a + r • θ) ∂unitSurface n) r

/-- Continuous means are locally smooth before extracting the Laplacian. -/
def SphereMeanSmoothStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContinuousOn u Ω →
      HasSphereMeanValue Ω u → ContDiffOn ℝ (⊤ : ℕ∞) u Ω

def BallMeanSmoothStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), ContinuousOn u Ω →
      HasBallMeanValue Ω u → ContDiffOn ℝ (⊤ : ℕ∞) u Ω

/-- Shrinking ball averages of a continuous function recover its center value. -/
def BallAverageLimitStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (a : Space n), ContinuousOn u Ω → a ∈ Ω →
      Tendsto (ballAverage u a) (𝓝[>] 0) (𝓝 (u a))

/-- The actual coordinate Laplacian is continuous for a C² function. -/
def LaplacianContinuousStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜),
    ContDiffOn ℝ 2 u Ω → ContinuousOn (laplacian u) Ω

/-- Vanishing ball integrals characterize zero among continuous functions. -/
def VanishingBallIntegralsStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (f : Space n → 𝕜), ContinuousOn f Ω →
    (∀ (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
      (∫ x in ball a r, f x) = 0) → ∀ a ∈ Ω, f a = 0

end P201Specs.MeanValues
