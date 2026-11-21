import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Independent statements for the odd-dimensional velocity propagators in
paper.tex:3739–3828. Smoothness is local on compact sets; no support, energy,
or boundedness premise is present. Time runs over ℝ, including zero. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace P201Specs.OddWave

abbrev SphericalMeanType := MeanValues.UnitSphereMeanType
abbrev sphericalMean : SphericalMeanType := @MeanValues.unitSphereMean

abbrev SphereProbabilityType := (n : ℕ) → Measure (Space n)
/-- Unit-sphere probability measure in every positive dimension. -/
def sphereProbability : SphereProbabilityType := fun n =>
  ENNReal.ofReal ((omega n)⁻¹) • unitSurface n

def SphereProbabilityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → sphereProbability n univ = 1

def SphericalMeanProbabilityStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (h : Space n → 𝕜) (x : Space n) (r : ℝ),
    sphericalMean h x r = ∫ θ, h (x + r • θ) ∂sphereProbability n

abbrev RadialDerivativeType := {𝕜 : Type} → [RCLike 𝕜] → (ℝ → 𝕜) → ℝ → 𝕜
/-- The source's D_r away from zero. Its totalized value at zero is not
used to assert any removable-singularity result. -/
def radialDerivative : RadialDerivativeType := fun f r => r⁻¹ • deriv f r

abbrev RadialIterateType :=
  {𝕜 : Type} → [RCLike 𝕜] → ℕ → (ℝ → 𝕜) → ℝ → 𝕜
def radialIterate : RadialIterateType := fun m f => (radialDerivative^[m]) f

abbrev VelocityOneType :=
  {𝕜 : Type} → [RCLike 𝕜] → ℝ → (ℝ → 𝕜) → ℝ → ℝ → 𝕜
/-- The oriented interval integral also defines negative times. -/
def velocityOne : VelocityOneType := fun c h t x =>
  (2 * c)⁻¹ • ∫ y in (x - c * t)..(x + c * t), h y

abbrev VelocityOddType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → ℝ → (Space n → 𝕜) → ℝ → Space n → 𝕜
/-- The positive-time formula with its prescribed value zero at time zero.
Smoothness across that point is a theorem, not an input certificate. -/
def velocityOdd : VelocityOddType := fun {n} {_𝕜} _ c h t x =>
  if t = 0 then 0 else
    (c * (Nat.doubleFactorial (n - 2) : ℝ))⁻¹ •
      radialIterate ((n - 3) / 2)
        (fun r => r ^ (n - 2) • sphericalMean h x r) (c * t)

abbrev RegularRadialType :=
  {𝕜 : Type} → [RCLike 𝕜] → ℕ → (ℝ → 𝕜) → ℝ → 𝕜
/-- A construction without division for the extension of
D_r^m (r^(2m+1) F). Agreement away from zero is a proof obligation. -/
def regularRadial : RegularRadialType := fun {_𝕜} _ m =>
  match m with
  | 0 => fun F r => r • F r
  | m + 1 => fun F => regularRadial m
      (fun r => ((2 * m + 3 : ℕ) : ℝ) • F r + r • deriv F r)

/-- A precise removable-singularity statement, including all initial jets. -/
def RegularRadialStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (F : ℝ → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) F → Function.Even F →
    ContDiff ℝ (⊤ : ℕ∞) (regularRadial m F) ∧
    Function.Odd (regularRadial m F) ∧
    (∀ r : ℝ, r ≠ 0 → regularRadial m F r =
      radialIterate m (fun s => s ^ (2 * m + 1) • F s) r) ∧
    regularRadial m F 0 = 0 ∧
    deriv (regularRadial m F) 0 = (Nat.doubleFactorial (2 * m + 1) : ℝ) • F 0 ∧
    deriv (deriv (regularRadial m F)) 0 = 0

/-- Full one-dimensional conclusion in the manuscript's real coordinate. -/
def VelocityOneStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (h : ℝ → 𝕜), ContDiff ℝ (⊤ : ℕ∞) h →
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => velocityOne c h p.1 p.2) ∧
    (∀ t x : ℝ,
      deriv (fun s => deriv (fun q => velocityOne c h q x) s) t =
        c ^ 2 • deriv (fun y => deriv (fun z => velocityOne c h t z) y) x) ∧
    (∀ x : ℝ, velocityOne c h 0 x = 0 ∧
      deriv (fun t => velocityOne c h t x) 0 = h x ∧
      deriv (fun s => deriv (fun t => velocityOne c h t x) s) 0 = 0)

/-- The fixed-unit-sphere integral is jointly smooth, even, and normalized at zero. -/
def SphericalMeanRegularityStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜] (h : Space n → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) h →
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => sphericalMean h p.1 p.2) ∧
    (∀ x r, sphericalMean h x (-r) = sphericalMean h x r) ∧
    (∀ x, sphericalMean h x 0 = h x)

/-- Darboux's equation for the actual spherical integral. -/
def DarbouxStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜] (h : Space n → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) h → ∀ (x : Space n) (r : ℝ), 0 < r →
    laplacian (fun y => sphericalMean h y r) x =
      deriv (deriv (sphericalMean h x)) r +
        (((n - 1 : ℕ) : ℝ) / r) • deriv (sphericalMean h x) r

/-- Full wave equation and the three initial identities, including smoothness
of the zero-time extension of the explicit odd-dimensional formula. -/
def VelocityOddStatement : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → Odd n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ), 0 < c → ∀ (h : Space n → 𝕜), ContDiff ℝ (⊤ : ℕ∞) h →
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space n => velocityOdd c h p.1 p.2) ∧
    (∀ (t : ℝ) (x : Space n),
      deriv (deriv (fun s => velocityOdd c h s x)) t =
        c ^ 2 • laplacian (velocityOdd c h t) x) ∧
    (∀ x : Space n, velocityOdd c h 0 x = 0 ∧
      deriv (fun t => velocityOdd c h t x) 0 = h x ∧
      deriv (deriv (fun t => velocityOdd c h t x)) 0 = 0)

/-- The special case displayed separately in the source. -/
def VelocityThreeStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (h : Space 3 → 𝕜) (t : ℝ) (x : Space 3),
      velocityOdd c h t x = t • sphericalMean h x (c * t)

end P201Specs.OddWave
