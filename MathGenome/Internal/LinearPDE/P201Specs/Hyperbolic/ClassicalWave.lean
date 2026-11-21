import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.EvenWave
import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SmoothCone
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Independent statements for the assembly, forcing, classical uniqueness and
sphere-jet assertion in `thm:pde-classical-wave`, paper.tex:3749–3846.
The velocity formulas use the existing probability means and their Euclidean
normalization. No support, boundedness, or global energy hypothesis is imposed.
The constructed smooth functions are defined for all real times. The comparison
class is only C² on the nonnegative time half-space, including one-sided time
derivatives at zero. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace P201Specs.ClassicalWave

abbrev VelocityType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → ℝ → (Space n → 𝕜) → ℝ → Space n → 𝕜

/-- The three velocity formulas, using the canonical line coordinate when n=1. -/
def velocity : VelocityType := fun {n} {𝕜} _ c h t =>
  match n with
  | 0 => fun _ => 0
  | 1 => fun x => OddWave.velocityOne c
      (fun y => h (P102.Trace.Ordinary.lineIsometry y)) t (x 0)
  | k + 2 => if Odd (k + 2) then OddWave.velocityOdd c h t
      else EvenWave.velocityEven c h t

abbrev HomogeneousType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → ℝ →
    (Space n → 𝕜) → (Space n → 𝕜) → ℝ → Space n → 𝕜

def homogeneous : HomogeneousType := fun c g h t x =>
  deriv (fun s => velocity c g s x) t + velocity c h t x

abbrev DuhamelType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → ℝ →
    (ℝ → Space n → 𝕜) → ℝ → Space n → 𝕜

def duhamel : DuhamelType := fun c f t x =>
  ∫ s in (0 : ℝ)..t, velocity c (f s) (t - s) x

abbrev ForcedType :=
  {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → ℝ →
    (Space n → 𝕜) → (Space n → 𝕜) →
    (ℝ → Space n → 𝕜) → ℝ → Space n → 𝕜

def forced : ForcedType := fun c g h f t x => homogeneous c g h t x + duhamel c f t x

/-- C² displacement and C¹ velocity on the time half-space. All endpoint
identities are within that half-space; values at negative times are unrestricted. -/
structure IsClassicalWave {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (u v f : ℝ → Space n → 𝕜) : Prop where
  displacement_regular : ContDiffOn ℝ 2 (Function.uncurry u) (Ici 0 ×ˢ univ)
  velocity_regular : ContDiffOn ℝ 1 (Function.uncurry v) (Ici 0 ×ˢ univ)
  forcing_continuous : ContinuousOn (Function.uncurry f) (Ici 0 ×ˢ univ)
  displacement_derivative : ∀ t ∈ Ici 0, ∀ x,
    HasDerivWithinAt (fun s => u s x) (v t x) (Ici 0) t
  wave_equation : ∀ t ∈ Ici 0, ∀ x,
    HasDerivWithinAt (fun s => v s x)
      (c ^ 2 • laplacian (u t) x + f t x) (Ici 0) t

/-- Joint smoothness, wave equation and the three zero-time velocity jets. -/
def VelocityRegularityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (h : Space n → 𝕜), ContDiff ℝ (⊤ : ℕ∞) h →
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (velocity c h)) ∧
    (∀ t x, deriv (deriv (fun s => velocity c h s x)) t =
      c ^ 2 • laplacian (velocity c h t) x) ∧
    (∀ x, velocity c h 0 x = 0 ∧ deriv (fun t => velocity c h t x) 0 = h x ∧
      deriv (deriv (fun t => velocity c h t x)) 0 = 0)

/-- The exact formulas (the upstream even mean retains its normalized lifted
sphere interpretation). Values at t=0 are covered by velocity regularity. -/
def VelocityFormulasStatement : Prop :=
  (∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ) (h : Space 1 → 𝕜) (t : ℝ) (x : Space 1),
    velocity c h t x = (2 * c)⁻¹ •
      ∫ y in (x 0 - c * t)..(x 0 + c * t), h (P102.Trace.Ordinary.lineIsometry y)) ∧
  (∀ {n : ℕ}, 3 ≤ n → Odd n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (h : Space n → 𝕜) (t : ℝ) (x : Space n), t ≠ 0 →
    velocity c h t x = (c * (Nat.doubleFactorial (n - 2) : ℝ))⁻¹ •
      OddWave.radialIterate ((n - 3) / 2)
        (fun r => r ^ (n - 2) • OddWave.sphericalMean h x r) (c * t)) ∧
  (∀ {n : ℕ}, 2 ≤ n → Even n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ), 0 < c → ∀ (h : Space n → 𝕜) (t : ℝ) (x : Space n), t ≠ 0 →
    velocity c h t x = (c * (Nat.doubleFactorial (n - 1) : ℝ))⁻¹ •
      OddWave.radialIterate ((n - 2) / 2)
        (fun r => r ^ (n - 1) • EvenWave.liftedMean h x r) (c * t))

/-- No global energy condition is part of this smooth Cauchy conclusion. -/
def SmoothCauchyResult {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (g h : Space n → 𝕜) (f u : ℝ → Space n → 𝕜) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u) ∧
  (∀ t x, deriv (deriv (fun s => u s x)) t = c ^ 2 • laplacian (u t) x + f t x) ∧
  (∀ x, u 0 x = g x ∧ deriv (fun t => u t x) 0 = h x) ∧
  IsClassicalWave c u (fun t x => deriv (fun s => u s x) t) f

def HomogeneousStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (g h : Space n → 𝕜), ContDiff ℝ (⊤ : ℕ∞) g →
    ContDiff ℝ (⊤ : ℕ∞) h → SmoothCauchyResult c g h (fun _ _ => 0) (homogeneous c g h)

def ForcedStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (g h : Space n → 𝕜) (f : ℝ → Space n → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) h →
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f) →
    SmoothCauchyResult c g h f (forced c g h f)

/-- Uniqueness in the entire classical comparison class, including endpoint
one-sided regularity, with no growth or integrability assumption at infinity. -/
def UniquenessStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (u₁ v₁ u₂ v₂ f : ℝ → Space n → 𝕜),
    IsClassicalWave c u₁ v₁ f → IsClassicalWave c u₂ v₂ f →
    (∀ x, u₁ 0 x = u₂ 0 x) → (∀ x, v₁ 0 x = v₂ 0 x) →
    ∀ t : ℝ, 0 ≤ t → ∀ x, u₁ t x = u₂ t x

/-- Equality of spatial jets through order k on a physical sphere. Fréchet
jets include every mixed coordinate derivative of the indicated orders. -/
def SphereJetsEqual {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (k : ℕ)
    (a : Space n) (r : ℝ) (g₁ g₂ : Space n → 𝕜) : Prop :=
  ∀ j : ℕ, j ≤ k → ∀ y ∈ Metric.sphere a r,
    iteratedFDeriv ℝ j g₁ y = iteratedFDeriv ℝ j g₂ y

/-- Huygens depends on the sphere jets, with displacement order m+1 and
velocity order m in n=2m+3. This is stronger than dependence on a ball. -/
def HuygensStatement : Prop :=
  ∀ (m : ℕ) {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (g₁ h₁ g₂ h₂ : Space (2 * m + 3) → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) g₁ → ContDiff ℝ (⊤ : ℕ∞) h₁ →
    ContDiff ℝ (⊤ : ℕ∞) g₂ → ContDiff ℝ (⊤ : ℕ∞) h₂ →
    ∀ (t : ℝ) (x : Space (2 * m + 3)), 0 < t →
      SphereJetsEqual (m + 1) x (c * t) g₁ g₂ →
      SphereJetsEqual m x (c * t) h₁ h₂ →
      homogeneous c g₁ h₁ t x = homogeneous c g₂ h₂ t x

end P201Specs.ClassicalWave
