import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Independent statements for paper.tex, Cancellation on Hölder data.
The principal value is the right-hand limit of the actual punctured Lebesgue
integrals. None of the definitions below supplies a convergence certificate.
-/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

namespace P201Specs.Elliptic.HolderCancellation

variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Source kernel assumptions. The value at zero is unrestricted. -/
structure KernelHypotheses (K : Space m → 𝕜) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ : Set (Space m))
  homogeneous : ∀ (r : ℝ), 0 < r → ∀ z : Space m, z ≠ 0 →
    K (r • z) = ((r ^ m)⁻¹ : ℝ) • K z
  mean_zero : (∫ z, K z ∂unitSurface m) = 0

/-- The two sphere bounds on which the quantitative constant may depend. -/
def SphereBounds (K : Space m → 𝕜) (A B : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧ ∀ z : Space m, ‖z‖ = 1 →
    ‖K z‖ ≤ A ∧ ‖fderiv ℝ K z‖ ≤ B

/-- Separate supremum and seminorm bounds, using ordinary Euclidean distance. -/
def HolderBounds (α : ℝ) (g : Space m → 𝕜) (M H : ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ H ∧ (∀ x, ‖g x‖ ≤ M) ∧
    ∀ x y, ‖g x - g y‖ ≤ H * dist x y ^ α

/-- The global bounded Hölder class; compact support is a separate hypothesis. -/
def IsHolder (α : ℝ) (g : Space m → 𝕜) : Prop :=
  ∃ M H : ℝ, HolderBounds α g M H

/-- Ordinary supremum norm plus ordinary Hölder seminorm. It is used only for
functions proved to have finite such bounds. -/
def holderNorm (α : ℝ) (g : Space m → 𝕜) : ℝ :=
  sSup (Set.range (fun x => ‖g x‖)) +
    sSup {q : ℝ | ∃ x y : Space m, x ≠ y ∧ q = ‖g x - g y‖ / dist x y ^ α}

def truncated (K g : Space m → 𝕜) (ε : ℝ) (x : Space m) : 𝕜 :=
  ∫ y in {y : Space m | ε < ‖x - y‖}, K (x - y) * g y

def principalValue (K g : Space m → 𝕜) (x : Space m) : 𝕜 :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => truncated K g ε x)

/-- Absolute-integral candidate obtained by subtracting only near zero. -/
def compensatedIntegrand (K g : Space m → 𝕜) (x z : Space m) : 𝕜 :=
  K z * (g (x - z) - (ball (0 : Space m) 1).indicator (fun _ => g x) z)

def annularCancellationStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ {𝕜 : Type} [RCLike 𝕜] (K : Space m → 𝕜),
    KernelHypotheses K → ∀ ε R : ℝ, 0 < ε →
      IntegrableOn K {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R} volume ∧
      (∫ z in {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R}, K z) = 0

def principalValueStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ),
    0 < α → α < 1 → ∀ (K g : Space m → 𝕜),
    KernelHypotheses K → HasCompactSupport g → IsHolder α g →
    ∀ x : Space m,
      (∀ ε : ℝ, 0 < ε →
        IntegrableOn (fun y => K (x - y) * g y) {y | ε < ‖x - y‖} volume) ∧
      Integrable (compensatedIntegrand K g x) volume ∧
      Tendsto (fun ε => truncated K g ε x) (𝓝[>] 0) (𝓝 (principalValue K g x)) ∧
      principalValue K g x = ∫ z, compensatedIntegrand K g x z

def globalHolderStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ),
    0 < α → α < 1 → ∀ (K g : Space m → 𝕜),
    KernelHypotheses K → HasCompactSupport g → IsHolder α g →
    IsHolder α (principalValue K g)

/-- The constant is chosen before K and g. The dimension is fixed, as in the
source's statement "in R^m". Centers and radii specify the prescribed ball. -/
def quantitativeHolderStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ),
    0 < α → α < 1 → ∀ (a : Space m) (R A B : ℝ), 0 < R → 0 ≤ A → 0 ≤ B →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K g : Space m → 𝕜),
      KernelHypotheses K → SphereBounds K A B → HasCompactSupport g →
      tsupport g ⊆ closedBall a R → IsHolder α g →
      IsHolder α (principalValue K g) ∧
      holderNorm α (principalValue K g) ≤ C * holderNorm α g

/-- Uniform seminorm control, with the constant independent of the input's
support and supremum bound. This proposition contains no bounded-operator data. -/
def principalValueSeminormStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ (α : ℝ), 0 < α → α < 1 →
    ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ {𝕜 : Type} [RCLike 𝕜] (K g : Space m → 𝕜) (M H : ℝ),
      KernelHypotheses K → SphereBounds K A B → HasCompactSupport g →
      HolderBounds α g M H → ∀ x y : Space m,
        ‖principalValue K g x - principalValue K g y‖ ≤ C * H * dist x y ^ α

end P201Specs.Elliptic.HolderCancellation
