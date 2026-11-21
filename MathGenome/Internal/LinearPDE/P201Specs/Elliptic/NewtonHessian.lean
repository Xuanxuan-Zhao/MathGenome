import MathGenome.Internal.LinearPDE.P201Specs.Potential.NewtonPotential
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.HolderCancellation

/-! Independent statements for paper.tex:1728–1779.
All integrals and derivatives use the shared Euclidean spatial interfaces.
In particular the kernel in the potential is the fixed fundamental solution
of `-Δ`, including its logarithmic two-dimensional case.
-/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

namespace P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation

/-- Kronecker symbol, regarded as a real scalar. -/
def kronecker {n : ℕ} (i j : Fin n) : ℝ := if i = j then 1 else 0

/-- Ordinary Hessian kernel away from zero; totalized division fixes its value at zero. -/
def hessianKernel {n : ℕ} (i j : Fin n) (x : Space n) : ℝ :=
  ((n : ℝ) * x i * x j / ‖x‖ ^ (n + 2) - kronecker i j / ‖x‖ ^ n) / omega n

/-- Locally integrable first derivative kernel. -/
def gradientKernel {n : ℕ} (i : Fin n) (x : Space n) : ℝ :=
  -x i / (omega n * ‖x‖ ^ n)

/-- The ordinary Newton integral for arbitrary scalar data. No convergence or
regularity is assumed in this definition. -/
def holderPotential {n : ℕ} (F : Space n → ℝ) (x : Space n) : ℝ :=
  ∫ y, fundamentalKernel n y * F (x - y)

/-- Punctured pairing, rather than a postulated distribution. -/
def truncatedPairing {n : ℕ} (i j : Fin n) (ε : ℝ)
    (φ : Test ℝ (⊤ : Domain n)) : ℝ :=
  ∫ x in {x : Space n | ε < ‖x‖}, hessianKernel i j x * φ x

/-- The principal-value operator already fixed by the cancellation lemma. -/
def hessianOperator {n : ℕ} (i j : Fin n) (F : Space n → ℝ) : Space n → ℝ :=
  principalValue (hessianKernel i j) F

/-- Ordinary bounded Hölder condition on a prescribed set. -/
def IsHolderOn {n : ℕ} (α : ℝ) (g : Space n → ℝ) (s : Set (Space n)) : Prop :=
  ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ s, ‖g x‖ ≤ M) ∧
    ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ H * dist x y ^ α

/-- Supremum and Hölder seminorm on a set, with empty suprema totalized in ℝ. -/
def holderNormOn {n : ℕ} (α : ℝ) (g : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, r = ‖g x‖} +
  sSup {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ r = ‖g x - g y‖ / dist x y ^ α}

/-- Ordinary `C^{2,α}` norm: suprema of orders zero and one, and the supremum
plus Hölder seminorm for each second coordinate derivative. -/
def c2HolderNormOn {n : ℕ} (α : ℝ) (u : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, r = ‖u x‖} +
  (∑ i : Fin n, sSup {r : ℝ | ∃ x ∈ s, r = ‖multiPartial u {i} x‖}) +
  ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (multiPartial u {i, j}) s

/-- Local Hölder condition for the actual second classical derivatives. -/
def IsC2HolderLoc {n : ℕ} (α : ℝ) (u : Space n → ℝ) : Prop :=
  ContDiff ℝ 2 u ∧ ∀ s : Set (Space n), Bornology.IsBounded s →
    ∀ i j : Fin n, IsHolderOn α (multiPartial u {i, j}) s

def hessianKernelType := {n : ℕ} → Fin n → Fin n → Space n → ℝ
def holderPotentialType := {n : ℕ} → (Space n → ℝ) → Space n → ℝ

def kernelHypothesesStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ i j : Fin n, KernelHypotheses (hessianKernel i j)

/-- A first step of the potential argument, valid in every positive dimension. -/
def potentialBasicStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → ∀ F : Space n → ℝ,
    HasCompactSupport F → IsHolder α F →
      (∀ x, Integrable (fun y => fundamentalKernel n y * F (x - y)) volume) ∧
      Continuous (holderPotential F)

/-- Full existence and compensation formula for the explicit Hessian operator. -/
def hessianOperatorStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ F : Space n → ℝ,
    HasCompactSupport F → IsHolder α F → ∀ i j : Fin n,
      IsHolder α (hessianOperator i j F) ∧ ∀ x : Space n,
        (∀ ε : ℝ, 0 < ε → IntegrableOn
          (fun y => hessianKernel i j (x - y) * F y) {y | ε < ‖x - y‖} volume) ∧
        Integrable (compensatedIntegrand (hessianKernel i j) F x) volume ∧
        Tendsto (fun ε => truncated (hessianKernel i j) F ε x)
          (𝓝[>] 0) (𝓝 (hessianOperator i j F x)) ∧
        hessianOperator i j F x = ∫ z, compensatedIntegrand (hessianKernel i j) F x z

def hessianOperatorEstimateStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ i j : Fin n,
    ∀ (a : Space n) (R : ℝ), 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
      HasCompactSupport F → tsupport F ⊆ closedBall a R → IsHolder α F →
      IsHolder α (hessianOperator i j F) ∧
      holderNorm α (hessianOperator i j F) ≤ C * holderNorm α F

def sphereMomentStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ i j : Fin n,
    (∫ θ, θ i * θ j ∂unitSurface n) = omega n * kronecker i j / (n : ℝ)

/-- Existence as a continuous linear distribution, its actual punctured-integral
limit on every test, and the sign and normalization of the contact term. -/
def distributionIdentityStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ i j : Fin n,
    ∃ T : Distribution ℝ (⊤ : Domain n),
      (∀ φ : Test ℝ (⊤ : Domain n),
        (∀ ε : ℝ, 0 < ε → IntegrableOn
          (fun x => hessianKernel i j x * φ x) {x | ε < ‖x‖} volume) ∧
        Tendsto (fun ε => truncatedPairing i j ε φ) (𝓝[>] 0) (𝓝 (T φ))) ∧
      distributionDerivative {i, j}
        (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) =
        T - (kronecker i j / (n : ℝ)) • originDirac n

/-- Pointwise and distributional identification of the Hessian on Hölder data.
The convergence of the actual punctured convolutions is included explicitly. -/
def potentialHessianStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ F : Space n → ℝ, HasCompactSupport F → IsHolder α F →
      (∀ x, Integrable (fun y => fundamentalKernel n y * F (x - y)) volume) ∧
      IsC2HolderLoc α (holderPotential F) ∧
      ∀ i j : Fin n,
        let H := fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)
        (∀ x, Tendsto (fun ε => truncated (hessianKernel i j) F ε x)
          (𝓝[>] 0) (𝓝 (hessianOperator i j F x))) ∧
        multiPartial (holderPotential F) {i, j} = H ∧
        distributionDerivative {i, j}
          (regularDistribution (⊤ : Domain n) (holderPotential F)) =
          regularDistribution (⊤ : Domain n) H

/-- The constant is chosen before F. Both observation set and prescribed support
ball can enter the constant, as can n and α. This includes n=1 and n=2. -/
def potentialEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ s : Set (Space n), Bornology.IsBounded s → ∀ (a : Space n) (R : ℝ), 0 < R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
        HasCompactSupport F → tsupport F ⊆ closedBall a R → IsHolder α F →
        IsC2HolderLoc α (holderPotential F) ∧
        c2HolderNormOn α (holderPotential F) s ≤ C * holderNorm α F

def dimensionOneIdentityStatement : Prop :=
  distributionDerivative ({0, 0} : MultiIndex 1)
    (regularDistribution (⊤ : Domain 1) (fundamentalKernel 1)) = -originDirac 1

def dimensionOnePotentialStatement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ F : Space 1 → ℝ,
    HasCompactSupport F → IsHolder α F →
      (∀ x, Integrable (fun y => fundamentalKernel 1 y * F (x - y)) volume) ∧
      IsC2HolderLoc α (holderPotential F) ∧
      multiPartial (holderPotential F) ({0, 0} : MultiIndex 1) = -F ∧
      distributionDerivative ({0, 0} : MultiIndex 1)
        (regularDistribution (⊤ : Domain 1) (holderPotential F)) =
        -(regularDistribution (⊤ : Domain 1) F)

/-- The corresponding local potential estimate in dimension one. -/
def dimensionOnePotentialEstimateStatement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    ∀ s : Set (Space 1), Bornology.IsBounded s → ∀ (a : Space 1) (R : ℝ), 0 < R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space 1 → ℝ,
        HasCompactSupport F → tsupport F ⊆ closedBall a R → IsHolder α F →
        IsC2HolderLoc α (holderPotential F) ∧
        c2HolderNormOn α (holderPotential F) s ≤ C * holderNorm α F

end P201Specs.Elliptic.NewtonHessian
