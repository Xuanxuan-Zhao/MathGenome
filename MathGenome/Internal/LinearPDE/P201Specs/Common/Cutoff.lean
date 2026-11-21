import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionOperations
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionSupport

/-! Independent statements of the distributional cutoff proposition (paper.tex,
`prop:pde-cutoff`). Coefficients need only be smooth on the open domain.
The support hypothesis below is intrinsic to the domain, so no condition is
imposed on the values of an ambient representative outside the domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace P201Specs

abbrev SmoothCoefficient {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) :=
  P102.U4.SmoothCoefficient 𝕜 Ω

/-- Multiplication is transposed pointwise multiplication on compact smooth tests. -/
abbrev distributionMultiply {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (χ : SmoothCoefficient 𝕜 Ω) (u : Distribution 𝕜 Ω) : Distribution 𝕜 Ω :=
  P102.U4.distributionMultiplier χ u

/-- The smooth coefficient whose value is the shared classical Laplacian. -/
def cutoffLaplacianCoefficient {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (χ : SmoothCoefficient 𝕜 Ω) : SmoothCoefficient 𝕜 Ω :=
  ⟨laplacian χ.val, by
    have heq : laplacian χ.val = fun x => ∑ i : Fin n,
        (P102.U4.coefficientPartial i (P102.U4.coefficientPartial i χ)).val x := by
      funext x
      apply Finset.sum_congr rfl
      intro i _
      change P102.U4.partialWord χ.val ((i ::ₘ {i}).sort (· ≤ ·)) x = _
      rw [Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]
      rfl
    rw [heq]
    exact ContDiffOn.sum fun i _ =>
      (P102.U4.coefficientPartial i (P102.U4.coefficientPartial i χ)).property⟩

/-- The dot product is bilinear, as are the manuscript's distribution pairings. -/
def cutoffGradientPairing {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (χ : SmoothCoefficient 𝕜 Ω) (u : Distribution 𝕜 Ω) : Distribution 𝕜 Ω :=
  ∑ i : Fin n, distributionMultiply (P102.U4.coefficientPartial i χ)
    (distributionDerivative {i} u)

def cutoffFirstDerivativeStatement : Prop :=
  ∀ (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n)
    (χ : SmoothCoefficient 𝕜 Ω) (u : Distribution 𝕜 Ω) (j : Fin n),
    distributionDerivative {j} (distributionMultiply χ u) =
      distributionMultiply χ (distributionDerivative {j} u) +
      distributionMultiply (P102.U4.coefficientPartial j χ) u

def cutoffLaplacianStatement : Prop :=
  ∀ (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n)
    (χ : SmoothCoefficient 𝕜 Ω) (u : Distribution 𝕜 Ω),
    distributionLaplacian (distributionMultiply χ u) =
      distributionMultiply χ (distributionLaplacian u) +
      (2 : 𝕜) • cutoffGradientPairing χ u +
      distributionMultiply (cutoffLaplacianCoefficient χ) u

/-- Compact support is measured on Ω itself. The conclusion gives compactness
of the actual relative distribution support, not merely a testwise vanishing claim. -/
def cutoffCompactSupportStatement : Prop :=
  ∀ (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n)
    (χ : SmoothCoefficient 𝕜 Ω) (u : Distribution 𝕜 Ω),
    HasCompactSupport (fun x : Ω => χ.val x) →
      IsCompact (P102.U4.relativeSupport (distributionMultiply χ u)) ∧
      P102.U4.relativeSupport (distributionMultiply χ u) ⊆ (Ω : Set (Space n))

end P201Specs
