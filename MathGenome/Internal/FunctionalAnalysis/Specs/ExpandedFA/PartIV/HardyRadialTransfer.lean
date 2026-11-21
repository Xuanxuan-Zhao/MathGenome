import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyCompactTransfer
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
Independent statements for `fa2:p4:hardy-tail-bumps`,
`fa2:p4:hardy-radial-transfer`, and the use of the same expansion at
`fa2:p4:hardy-fixed-maximal` (paper.tex:20407--20411).
The chapter assumes d ≥ 1. Both scalar fields and the actual pointwise
convolutions and extended-valued suprema are retained.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.HardyRadialTransferSpec
open ExpandedFA.Fourier HardyMaximalSpec HardyLowpassSpec HardyCompactTransferSpec

/-- Including m=0 makes the first term literally ψ₀. -/
def tailPiece {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ψ : ℕ → Euclidean d → 𝕜) (m : ℕ) : Euclidean d → 𝕜 :=
  (1 / 2 : ℝ) ^ m • dilate ((2 : ℝ) ^ m) (ψ m)

def tailSum {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ψ : ℕ → Euclidean d → 𝕜) (n : ℕ) : Euclidean d → 𝕜 :=
  ∑ m ∈ Finset.range n, tailPiece ψ m

/-- Uniform and L¹ convergence of the literal dyadic expansion, with one
support radius and one bound for every derivative of order at most N. -/
def IsTailExpansion {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (N : ℕ) (Φ : Euclidean d → 𝕜)
    (ψ : ℕ → Euclidean d → 𝕜) (a B : ℝ) : Prop :=
  0 < a ∧ 0 ≤ B ∧ (∀ m, IsUniformTest N a B (ψ m)) ∧
    (∀ m, Integrable (tailPiece ψ m)) ∧
    TendstoUniformly (tailSum ψ) Φ atTop ∧
    Tendsto (fun n => ∫ x, ‖Φ x - tailSum ψ n x‖) atTop (𝓝 0)

def TailBumps : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d → ∀ (N : ℕ)
    (Φ : Euclidean d → 𝕜), IsFixedKernel Φ →
      ∃ (ψ : ℕ → Euclidean d → 𝕜) (a B : ℝ), IsTailExpansion N Φ ψ a B

def DyadicTransfer : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ N : ℕ, AdmissibleOrder d N →
      ∀ Φ : Euclidean d → 𝕜, IsFixedKernel Φ →
        ∀ (η : Schwartz 𝕜 d) (R : ℝ), IsLowpass η R →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euclidean d → 𝕜, Integrable f →
            ∀ x, peetre η f x < ⊤ → ∀ (j : ℤ) (z : Euclidean d),
              ‖convolve (dilate ((2 : ℝ) ^ (-j)) Φ) f z‖ ≤
                C * (peetre η f x).toReal *
                  (1 + (2 : ℝ) ^ j * ‖x - z‖) ^ peetreExponent d

/-- All positive scales, including points where the grand supremum is infinite. -/
def RadialGrand : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ N : ℕ, AdmissibleOrder d N →
      ∀ Φ : Euclidean d → 𝕜, IsFixedKernel Φ →
        ∃ C : ℝ, 0 < C ∧ ∀ f : Euclidean d → 𝕜, Integrable f →
          ∀ x, radial Φ f x ≤ ENNReal.ofReal C * grand N f x

end ExpandedFA.PartIV.HardyRadialTransferSpec
