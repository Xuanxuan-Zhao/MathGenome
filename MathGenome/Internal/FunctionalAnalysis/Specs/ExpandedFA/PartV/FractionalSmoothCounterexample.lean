import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeakVolterraResolvent
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Asymptotics.Defs

/-! The constant-datum example, with the positive-length restriction only on
failure of endpoint differentiability. The canonical series is evaluated on the
real line; all regularity claims away from zero concern positive time. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ExpandedFA.PartV.FractionalSmoothCounterexample.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraResolvent.Spec

def solution {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (ζ : 𝕜) (t : ℝ) : 𝕜 :=
  ∑' n : ℕ, mittagTerm α ζ n t

def SolutionIdentification : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → ∀ hT : 0 ≤ T, ∀ ζ : 𝕜,
    ∃ u : C(Icc (0 : ℝ) T, 𝕜),
      (∀ t, u t = solution α ζ t) ∧
      (∀ t, u t = 1 + ζ * fractionalValue α (continuousExtension hT u) t) ∧
      (∀ v : C(Icc (0 : ℝ) T, 𝕜),
        (∀ t, v t = 1 + ζ * fractionalValue α (continuousExtension hT v) t) → v = u) ∧
      u ⟨0, le_rfl, hT⟩ = 1

def Expansion : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ), 0 < α → ∀ ζ : 𝕜,
  Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
    (fun t => solution α ζ t - 1 - (t ^ α / Real.Gamma (1 + α)) • ζ)
    (fun t => t ^ (2 * α))

def PositiveSmoothness : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ), 0 < α → ∀ ζ : 𝕜,
  ContDiffOn ℝ ∞ (fun t => solution α ζ t - 1) (Ioi 0)

def DerivativeBounds : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ), 0 < α →
  ∀ (ζ : 𝕜) (j : ℕ), ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
    ∀ t : ℝ, 0 < t → t < δ →
      ‖iteratedDeriv j (fun s => solution α ζ s - 1) t‖ ≤ C * t ^ (α - (j : ℝ))

/-- This stronger statement rules out even a differentiable extension. -/
def NoDifferentiableExtension : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
  (α T : ℝ), 0 < α → α < 1 → 0 < T → ∀ ζ : 𝕜, ζ ≠ 0 →
  ¬ ∃ v : ℝ → 𝕜, DifferentiableAt ℝ v 0 ∧
    ∀ t ∈ Icc (0 : ℝ) T, v t = solution α ζ t

def NoC1Extension : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
  (α T : ℝ), 0 < α → α < 1 → 0 < T → ∀ ζ : 𝕜, ζ ≠ 0 →
  ¬ ∃ v : ℝ → 𝕜, ContDiffAt ℝ 1 v 0 ∧
    ∀ t ∈ Icc (0 : ℝ) T, v t = solution α ζ t

def ZeroInterval : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ), 0 < α → ∀ ζ : 𝕜,
  solution α ζ 0 = 1 ∧ ∃ v : ℝ → 𝕜, ContDiff ℝ ∞ v ∧
    ∀ t ∈ Icc (0 : ℝ) 0, v t = solution α ζ t

end ExpandedFA.PartV.FractionalSmoothCounterexample.Spec
