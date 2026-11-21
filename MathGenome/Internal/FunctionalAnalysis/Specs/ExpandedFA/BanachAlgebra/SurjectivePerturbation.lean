import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Topology.Closure

/-!
Independent statements for `fa2:p2:surjective-perturbation`, paper.tex
9937–9961. The maps use the original Banach spaces, their norm topology,
and their operator norm. There is no assumption on a kernel or a linear
right inverse. `RCLike` retains both scalar fields in the perturbation
statements. The spectral assertion is for arbitrary complex Banach spaces,
including the zero space, with the accepted spectrum convention.
-/

namespace Specs.ExpandedFA.BanachAlgebra.SurjectivePerturbation

universe u v w

/-- Exact bounded lifts, with the geometric-series estimate. The lift bound
for T is a premise of this quantitative version, not an assumed inverse. -/
def ControlledPerturbationLifts : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (T B : X →L[𝕜] Y) (C : ℝ), 0 < C →
    (∀ y : Y, ∃ x : X, T x = y ∧ ‖x‖ ≤ C * ‖y‖) → C * ‖B‖ < 1 →
    ∀ y : Y, ∃ x : X, (T + B) x = y ∧
      ‖x‖ ≤ (C / (1 - C * ‖B‖)) * ‖y‖

/-- Surjections in one norm neighborhood have one common bound on exact lifts. -/
def UniformPerturbationLifts : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y), Function.Surjective T →
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ B : X →L[𝕜] Y, ‖B‖ < δ →
      ∀ y : Y, ∃ x : X, (T + B) x = y ∧ ‖x‖ ≤ K * ‖y‖

/-- Every sufficiently small additive perturbation of a surjection is surjective. -/
def SurjectivityIsOpen : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y), Function.Surjective T →
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : X →L[𝕜] Y, ‖B‖ < δ → Function.Surjective (T + B)

/-- A spectral boundary value λI-A is never onto, without separability,
nonzeroness, or any splitting assumption. -/
def SpectralBoundaryNotSurjective : Prop :=
  ∀ (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (lam : ℂ),
    lam ∈ frontier (Conventions.AlgebraSpectrumValue ℂ (X →L[ℂ] X) A) →
      ¬ Function.Surjective (lam • (1 : X →L[ℂ] X) - A)

end Specs.ExpandedFA.BanachAlgebra.SurjectivePerturbation
