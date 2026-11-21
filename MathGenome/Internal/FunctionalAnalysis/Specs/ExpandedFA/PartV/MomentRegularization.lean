import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.MomentProjection
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Noisy part of `fa2:p5:moment-regularization`, paper.tex 23091–23126.
The smallest singular value is represented by its variational definition:
the minimum of ‖P_V A z‖ over unit vectors of A*V. The theorem below includes
attainment and strict positivity, rather than assuming a stability constant.
The reciprocal is explicitly zero on the zero stage. -/
noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.PartV.MomentRegularization.Spec
universe u v w
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
  [CompleteSpace X] [CompleteSpace Y]
open MomentProjection.Spec (trialSpace)

def stageMap (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] : trialSpace A V →L[𝕜] V :=
  V.orthogonalProjectionOnto.comp (A.comp (trialSpace A V).subtypeL)

def beta (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] : ℝ :=
  sInf {r | ∃ z : trialSpace A V, ‖z‖ = 1 ∧ ‖stageMap A V z‖ = r}

def noiseConstant (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] : ℝ :=
  if V = ⊥ then 0 else (beta A V)⁻¹

def StageStability : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V],
    V ≤ A.adjoint.ker.orthogonal →
    Function.Bijective (stageMap A V) ∧
    (V ≠ ⊥ → 0 < beta A V ∧
      IsLeast {r | ∃ z : trialSpace A V, ‖z‖ = 1 ∧ ‖stageMap A V z‖ = r}
        (beta A V)) ∧
    0 ≤ noiseConstant A V ∧
    (∀ z : trialSpace A V, ‖z‖ ≤ noiseConstant A V * ‖stageMap A V z‖) ∧
    (∀ g : Y, ∃! z : X, z ∈ trialSpace A V ∧
      V.starProjection (A z) = V.starProjection g)

/-- The variational value is an actual singular value, and is no larger than
any other nonnegative singular value. This bridges the variational definition
to the adjoint singular-vector equations, over both scalar fields. -/
def SingularCharacterization : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V],
    V ≤ A.adjoint.ker.orthogonal → V ≠ ⊥ →
    (∃ (e : trialSpace A V) (f : V), ‖e‖ = 1 ∧ ‖f‖ = 1 ∧
      stageMap A V e = (beta A V : 𝕜) • f ∧
      (stageMap A V).adjoint f = (beta A V : 𝕜) • e) ∧
    ∀ (σ : ℝ) (e : trialSpace A V) (f : V), 0 ≤ σ → ‖e‖ = 1 → ‖f‖ = 1 →
      stageMap A V e = (σ : 𝕜) • f → beta A V ≤ σ

def NoisyError : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V],
    V ≤ A.adjoint.ker.orthogonal → ∀ (x z : X) (g : Y) (δ : ℝ),
    ‖g - A x‖ ≤ δ → z ∈ trialSpace A V →
    V.starProjection (A z) = V.starProjection g →
    ‖z - x‖ ≤ Metric.infDist x (trialSpace A V : Set X) + δ * noiseConstant A V

def ZeroStage : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (g : Y),
    noiseConstant A (⊥ : Submodule 𝕜 Y) = 0 ∧
    ∀ z : X, (z ∈ trialSpace A ⊥ ∧
      (⊥ : Submodule 𝕜 Y).starProjection (A z) =
        (⊥ : Submodule 𝕜 Y).starProjection g) ↔ z = 0

/-- A single a priori choice works for every nonnegative stage amplification sequence. -/
def SlowChoice : Prop :=
  ∀ C : ℕ → ℝ, (∀ n, 0 ≤ C n) → ∃ n : ℝ → ℕ,
    Filter.Tendsto n (𝓝[>] (0 : ℝ)) Filter.atTop ∧
    Filter.Tendsto (fun δ => δ * C (n δ)) (𝓝[>] (0 : ℝ)) (𝓝 0)

def Regularization : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : ℕ → Submodule 𝕜 Y)
    [∀ n, FiniteDimensional 𝕜 (V n)], Monotone V →
    closure (⋃ n, (V n : Set Y)) = (A.adjoint.ker.orthogonal : Set Y) →
    ∀ x : X, x ∈ A.ker.orthogonal →
    (∃ n : ℝ → ℕ, Filter.Tendsto n (𝓝[>] (0 : ℝ)) Filter.atTop ∧
      Filter.Tendsto (fun δ => δ * noiseConstant A (V (n δ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
    ∀ (n : ℝ → ℕ), Filter.Tendsto n (𝓝[>] (0 : ℝ)) Filter.atTop →
      Filter.Tendsto (fun δ => δ * noiseConstant A (V (n δ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) →
      ∀ (g : ℝ → Y) (z : ℝ → X),
        (∀ δ > 0, ‖g δ - A x‖ ≤ δ) →
        (∀ δ > 0, z δ ∈ trialSpace A (V (n δ)) ∧
          (V (n δ)).starProjection (A (z δ)) = (V (n δ)).starProjection (g δ)) →
        Filter.Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 x)
end ExpandedFA.PartV.MomentRegularization.Spec
