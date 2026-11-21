import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ProperSupportConvolution
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Independent formulation of the heat part of
`paper.tex`, `fa2:p4:laplace-heat-fundamental`, including dimension zero.
Coordinate zero is time; the remaining coordinates are spatial. The ambient
`Domain` has the supremum norm, so the Euclidean square is written explicitly.
All scalar-valued distribution pairings are linear, including over ℂ. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ContDiff Distributions Pointwise

namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

/-- The Euclidean square, independently of the norm on `Domain d`. -/
def spatialSquare {d : ℕ} (x : Domain d) : ℝ := ∑ i, (x i) ^ 2

/-- The positive-time Gaussian formula. Its values for nonpositive time are
immaterial; the space-time kernel below vanishes there. -/
def gaussianSlice (d : ℕ) (t : ℝ) (x : Domain d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-spatialSquare x / (4 * t))

/-- The causal space-time function, with the value zero on the time-zero slice. -/
def heatKernel (d : ℕ) (z : Domain (d + 1)) : ℝ :=
  if 0 < z 0 then gaussianSlice d (z 0) (Fin.tail z) else 0

/-- Closed future half-space, with an arbitrary initial time. -/
def future (d : ℕ) (a : ℝ) : Set (Domain (d + 1)) := {z | a ≤ z 0}

abbrev SpaceTimeTests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  Tests 𝕜 (⊤ : Opens (Domain (d + 1)))
abbrev SpaceTimeDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  ScalarDistribution 𝕜 (⊤ : Opens (Domain (d + 1)))

/-- Evaluation in the actual scalar-linear dual, for either scalar field. -/
def delta (𝕜 : Type) [RCLike 𝕜] (d : ℕ) : SpaceTimeDistribution 𝕜 d :=
  (BoundedContinuousFunction.evalCLM 𝕜 (0 : Domain (d + 1))).comp
    (TestFunction.toBoundedContinuousFunctionCLM 𝕜)

/-- ∂ₜ - Σᵢ∂²ₓᵢ, using the accepted transpose-sign derivative interface. -/
def heatOperator {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : SpaceTimeDistribution 𝕜 d) : SpaceTimeDistribution 𝕜 d :=
  Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue 𝕜 (d+1) ⊤ [0] u -
    ∑ i : Fin d,
      Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue
        𝕜 (d+1) ⊤ [i.succ, i.succ] u

/-- The density pairing is part of the conclusion; `E` is not an arbitrary
fundamental solution introduced without a bridge to the displayed function. -/
def HasHeatKernelPairing {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E : SpaceTimeDistribution 𝕜 d) : Prop :=
  ∀ φ : SpaceTimeTests 𝕜 d,
    E φ = ∫ z : Domain (d+1), (heatKernel d z : 𝕜) * φ z

end ExpandedFA.PartIV.HeatFundamental

namespace Specs.ExpandedFA.PartIV.HeatFundamental
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.PartIV.HeatFundamental

/-- Normalization includes the mass-one zero-dimensional slice. -/
def sliceMassType : Prop := ∀ (d : ℕ) (t : ℝ), 0 < t →
  Integrable (gaussianSlice d t) ∧ (∫ x : Domain d, gaussianSlice d t x) = 1

/-- Integrability is in space-time, through the initial singularity, for
both scalar fields and all d ≥ 0. -/
def localIntegrabilityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  LocallyIntegrable (fun z : Domain (d+1) => (heatKernel d z : 𝕜))

/-- The positive-time slice boundary term tends to the point evaluation. -/
def initialBoundaryType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] (d : ℕ)
    (φ : SpaceTimeTests 𝕜 d),
  Tendsto (fun t : ℝ => ∫ x : Domain d,
    gaussianSlice d t x • φ (Fin.cons t x)) (𝓝[>] 0) (𝓝 (φ 0))

/-- Integration by parts away from the initial singularity. This is a helper
obligation; the original distribution equation still requires the ε ↓ 0 limit. -/
def truncatedIdentityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (φ : SpaceTimeTests 𝕜 d) (ε : ℝ), 0 < ε →
  (∫ z : Domain (d+1) in {z | ε < z 0}, (heatKernel d z : 𝕜) *
    (-(testPartialCLM [0] φ) z -
      ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z)) =
    ∫ x : Domain d, gaussianSlice d ε x • φ (Fin.cons ε x)

/-- The full initial contribution, with the signs of ∂ₜ-Δ expanded on tests. -/
def weakIdentityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (φ : SpaceTimeTests 𝕜 d),
  (∫ z : Domain (d+1), (heatKernel d z : 𝕜) *
    (-(testPartialCLM [0] φ) z -
      ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z)) = φ 0

/-- The distribution support is contained in the closed causal half-space. -/
def causalSupportType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (E : SpaceTimeDistribution 𝕜 d),
  HasHeatKernelPairing E → distributionSupport E ⊆ future d 0

/-- Construction of the regular distribution and its causal support. -/
def kernelDistributionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  ∃ E : SpaceTimeDistribution 𝕜 d,
    HasHeatKernelPairing E ∧ distributionSupport E ⊆ future d 0

/-- The heat operator, including its finite linear combination, commutes with
proper convolution against an arbitrary compactly supported distribution. -/
def heatConvolutionType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E f u : SpaceTimeDistribution 𝕜 d), IsCompact (distributionSupport f) →
  IsProperConvolution E f u → IsProperConvolution (heatOperator E) f (heatOperator u)

/-- The original heat fundamental solution, its density representation,
delta source, and convolution solution for every compactly supported datum.
The support-addition bound also gives causality for every lower time bound
on the data, not only for data beginning at time zero. -/
def fundamentalSolutionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  ∃ E : SpaceTimeDistribution 𝕜 d,
    HasHeatKernelPairing E ∧ heatOperator E = delta 𝕜 d ∧
    distributionSupport E ⊆ future d 0 ∧
    ∀ f : SpaceTimeDistribution 𝕜 d, IsCompact (distributionSupport f) →
      ∃ u : SpaceTimeDistribution 𝕜 d,
        IsProperConvolution E f u ∧ heatOperator u = f ∧
        distributionSupport u ⊆ distributionSupport E + distributionSupport f ∧
        ∀ a : ℝ, distributionSupport f ⊆ future d a →
          distributionSupport u ⊆ future d a

/-- A conditional assembly interface, not a proof of the outstanding helper. -/
def truncatedAssemblyType : Prop := truncatedIdentityType → fundamentalSolutionType

end Specs.ExpandedFA.PartIV.HeatFundamental
