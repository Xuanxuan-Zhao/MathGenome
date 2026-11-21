import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ProperSupportConvolution
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Independent statements for the Laplace portion of
`fa2:p4:laplace-heat-fundamental`. The coordinate domain has a sup norm;
the radius and sphere below explicitly use its Euclidean norm. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions ContDiff

namespace ExpandedFA.PartIV.LaplaceFundamental
open ExpandedFA.Distributions

def euclideanRadius {d : ℕ} (x : Domain d) : ℝ := ‖WithLp.toLp 2 x‖

/-- Total Euclidean surface measure of the unit sphere S^(d-1). -/
def sphereArea (d : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.real univ

/-- Values at zero use Mathlib's totalized log and real powers. They do not
change any distribution in positive dimension. No d=0 fundamental solution
is asserted. -/
def kernel (d : ℕ) (x : Domain d) : ℝ :=
  if d = 1 then euclideanRadius x / 2
  else if d = 2 then Real.log (euclideanRadius x) / (2 * Real.pi)
  else (euclideanRadius x) ^ (2 - (d : ℝ)) / ((2 - (d : ℝ)) * sphereArea d)

def scalarKernel (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (x : Domain d) : 𝕜 :=
  algebraMap ℝ 𝕜 (kernel d x)

def testLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) : Tests 𝕜 (⊤ : Opens (Domain d)) :=
  ∑ i : Fin d, testPartialCLM [i, i] φ

def distributionLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) :=
  ∑ i : Fin d, Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue
    𝕜 d ⊤ [i, i] u

/-- Scalar-linear evaluation, also for complex tests. -/
def diracZero (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) where
  toFun φ := φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

/-- The integration distribution. Its integral formula is asserted only after
local integrability has been proved, since the library constructor is total. -/
def kernelDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul 𝕜 𝕜) volume
    (scalarKernel 𝕜 d)

end ExpandedFA.PartIV.LaplaceFundamental

namespace Specs.ExpandedFA.PartIV.LaplaceFundamental
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.PartIV.LaplaceFundamental

/-- All three source formulas with the Euclidean radius, including constants. -/
def formulasType : Prop :=
  (∀ x : Domain 1, kernel 1 x = |x 0| / 2) ∧
  (∀ x : Domain 2, kernel 2 x = Real.log (euclideanRadius x) / (2 * Real.pi)) ∧
  (∀ d : ℕ, 3 ≤ d → ∀ x : Domain d,
    kernel d x = (euclideanRadius x) ^ (2 - (d : ℝ)) /
      ((2 - (d : ℝ)) * sphereArea d))

def localIntegrabilityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  1 ≤ d → LocallyIntegrable (scalarKernel 𝕜 d) volume

/-- This includes the mass at the origin, with a bilinear scalar pairing. -/
def pairingType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), 1 ≤ d →
  ∀ φ : Tests 𝕜 (⊤ : Opens (Domain d)),
    ∫ x, scalarKernel 𝕜 d x * testLaplacian φ x = φ 0

def fundamentalSolutionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  1 ≤ d → distributionLaplacian (kernelDistribution 𝕜 d) = diracZero 𝕜 d

/-- Convolution is the upstream tensor/cutoff convolution of distributions;
no smoothness or integrability is required of the compactly supported datum. -/
def convolutionSolutionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  1 ≤ d → ∀ v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)),
    IsCompact (distributionSupport v) →
    ∃ u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)),
      IsProperConvolution (kernelDistribution 𝕜 d) v u ∧ distributionLaplacian u = v

def pairingOneType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))),
    ∫ x, scalarKernel 𝕜 1 x * testLaplacian φ x = φ 0

def fundamentalSolutionOneType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  distributionLaplacian (kernelDistribution 𝕜 1) = diracZero 𝕜 1

/-- A general convolution consequence, without a hypothesis on a density. -/
def laplacianConvolutionType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E v u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
    IsCompact (distributionSupport v) → IsProperConvolution E v u →
    distributionLaplacian E = diracZero 𝕜 d → distributionLaplacian u = v

def convolutionSolutionOneType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain 1))),
    IsCompact (distributionSupport v) →
    ∃ u : ScalarDistribution 𝕜 (⊤ : Opens (Domain 1)),
      IsProperConvolution (kernelDistribution 𝕜 1) v u ∧ distributionLaplacian u = v

end Specs.ExpandedFA.PartIV.LaplaceFundamental
