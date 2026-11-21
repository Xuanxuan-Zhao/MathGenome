import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ProperSupportConvolution
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionRegularization
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardySupportBridge
import Mathlib.Topology.Order.Compact

/-! The compact-distribution theorem at `fa2:p4:titchmarsh`.
The real line is the upstream one-dimensional Euclidean domain. Endpoints are
computed from its coordinate image, not from the support of a representative.
Both manuscript scalar fields are included by `RCLike`. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions Topology Pointwise

namespace ExpandedFA.PartIV.Titchmarsh
open ExpandedFA.Distributions

abbrev LineDistribution (𝕜 : Type) [RCLike 𝕜] :=
  ScalarDistribution 𝕜 (⊤ : Opens (Domain 1))

/-- Actual distribution support in real-line coordinates. -/
def realSupport {𝕜 : Type} [RCLike 𝕜] (u : LineDistribution 𝕜) : Set ℝ :=
  (fun x : Domain 1 => x 0) '' distributionSupport u

def leftEndpoint {𝕜 : Type} [RCLike 𝕜] (u : LineDistribution 𝕜) : ℝ :=
  sInf (realSupport u)

def rightEndpoint {𝕜 : Type} [RCLike 𝕜] (u : LineDistribution 𝕜) : ℝ :=
  sSup (realSupport u)

/-- Reversing the sign gives the endpoint needed for reflection. -/
def orientedSupport {𝕜 : Type} [RCLike 𝕜] (u : LineDistribution 𝕜) (s : ℝ) : Set ℝ :=
  (fun x : Domain 1 => s * x 0) '' distributionSupport u

def orientedEndpoint {𝕜 : Type} [RCLike 𝕜] (u : LineDistribution 𝕜) (s : ℝ) : ℝ :=
  sInf (orientedSupport u s)

def LowerSupportBound {𝕜 : Type} [RCLike 𝕜]
    (u : LineDistribution 𝕜) (s c : ℝ) : Prop :=
  ∀ x ∈ distributionSupport u, c ≤ s * x 0

/-- Vanishing on the entire initial open interval, in the distribution sense. -/
def VanishesBefore {𝕜 : Type} [RCLike 𝕜] (u : LineDistribution 𝕜) (c : ℝ) : Prop :=
  ∀ φ : Tests 𝕜 (⊤ : Opens (Domain 1)),
    tsupport φ ⊆ {x | x 0 < c} → u φ = 0

namespace Spec

/-- Nonvanishing and both endpoint identities, for the actual tensor/cutoff
convolution relation. Compactness of the output is included. -/
def ConvolutionEndpoints : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u v w : LineDistribution 𝕜),
  IsCompact (distributionSupport u) → IsCompact (distributionSupport v) →
  u ≠ 0 → v ≠ 0 → IsProperConvolution u v w →
  w ≠ 0 ∧ IsCompact (distributionSupport w) ∧
    leftEndpoint w = leftEndpoint u + leftEndpoint v ∧
    rightEndpoint w = rightEndpoint u + rightEndpoint v

/-- Existence and endpoint equalities without an input convolution witness. -/
def ConvolutionExistence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u v : LineDistribution 𝕜),
  IsCompact (distributionSupport u) → IsCompact (distributionSupport v) →
  u ≠ 0 → v ≠ 0 → ∃ w : LineDistribution 𝕜,
    IsProperConvolution u v w ∧ w ≠ 0 ∧
    leftEndpoint w = leftEndpoint u + leftEndpoint v ∧
    rightEndpoint w = rightEndpoint u + rightEndpoint v

/-- No initial interval of zeros can extend beyond the sum of the lower
endpoints. This quantifies over all real cut points, including the endpoints. -/
def NoExtraInitialInterval : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u v w : LineDistribution 𝕜),
  IsCompact (distributionSupport u) → IsCompact (distributionSupport v) →
  u ≠ 0 → v ≠ 0 → IsProperConvolution u v w →
    ∀ c : ℝ, VanishesBefore w c ↔ c ≤ leftEndpoint u + leftEndpoint v

end Spec
end ExpandedFA.PartIV.Titchmarsh
