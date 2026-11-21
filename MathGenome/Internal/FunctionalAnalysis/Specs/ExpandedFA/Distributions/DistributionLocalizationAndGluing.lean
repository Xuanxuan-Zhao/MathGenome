import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionLFTopology
import Mathlib.Topology.Algebra.Support

open Set TopologicalSpace
open scoped Distributions Topology

universe u

namespace ExpandedFA.Distributions

/-- The open subset of Ω on which a distribution vanishes. -/
def vanishingRegion {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : ScalarDistribution 𝕜 Ω) : Set (Domain d) :=
  ⋃₀ {V | IsOpen V ∧ V ⊆ Ω ∧ ∀ φ : Tests 𝕜 Ω, tsupport φ ⊆ V → u φ = 0}

/-- Support relative to the distribution's domain. -/
def distributionSupport {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : ScalarDistribution 𝕜 Ω) : Set (Domain d) :=
  (Ω : Set (Domain d)) \ vanishingRegion u

/-- Smooth multiplication, in the same scalar field as the tests. -/
noncomputable def multiplyTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a) : Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul 𝕜 𝕜) ha

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing
open _root_.ExpandedFA.Distributions

def supportType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
  ScalarDistribution 𝕜 Ω → Set (Domain d)

def supportValue : supportType := fun _ _ _ _ u => distributionSupport u

/-- Agreement on every intersection, and a unique distribution on the entire union.
The original index type is arbitrary. -/
def gluingType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (ι : Type u) (U : ι → Opens (Domain d)) (v : ∀ i, ScalarDistribution 𝕜 (U i)),
  (∀ i j (φ : Tests 𝕜 (U i ⊓ U j)),
    v i (TestFunction.monoCLM 𝕜 φ) = v j (TestFunction.monoCLM 𝕜 φ)) →
  ∃! w : ScalarDistribution 𝕜 (⨆ i, U i),
    ∀ i (φ : Tests 𝕜 (U i)), w (TestFunction.monoCLM 𝕜 φ) = v i φ

/-- Vanishing holds on the whole union, not merely on each member. -/
def vanishingUnionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω)
    (ι : Type u) (V : ι → Set (Domain d)),
  (∀ i, IsOpen (V i)) →
  (∀ i (φ : Tests 𝕜 Ω), tsupport φ ⊆ V i → u φ = 0) →
  ∀ φ : Tests 𝕜 Ω, tsupport φ ⊆ ⋃ i, V i → u φ = 0

def supportVanishingType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω),
  IsOpen (vanishingRegion u) ∧ vanishingRegion u ⊆ Ω ∧
  ∀ φ : Tests 𝕜 Ω, tsupport φ ⊆ vanishingRegion u → u φ = 0

/-- Two tests equal on an open neighborhood of the support give equal pairings. -/
def pairingLocalityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω) (φ ψ : Tests 𝕜 Ω)
    (V : Set (Domain d)), IsOpen V → distributionSupport u ⊆ V →
    EqOn φ ψ V → u φ = u ψ

/-- Any smooth cutoff equal to one near the support leaves the pairing unchanged. -/
def cutoffLocalityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (V : Set (Domain d)), IsOpen V → distributionSupport u ⊆ V →
    EqOn a 1 V → ∀ φ : Tests 𝕜 Ω, u (multiplyTest a ha φ) = u φ

/-- Compact subsets of the domain admit compactly supported cutoffs equal to
one on a neighborhood, in particular for compact distribution supports. -/
def cutoffExistenceType : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (K : Set (Domain d)), IsCompact K → K ⊆ Ω →
    ∃ (χ : Tests ℝ Ω) (V : Set (Domain d)), IsOpen V ∧ K ⊆ V ∧ EqOn χ 1 V

end Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing
