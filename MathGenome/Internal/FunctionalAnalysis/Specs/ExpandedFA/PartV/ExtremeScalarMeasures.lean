import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-! The finite real/complex Radon measure ball in `fa2:p5:extreme-measures`.
Convexity and extremality use real scalars, also for complex measures.
The variation is the partition variation of the actual countably additive
scalar measure. In particular its mass is not the absolute value of its
scalar mass. No separability or countability assumption is made. -/

noncomputable section
namespace ExpandedFA.PartV.ExtremeScalarMeasuresSpec
open Set MeasureTheory
open scoped ENNReal
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
universe u v

/-- The closed total-variation unit ball of finite scalar Radon measures. -/
def measureBall (K : Type u) [TopologicalSpace K] [MeasurableSpace K]
    (𝕜 : Type*) [RCLike 𝕜] : Set (VectorMeasure K 𝕜) :=
  {ν | FiniteScalarRadon ν ∧ ν.variation univ ≤ 1}

def ScalarCharacterization (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (ν : VectorMeasure K 𝕜),
    ν ∈ (measureBall K 𝕜).extremePoints ℝ ↔
      ∃ (x : K) (z : 𝕜), ‖z‖ = 1 ∧ ν = VectorMeasure.dirac x z

def ComplexCharacterization : Prop := ScalarCharacterization.{u} ℂ

def RealCharacterization : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (ν : SignedMeasure K),
    ν ∈ (measureBall K ℝ).extremePoints ℝ ↔
      ∃ x : K, ν = VectorMeasure.dirac x 1 ∨ ν = VectorMeasure.dirac x (-1)

/-- In particular, every point strictly inside the ball fails extremality. -/
def InteriorNotExtreme (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (ν : VectorMeasure K 𝕜),
    FiniteScalarRadon ν → ν.variation univ < 1 →
      ν ∉ (measureBall K 𝕜).extremePoints ℝ

/-- Exact normalized restrictions at a Borel set of intermediate variation mass.
The two coefficients are the original variation masses, and both pieces have
variation norm one. This also records their distinctness. -/
def RestrictionDecomposition (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (ν : VectorMeasure K 𝕜),
    FiniteScalarRadon ν → ν.variation univ = 1 →
    ∀ A : Set K, MeasurableSet A → 0 < ν.variation A → ν.variation A < 1 →
    let a := ν.variation.real A
    let b := ν.variation.real Aᶜ
    let ν₁ := a⁻¹ • ν.restrict A
    let ν₂ := b⁻¹ • ν.restrict Aᶜ
    0 < a ∧ 0 < b ∧ a + b = 1 ∧
    ν₁ ∈ measureBall K 𝕜 ∧ ν₂ ∈ measureBall K 𝕜 ∧
    ν₁.variation univ = 1 ∧ ν₂.variation univ = 1 ∧
    ν₁ ≠ ν₂ ∧ ν = a • ν₁ + b • ν₂

/-- Uniform statements in the scalar field, including both R and C. -/
def AllScalarCharacterization : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜], ScalarCharacterization.{u} 𝕜

def AllInteriorNotExtreme : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜], InteriorNotExtreme.{u} 𝕜

def AllRestrictionDecomposition : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜], RestrictionDecomposition.{u} 𝕜

end ExpandedFA.PartV.ExtremeScalarMeasuresSpec
