import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces

/-! Independent statements for the measure-extremality step of
`fa2:p1:banach-stone`, paper.tex:6658–6677. The ambient objects are the
same native countably additive scalar measures as in Riesz--Markov.
The ball uses the total variation on the whole space, and convexity is real
also for complex scalar measures. -/

namespace ExpandedFA.Supplements.MeasureBallExtremesSpec

open Set MeasureTheory
universe u

/-- The closed unit ball of finite scalar Radon measures for total variation.
Finiteness is explicit, so `Measure.real` never discards an infinite mass. -/
def UnitBall (K : Type u) [TopologicalSpace K] [MeasurableSpace K]
    (𝕜 : Type*) [RCLike 𝕜] : Set (VectorMeasure K 𝕜) :=
  {ν | FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon ν ∧
    ν.variation.real univ ≤ 1}

/-- The complete classification for both manuscript scalar fields. -/
def Classification : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] [Nonempty K]
    (𝕜 : Type*) [RCLike 𝕜] (ν : VectorMeasure K 𝕜),
    ν ∈ P1.C24FacesSpec.extremePoints (UnitBall K 𝕜) ↔
      ∃ (s : K) (c : 𝕜), ‖c‖ = 1 ∧ ν = VectorMeasure.dirac s c

/-- In the real case unimodular coefficients are precisely the two signs. -/
def RealSigns : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] [Nonempty K] (ν : VectorMeasure K ℝ),
    ν ∈ P1.C24FacesSpec.extremePoints (UnitBall K ℝ) ↔
      ∃ s : K, ν = VectorMeasure.dirac s 1 ∨ ν = VectorMeasure.dirac s (-1)

/-- Empty compact domains give the zero continuous-function and measure
spaces. The nonempty classification is deliberately not applied here: the
unit ball of a zero vector space has its zero vector as an extreme point. -/
def EmptySpaces : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [IsEmpty K] (𝕜 : Type*) [RCLike 𝕜],
    (∀ f : C(K, 𝕜), f = 0) ∧ (∀ ν : VectorMeasure K 𝕜, ν = 0)

end ExpandedFA.Supplements.MeasureBallExtremesSpec
