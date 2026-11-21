import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.EtemadiStrongLaw
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! Independent specification of paper.tex:3041–3069. All sums are one-based;
`X 0` is unused. The common law can have arbitrary atoms. The supremum is
an actual real supremum over all real thresholds. -/

open MeasureTheory Filter
open scoped Topology

namespace Specs.ProbabilityFoundations.Ch08.GlivenkoCantelli

universe u

def empiricalDistributionType := {Ω : Type u} → (ℕ → Ω → ℝ) → ℕ → Ω → ℝ → ℝ

noncomputable def empiricalDistributionValue : empiricalDistributionType :=
  fun X n ω x => (∑ k ∈ Finset.Icc 1 n, if X k ω ≤ x then (1 : ℝ) else 0) / (n : ℝ)

def commonDistributionType := {Ω : Type u} → [MeasurableSpace Ω] →
  Measure Ω → (ℕ → Ω → ℝ) → ℝ → ℝ

noncomputable def commonDistributionValue : commonDistributionType :=
  fun P X x => (P {ω | X 1 ω ≤ x}).toReal

def distributionDeviationType := {Ω : Type u} → [MeasurableSpace Ω] →
  Measure Ω → (ℕ → Ω → ℝ) → ℕ → Ω → ℝ

noncomputable def distributionDeviationValue : distributionDeviationType :=
  fun P X n ω => ⨆ x : ℝ, |empiricalDistributionValue X n ω x - commonDistributionValue P X x|

def deviationMeasurableType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (_hX : ∀ k : ℕ, Measurable (X (k + 1))) (n : ℕ),
    Measurable (distributionDeviationValue P X n)

def rationalSupremumType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (_hX : ∀ k : ℕ, Measurable (X (k + 1))) (n : ℕ) (ω : Ω),
    distributionDeviationValue P X n ω =
      ⨆ q : ℚ, |empiricalDistributionValue X n ω (q : ℝ) - commonDistributionValue P X q|

def glivenkoCantelliType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (_hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (_hindep : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue
      P (fun k : ℕ => X (k + 1)))
    (_hident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X (k + 1)) (X 1) P P),
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => distributionDeviationValue P X n ω) atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch08.GlivenkoCantelli
