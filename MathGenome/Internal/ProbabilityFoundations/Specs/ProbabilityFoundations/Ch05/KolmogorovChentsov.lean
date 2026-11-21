import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.Modifications
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.DyadicHolderExtension
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.EReal.Basic

/-! Kolmogorov--Chentsov, paper.tex:1349–1383. Expectations are extended
nonnegative integrals, embedded in `EReal` so that a real constant `C` retains
its sign. In particular nonnegativity of `C` is not an extra hypothesis.
All events and coordinate maps use the original sigma-algebra. -/
open MeasureTheory TopologicalSpace
open ProbabilityFoundations.Ch05
universe u v

namespace Specs.ProbabilityFoundations.Ch05.KolmogorovChentsov

/-- The complete admissible exponent range, on one event, with continuous paths
also on the exceptional set. No inhabited-state or complete-measure assumption. -/
def kolmogorovChentsovType : Prop :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω]
    [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (T p β C : ℝ),
    0 < T → 0 < p → 0 < β → ∀ X : Time T → Ω → S,
    (∀ t, Measurable (X t)) →
    (∀ s t : Time T,
      ((∫⁻ ω, ENNReal.ofReal (dist (X t ω) (X s ω) ^ p) ∂P) : EReal) ≤
        ((C * dist t s ^ (1 + β) : ℝ) : EReal)) →
    ∃ Y : Time T → Ω → S,
      (∀ t, Measurable (Y t)) ∧ ModificationsSpec.modificationValue P X Y ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      ∃ G : Set Ω, MeasurableSet G ∧ P G = 1 ∧
        ∀ ω ∈ G, ∀ γ : ℝ, 0 < γ → γ < β / p →
          ∃ K : ℝ, 0 ≤ K ∧ Dyadic.Bound γ K (fun t => Y t ω)

/-- The uniqueness assertion needs no moment hypothesis and includes `T = 0`. -/
def continuousModificationsUniqueType : Prop :=
  ModificationsSpec.continuousModificationsUnique.{u, v}

/-- With a single time the original process itself has continuous paths. -/
def zeroTimeType : Prop :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω]
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Time 0 → Ω → S),
    (∀ t, Measurable (X t)) →
    (∀ ω, Continuous (fun t => X t ω)) ∧
    ∃ Y : Time 0 → Ω → S, (∀ t, Measurable (Y t)) ∧
      ModificationsSpec.modificationValue P X Y ∧
      ∀ ω, Continuous (fun t => Y t ω)

end Specs.ProbabilityFoundations.Ch05.KolmogorovChentsov
