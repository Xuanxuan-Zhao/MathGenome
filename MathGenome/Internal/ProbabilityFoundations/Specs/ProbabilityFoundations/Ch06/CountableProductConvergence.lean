import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.CylinderFramework
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.ProductMeasure

/-! Independent statements for paper.tex, Theorem `p06-countable-products`.
Any countable index type is allowed; in particular `ℕ+` gives the paper's
positive indexing. All sigma algebras are the original Borel sigma algebras.
No factor is assumed complete. -/

open MeasureTheory Filter Topology TopologicalSpace

namespace Specs.ProbabilityFoundations.Ch06.CountableProductConvergence

universe u v
noncomputable section

/-- The probability law constructed on the uncompleted product sigma algebra. -/
def productLawType :=
  ∀ {I : Type u} {S : I → Type v} [∀ i, MeasurableSpace (S i)],
    (∀ i, ProbabilityMeasure (S i)) → ProbabilityMeasure (∀ i, S i)

def productLawValue : productLawType.{u,v} := fun μ =>
  ⟨Measure.infinitePi (fun i => (μ i : Measure _)), inferInstance⟩

/-- The canonical product topology is separable and metrizable and its Borel
sigma algebra equals the cylinder sigma algebra, hence also the Pi one. -/
def productBridgeType : Prop :=
  ∀ {I : Type u} [Countable I] (S : I → Type v)
    [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)],
    MetrizableSpace (∀ i, S i) ∧ SeparableSpace (∀ i, S i) ∧
      borel (∀ i, S i) =
        _root_.ProbabilityFoundations.Ch05.CylinderFramework.cylinderSigma S

/-- All finite supports are tested, including the empty support. -/
def finiteMarginalsCriterionType : Prop :=
  ∀ {I : Type u} [Countable I] {S : I → Type v}
    [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)]
    (νs : ℕ → ProbabilityMeasure (∀ i, S i)) (ν : ProbabilityMeasure (∀ i, S i)),
    WeakFramework.weaklyConvergesValue atTop νs ν ↔
      ∀ F : Finset I,
        WeakFramework.weaklyConvergesValue atTop
          (fun n => (νs n).map F.restrict) (ν.map F.restrict)

def productConvergenceType : Prop :=
  ∀ {I : Type u} [Countable I] {S : I → Type v}
    [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)]
    (μs : ℕ → ∀ i, ProbabilityMeasure (S i)) (μ : ∀ i, ProbabilityMeasure (S i)),
    WeakFramework.weaklyConvergesValue atTop
      (fun n => productLawValue (μs n)) (productLawValue μ) ↔
        ∀ i, WeakFramework.weaklyConvergesValue atTop (fun n => μs n i) (μ i)

end
end Specs.ProbabilityFoundations.Ch06.CountableProductConvergence
