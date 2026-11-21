import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalProductCriterion
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod

/-! Independent statements for the second assertion of `prop:conditional-gluing`.
The triple is associated as S × (T × U), with the product sigma-algebra.
The first space is arbitrary; standard Borel assumptions occur only on T and U.
Empty targets are allowed: the given probability marginals imply nonemptiness.
-/
open MeasureTheory ProbabilityTheory

namespace Specs.ProbabilityFoundations.Ch04.ConditionalGluing
universe u v w

noncomputable def gluedLawValue {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure S) (K : Kernel S T) (L : Kernel S U) : Measure (S × (T × U)) :=
  μ.compProd (K ×ₖ L)

def gluedLawType :=
  {S : Type u} → {T : Type v} → {U : Type w} →
  [MeasurableSpace S] → [MeasurableSpace T] → [MeasurableSpace U] →
  Measure S → Kernel S T → Kernel S U → Measure (S × (T × U))

noncomputable def gluingValue {S : Type u} {T : Type v} {U : Type w}
    [mS : MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (M : Measure (S × T)) (N : Measure (S × U)) (Λ : Measure (S × (T × U))) : Prop :=
  IsProbabilityMeasure Λ ∧
  Λ.map (fun p => (p.1, p.2.1)) = M ∧
  Λ.map (fun p => (p.1, p.2.2)) = N ∧
  ConditionalIndependence.independenceValue
    (MeasurableSpace.comap Prod.fst mS) Λ (fun p => p.2.1) (fun p => p.2.2)

def gluingType :=
  {S : Type u} → {T : Type v} → {U : Type w} →
  [MeasurableSpace S] → [MeasurableSpace T] → [MeasurableSpace U] →
  Measure (S × T) → Measure (S × U) → Measure (S × (T × U)) → Prop

/-- The formula characterizes precisely all probability laws with the two
prescribed projections and the stated conditional independence. -/
def formulaType : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue U →
    ∀ (μ : Measure S) [IsProbabilityMeasure μ]
      (M : Measure (S × T)) (N : Measure (S × U))
      (K : Kernel S T) (L : Kernel S U) [IsMarkovKernel K] [IsMarkovKernel L],
    M = μ.compProd K → N = μ.compProd L →
    ∀ Λ, gluingValue M N Λ ↔ Λ = gluedLawValue μ K L

/-- No nonemptiness hypothesis is added to the source's assertion. -/
def existenceUniqueType : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue U →
    ∀ (μ : Measure S) (M : Measure (S × T)) (N : Measure (S × U))
      [IsProbabilityMeasure M] [IsProbabilityMeasure N],
    M.map Prod.fst = μ → N.map Prod.fst = μ → ∃! Λ, gluingValue M N Λ

/-- The displayed formula is independent of every choice of disintegrations. -/
def choiceIndependentType : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (hT : _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T)
    (hU : _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue U)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K K' : Kernel S T) (L L' : Kernel S U)
    [IsMarkovKernel K] [IsMarkovKernel K'] [IsMarkovKernel L] [IsMarkovKernel L'],
    μ.compProd K = μ.compProd K' → μ.compProd L = μ.compProd L' →
    gluedLawValue μ K L = gluedLawValue μ K' L'

end Specs.ProbabilityFoundations.Ch04.ConditionalGluing
