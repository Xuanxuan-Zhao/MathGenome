import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelRandomization
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalGluing

/-! Independent statements for `cor:conditional-sampling`, paper.tex §4.5.
The base carries an arbitrary specified sigma-algebra. The uniforms take values
in the closed unit interval with its trace sigma-algebra; their law is Lebesgue
probability. No completion of the original probability space is assumed. -/
open MeasureTheory ProbabilityTheory Set

namespace Specs.ProbabilityFoundations.Ch04.TransferSampling
universe u v w x

abbrev UnitInterval := Icc (0 : ℝ) 1
noncomputable abbrev uniform := KernelRandomization.unitUniform

/-- A single measurable sampling function works on every realization of the
first marginal equipped with an independent uniform variable. -/
def transferType : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T] [Nonempty T],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∀ (M : Measure (S × T)) [IsProbabilityMeasure M],
    ∃ g : S × UnitInterval → T, Measurable g ∧
      ∀ {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Ω → S) (V : Ω → UnitInterval),
        Measurable X → Measurable V → P.map X = M.map Prod.fst →
        P.map V = uniform → IndepFun X V P →
        P.map (fun ω => (X ω, g (X ω, V ω))) = M

/-- Independent uniforms, with their pair independent of X, realize the unique
conditionally independent gluing. The two sampling functions depend only on the
specified joint probabilities, and work for every such input realization. -/
def independentSamplingType : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [Nonempty T] [Nonempty U],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue U →
    ∀ (μ : Measure S) (M : Measure (S × T)) (N : Measure (S × U))
      [IsProbabilityMeasure M] [IsProbabilityMeasure N],
    M.map Prod.fst = μ → N.map Prod.fst = μ →
    ∃ (g : S × UnitInterval → T) (h : S × UnitInterval → U),
      Measurable g ∧ Measurable h ∧
      ∀ {Ω : Type x} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Ω → S) (V₁ V₂ : Ω → UnitInterval),
        Measurable X → Measurable V₁ → Measurable V₂ →
        P.map X = μ → P.map V₁ = uniform → P.map V₂ = uniform →
        IndepFun V₁ V₂ P → IndepFun X (fun ω => (V₁ ω, V₂ ω)) P →
        let Q := P.map (fun ω => (X ω, (g (X ω, V₁ ω), h (X ω, V₂ ω))))
        ConditionalGluing.gluingValue M N Q ∧
          ∀ Λ, ConditionalGluing.gluingValue M N Λ → Λ = Q

/-- The explicit product enlargement supplies both uniforms and preserves the
original probability and every original measurable X's law. -/
def enlargementType : Prop :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S), Measurable X →
    let P' := P.prod (uniform.prod uniform)
    let X' : Ω × (UnitInterval × UnitInterval) → S := fun p => X p.1
    let V₁ : Ω × (UnitInterval × UnitInterval) → UnitInterval := fun p => p.2.1
    let V₂ : Ω × (UnitInterval × UnitInterval) → UnitInterval := fun p => p.2.2
    IsProbabilityMeasure P' ∧ Measurable X' ∧ Measurable V₁ ∧ Measurable V₂ ∧
      P'.map Prod.fst = P ∧ P'.map X' = P.map X ∧
      P'.map V₁ = uniform ∧ P'.map V₂ = uniform ∧
      IndepFun V₁ V₂ P' ∧ IndepFun X' (fun p => (V₁ p, V₂ p)) P'

end Specs.ProbabilityFoundations.Ch04.TransferSampling
