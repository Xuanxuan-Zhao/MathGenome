import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework

/-!
Independent specifications for the fixed continuous mapping theorem,
paper.tex lines 1567–1590. Both spaces carry exactly their Borel sigma
algebras. The filter formulation includes sequences and imposes no metric,
separation, countability, or completeness assumptions.
-/

open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch06.ContinuousMapping

universe u v w z t

noncomputable section

/-- Continuous pushforward preserves weak convergence of Borel probability laws. -/
def weaklyConvergesMapType : Prop :=
  ∀ {ι : Type u} {E : Type v} {F : Type w}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (l : Filter ι) (μs : ι → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (g : E → F), Continuous g →
    WeakFramework.weaklyConvergesValue l μs μ →
    WeakFramework.weaklyConvergesValue l (fun i => (μs i).map g) (μ.map g)

/-- The variables at different indices and at the limit may have distinct
source probability spaces, with no completeness assumption. -/
def convergesInLawContinuousType : Prop :=
  ∀ {ι : Type u} {Ω : Type v} {Ωs : ι → Type w} {E : Type z} {F : Type t}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Ωs i)]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (l : Filter ι) (Ps : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (Ps i)]
    (Xs : ∀ i, Ωs i → E) (hXs : ∀ i, Measurable (Xs i))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : Measurable X)
    (g : E → F) (hg : Continuous g),
    WeakFramework.convergesInLawValue l Ps Xs hXs P X hX →
    WeakFramework.convergesInLawValue l Ps (fun i => g ∘ Xs i)
      (fun i => hg.measurable.comp (hXs i)) P (g ∘ X) (hg.measurable.comp hX)

end
end Specs.ProbabilityFoundations.Ch06.ContinuousMapping
