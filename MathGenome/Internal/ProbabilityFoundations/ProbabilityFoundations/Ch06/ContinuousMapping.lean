import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuousMapping

/-!
The fixed continuous mapping theorem (paper.tex, lines 1567–1590).
Composition with a continuous map preserves bounded continuous real tests;
the upstream transfer identity identifies their pushforward integrals.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction

namespace ProbabilityFoundations.Ch06

universe u v w z t

noncomputable section

/-- Continuous maps preserve weak convergence on arbitrary Borel topological
spaces. In particular this applies to sequences by taking `l = atTop`. -/
theorem weaklyConverges_map {ι : Type u} {E : Type v} {F : Type w}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (l : Filter ι) (μs : ι → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (g : E → F) (hg : Continuous g) (hμ : WeaklyConverges l μs μ) :
    WeaklyConverges l (fun i => (μs i).map g) (μ.map g) := by
  apply (weaklyConverges_iff_integrals l _ _).mpr
  intro f
  have transfer (η : ProbabilityMeasure E) :
      (∫ y, f y ∂(η.map g : Measure F)) = ∫ x, f (g x) ∂(η : Measure E) :=
    probabilityLaw_integral (η : Measure E) g hg.measurable f
  simpa only [transfer, compContinuous_apply, ContinuousMap.coe_mk] using
    (weaklyConverges_iff_integrals l μs μ).mp hμ (f.compContinuous ⟨g, hg⟩)

/-- The continuous mapping assertion for random variables, including variables
defined on different probability spaces at every index and at the limit. -/
theorem convergesInLaw_continuous
    {ι : Type u} {Ω : Type v} {Ωs : ι → Type w} {E : Type z} {F : Type t}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Ωs i)]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (l : Filter ι) (Ps : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (Ps i)]
    (Xs : ∀ i, Ωs i → E) (hXs : ∀ i, Measurable (Xs i))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : Measurable X)
    (g : E → F) (hg : Continuous g) (h : ConvergesInLaw l Ps Xs hXs P X hX) :
    ConvergesInLaw l Ps (fun i => g ∘ Xs i)
      (fun i => hg.measurable.comp (hXs i)) P (g ∘ X) (hg.measurable.comp hX) := by
  apply (convergesInLaw_iff_expectations l Ps _ _ P _ _).mpr
  intro f
  simpa only [compContinuous_apply, ContinuousMap.coe_mk, Function.comp_apply] using
    (convergesInLaw_iff_expectations l Ps Xs hXs P X hX).mp h
      (f.compContinuous ⟨g, hg⟩)

end
end ProbabilityFoundations.Ch06
