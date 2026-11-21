import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.LawsAndTransfer
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
Independent specification of the introductory conventions of Chapter 6
(paper.tex, lines 1418–1427), also applicable to the Borel topological spaces
of the fixed continuous mapping theorem (lines 1567–1590).

`BorelSpace S` requires the given sigma algebra to equal `borel S`, rather
than merely to contain the open sets. No metric, separation, countability,
tightness, or completeness hypothesis is imposed. All laws below are canonical
`ProbabilityMeasure`s, and all tests are bounded continuous real functions.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction

namespace Specs.ProbabilityFoundations.Ch06.WeakFramework

universe u v w z

noncomputable section

def weakTopologyType := ∀ {S : Type u} [TopologicalSpace S] [MeasurableSpace S]
  [BorelSpace S], TopologicalSpace (ProbabilityMeasure S)

def weakTopologyValue : weakTopologyType :=
  fun {S} _ _ _ => ⨅ f : S →ᵇ ℝ, TopologicalSpace.induced
    (fun μ : ProbabilityMeasure S => ∫ s, f s ∂(μ : Measure S)) inferInstance

def weaklyConvergesType := ∀ {ι : Type u} {S : Type v}
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S],
  Filter ι → (ι → ProbabilityMeasure S) → ProbabilityMeasure S → Prop

def weaklyConvergesValue : weaklyConvergesType :=
  fun l μ ν => Tendsto μ l (𝓝 ν)

def probabilityLawType := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
  (X : Ω → S), Measurable X → ProbabilityMeasure S

def probabilityLawValue : probabilityLawType := fun P _ X hX =>
  ⟨Measure.map X P, (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance⟩

def convergesInLawType := ∀ {ι : Type u} {Ω : Type v} {Ωs : ι → Type w} {S : Type z}
  [MeasurableSpace Ω] [∀ i, MeasurableSpace (Ωs i)]
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  (l : Filter ι) (Ps : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (Ps i)]
  (Xs : ∀ i, Ωs i → S) (hXs : ∀ i, Measurable (Xs i))
  (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S), Measurable X → Prop

def convergesInLawValue : convergesInLawType := fun l Ps _ Xs hXs P _ X hX =>
  Tendsto (fun i => probabilityLawValue (Ps i) (Xs i) (hXs i)) l
    (𝓝 (probabilityLawValue P X hX))

def weakTopologyEqType : Prop := ∀ {S : Type u}
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S],
  (⨅ f : S →ᵇ ℝ, TopologicalSpace.induced
    (fun μ : ProbabilityMeasure S => ∫ s, f s ∂(μ : Measure S)) inferInstance) =
    (inferInstance : TopologicalSpace (ProbabilityMeasure S))

def weaklyConvergesIffIntegralsType : Prop := ∀ {ι : Type u} {S : Type v}
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  (l : Filter ι) (μ : ι → ProbabilityMeasure S) (ν : ProbabilityMeasure S),
  Tendsto μ l (𝓝 ν) ↔ ∀ f : S →ᵇ ℝ,
    Tendsto (fun i => ∫ s, f s ∂(μ i : Measure S)) l
      (𝓝 (∫ s, f s ∂(ν : Measure S)))

def probabilityLawToMeasureType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
  (X : Ω → S) (hX : Measurable X),
  (probabilityLawValue P X hX : Measure S) = Measure.map X P

def probabilityLawIntegralType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X)
  (f : S →ᵇ ℝ),
  (∫ s, f s ∂(probabilityLawValue P X hX : Measure S)) = ∫ ω, f (X ω) ∂P

def convergesInLawIffExpectationsType : Prop :=
  ∀ {ι : Type u} {Ω : Type v} {Ωs : ι → Type w} {S : Type z}
  [MeasurableSpace Ω] [∀ i, MeasurableSpace (Ωs i)]
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  (l : Filter ι) (Ps : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (Ps i)]
  (Xs : ∀ i, Ωs i → S) (hXs : ∀ i, Measurable (Xs i))
  (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X),
  convergesInLawValue l Ps Xs hXs P X hX ↔
    ∀ f : S →ᵇ ℝ, Tendsto (fun i => ∫ ω, f (Xs i ω) ∂Ps i) l
      (𝓝 (∫ ω, f (X ω) ∂P))

def lawNonemptyType : Prop := ∀ {S : Type u} [MeasurableSpace S],
  ProbabilityMeasure S → Nonempty S

end
end Specs.ProbabilityFoundations.Ch06.WeakFramework
