import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Independent statements for Slutsky, paper.tex 1680–1697.
The general metric version below includes all finite-dimensional real vectors,
including dimension zero. The source spaces may vary with n and the limit
may live on a separate space. No independence is assumed.
The probability hypothesis uses the product-compatible metric on the target.
For quotients, any Borel function of the numerator may be used at denominator zero.
-/
open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch06.Slutsky
universe u v w z t
noncomputable section

def jointType : Prop :=
  ∀ {S : Type u} {T : Type v}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    [MetricSpace T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    {Ω : Type w} {Ωs : ℕ → Type z}
    [MeasurableSpace Ω] [∀ n, MeasurableSpace (Ωs n)]
    (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (Xs : ∀ n, Ωs n → S) (Ys : ∀ n, Ωs n → T)
    (hXs : ∀ n, Measurable (Xs n)) (hYs : ∀ n, Measurable (Ys n))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X)
    (c : T),
    WeakFramework.convergesInLawValue atTop Ps Xs hXs P X hX →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Ps n {ω | ε < dist (Ys n ω) c})
      atTop (𝓝 0)) →
    WeakFramework.convergesInLawValue atTop Ps
      (fun n ω => (Xs n ω, Ys n ω)) (fun n => (hXs n).prodMk (hYs n))
      P (fun ω => (X ω, c)) (hX.prodMk measurable_const)


/-- The explicit finite-dimensional specialization, also for zero dimensions. -/
def vectorsType : Prop :=
  ∀ (d e : ℕ) {Ω : Type w} {Ωs : ℕ → Type z}
    [MeasurableSpace Ω] [∀ n, MeasurableSpace (Ωs n)]
    (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (Xs : ∀ n, Ωs n → Fin d → ℝ) (Ys : ∀ n, Ωs n → Fin e → ℝ)
    (hXs : ∀ n, Measurable (Xs n)) (hYs : ∀ n, Measurable (Ys n))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin d → ℝ)
    (hX : Measurable X) (c : Fin e → ℝ),
    WeakFramework.convergesInLawValue atTop Ps Xs hXs P X hX →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Ps n {ω | ε < dist (Ys n ω) c})
      atTop (𝓝 0)) →
    WeakFramework.convergesInLawValue atTop Ps
      (fun n ω => (Xs n ω, Ys n ω)) (fun n => (hXs n).prodMk (hYs n))
      P (fun ω => (X ω, c)) (hX.prodMk measurable_const)

def continuousType : Prop :=
  ∀ {S : Type u} {T : Type v}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    [MetricSpace T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    {Ω : Type w} {Ωs : ℕ → Type z}
    [MeasurableSpace Ω] [∀ n, MeasurableSpace (Ωs n)]
    (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (Xs : ∀ n, Ωs n → S) (Ys : ∀ n, Ωs n → T)
    (hXs : ∀ n, Measurable (Xs n)) (hYs : ∀ n, Measurable (Ys n))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X)
    (c : T),
    WeakFramework.convergesInLawValue atTop Ps Xs hXs P X hX →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Ps n {ω | ε < dist (Ys n ω) c})
      atTop (𝓝 0)) →
    ∀ {U : Type t} [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
      (g : S × T → U) (hg : Continuous g),
    WeakFramework.convergesInLawValue atTop Ps
      (fun n ω => g (Xs n ω, Ys n ω))
      (fun n => hg.measurable.comp ((hXs n).prodMk (hYs n)))
      P (fun ω => g (X ω, c)) (hg.measurable.comp (hX.prodMk measurable_const))

def continuousAtSliceType : Prop :=
  ∀ {S : Type u} {T : Type v}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    [MetricSpace T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    {Ω : Type w} {Ωs : ℕ → Type z}
    [MeasurableSpace Ω] [∀ n, MeasurableSpace (Ωs n)]
    (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (Xs : ∀ n, Ωs n → S) (Ys : ∀ n, Ωs n → T)
    (hXs : ∀ n, Measurable (Xs n)) (hYs : ∀ n, Measurable (Ys n))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X)
    (c : T),
    WeakFramework.convergesInLawValue atTop Ps Xs hXs P X hX →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Ps n {ω | ε < dist (Ys n ω) c})
      atTop (𝓝 0)) →
    ∀ {U : Type t} [MetricSpace U] [MeasurableSpace U] [BorelSpace U]
      (g : S × T → U) (hg : Measurable g),
    (∀ x : S, ContinuousAt g (x, c)) →
    WeakFramework.convergesInLawValue atTop Ps
      (fun n ω => g (Xs n ω, Ys n ω))
      (fun n => hg.comp ((hXs n).prodMk (hYs n)))
      P (fun ω => g (X ω, c)) (hg.comp (hX.prodMk measurable_const))

def sumType : Prop :=
  ∀ {Ω : Type w} {Ωs : ℕ → Type z}
    [MeasurableSpace Ω] [∀ n, MeasurableSpace (Ωs n)]
    (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (Xs Ys : ∀ n, Ωs n → ℝ)
    (hXs : ∀ n, Measurable (Xs n)) (hYs : ∀ n, Measurable (Ys n))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (c : ℝ),
    WeakFramework.convergesInLawValue atTop Ps Xs hXs P X hX →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Ps n {ω | ε < dist (Ys n ω) c})
      atTop (𝓝 0)) →
    WeakFramework.convergesInLawValue atTop Ps
      (fun n ω => Xs n ω + Ys n ω) (fun n => (hXs n).add (hYs n))
      P (fun ω => X ω + c) (hX.add measurable_const)

def productType : Prop :=
  ∀ {Ω : Type w} {Ωs : ℕ → Type z}
    [MeasurableSpace Ω] [∀ n, MeasurableSpace (Ωs n)]
    (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (Xs Ys : ∀ n, Ωs n → ℝ)
    (hXs : ∀ n, Measurable (Xs n)) (hYs : ∀ n, Measurable (Ys n))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (c : ℝ),
    WeakFramework.convergesInLawValue atTop Ps Xs hXs P X hX →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Ps n {ω | ε < dist (Ys n ω) c})
      atTop (𝓝 0)) →
    WeakFramework.convergesInLawValue atTop Ps
      (fun n ω => Xs n ω * Ys n ω) (fun n => (hXs n).mul (hYs n))
      P (fun ω => X ω * c) (hX.mul measurable_const)

def quotientType : Prop :=
  ∀ {Ω : Type w} {Ωs : ℕ → Type z}
    [MeasurableSpace Ω] [∀ n, MeasurableSpace (Ωs n)]
    (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (Xs Ys : ∀ n, Ωs n → ℝ)
    (hXs : ∀ n, Measurable (Xs n)) (hYs : ∀ n, Measurable (Ys n))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (c : ℝ),
    WeakFramework.convergesInLawValue atTop Ps Xs hXs P X hX →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Ps n {ω | ε < dist (Ys n ω) c})
      atTop (𝓝 0)) →
    c ≠ 0 → ∀ a : ℝ → ℝ, Measurable a →
    ∃ (hZs : ∀ n, Measurable (fun ω => if Ys n ω = 0 then a (Xs n ω)
        else Xs n ω / Ys n ω)) (hZ : Measurable (fun ω => X ω / c)),
    WeakFramework.convergesInLawValue atTop Ps
      (fun n ω => if Ys n ω = 0 then a (Xs n ω) else Xs n ω / Ys n ω) hZs
      P (fun ω => X ω / c) hZ

end
end Specs.ProbabilityFoundations.Ch06.Slutsky
