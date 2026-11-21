import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.LawsAndTransfer
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework

/-!
# Borel probability laws and weak convergence

The conventions of Chapter 6, paper.tex lines 1418–1427. The topology is
identified with Mathlib's canonical topology using all bounded continuous real
tests. These interfaces also apply to arbitrary Borel topological spaces in the
fixed continuous mapping theorem. In metric applications `BorelSpace` enforces
exactly the Borel sigma algebra. Source probability spaces remain arbitrary and
may vary with the index; they need not be complete or coupled to each other.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction

namespace ProbabilityFoundations.Ch06

universe u v w z

noncomputable section

/-- The initial topology of the real integral tests. -/
def weakTopology {S : Type u} [TopologicalSpace S] [MeasurableSpace S]
    [BorelSpace S] : TopologicalSpace (ProbabilityMeasure S) :=
  ⨅ f : S →ᵇ ℝ, TopologicalSpace.induced
    (fun μ : ProbabilityMeasure S => ∫ s, f s ∂(μ : Measure S)) inferInstance

/-- Weak convergence along a filter; sequences use `Filter.atTop`. -/
def WeaklyConverges {ι : Type u} {S : Type v}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (l : Filter ι) (μ : ι → ProbabilityMeasure S) (ν : ProbabilityMeasure S) : Prop :=
  Tendsto μ l (𝓝 ν)

/-- Package the upstream law as a canonical probability measure. -/
def probabilityLaw {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (hX : Measurable X) : ProbabilityMeasure S :=
  ⟨Ch01.law P X, Ch01.law_probability P X hX⟩

/-- Convergence in law allows a separate probability space at every index,
and a separate space for the limiting variable. -/
def ConvergesInLaw {ι : Type u} {Ω : Type v} {Ωs : ι → Type w} {S : Type z}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Ωs i)]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (l : Filter ι) (Ps : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (Ps i)]
    (Xs : ∀ i, Ωs i → S) (hXs : ∀ i, Measurable (Xs i))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X) : Prop :=
  WeaklyConverges l (fun i => probabilityLaw (Ps i) (Xs i) (hXs i))
    (probabilityLaw P X hX)

/-- Mathlib's topology, inherited from finite measures and nonnegative tests,
is precisely the initial topology for all bounded continuous real tests. -/
theorem weakTopology_eq {S : Type u} [TopologicalSpace S] [MeasurableSpace S]
    [BorelSpace S] : weakTopology (S := S) =
      (inferInstance : TopologicalSpace (ProbabilityMeasure S)) := by
  apply le_antisymm
  · apply continuous_id_iff_le.mp
    apply (@ProbabilityMeasure.continuous_iff_forall_continuous_integral
      S _ _ _ (ProbabilityMeasure S) (weakTopology (S := S)) id).mpr
    intro f
    exact continuous_iInf_dom (i := f) continuous_induced_dom
  · apply continuous_id_iff_le.mp
    apply continuous_iInf_rng.mpr
    intro f
    exact continuous_induced_rng.mpr
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f)

/-- No metrizability or separation assumptions are needed for the test criterion. -/
theorem weaklyConverges_iff_integrals {ι : Type u} {S : Type v}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (l : Filter ι) (μ : ι → ProbabilityMeasure S) (ν : ProbabilityMeasure S) :
    WeaklyConverges l μ ν ↔ ∀ f : S →ᵇ ℝ,
      Tendsto (fun i => ∫ s, f s ∂(μ i : Measure S)) l
        (𝓝 (∫ s, f s ∂(ν : Measure S))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto

@[simp] theorem probabilityLaw_toMeasure {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (hX : Measurable X) :
    (probabilityLaw P X hX : Measure S) = Measure.map X P := rfl

/-- The integral tests of a law equal the expectations on its original space. -/
theorem probabilityLaw_integral {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X)
    (f : S →ᵇ ℝ) :
    (∫ s, f s ∂(probabilityLaw P X hX : Measure S)) = ∫ ω, f (X ω) ∂P :=
  Ch01.law_real_integral P X hX f (f.integrable (probabilityLaw P X hX))

/-- The expectation characterization also holds for variables on different spaces. -/
theorem convergesInLaw_iff_expectations
    {ι : Type u} {Ω : Type v} {Ωs : ι → Type w} {S : Type z}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Ωs i)]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (l : Filter ι) (Ps : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (Ps i)]
    (Xs : ∀ i, Ωs i → S) (hXs : ∀ i, Measurable (Xs i))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X) :
    ConvergesInLaw l Ps Xs hXs P X hX ↔
      ∀ f : S →ᵇ ℝ, Tendsto (fun i => ∫ ω, f (Xs i ω) ∂Ps i) l
        (𝓝 (∫ ω, f (X ω) ∂P)) := by
  unfold ConvergesInLaw
  rw [weaklyConverges_iff_integrals]
  simp only [probabilityLaw_integral]

/-- Normalization automatically excludes laws on the empty space. -/
theorem law_nonempty {S : Type u} [MeasurableSpace S]
    (μ : ProbabilityMeasure S) : Nonempty S := μ.nonempty

end
end ProbabilityFoundations.Ch06
