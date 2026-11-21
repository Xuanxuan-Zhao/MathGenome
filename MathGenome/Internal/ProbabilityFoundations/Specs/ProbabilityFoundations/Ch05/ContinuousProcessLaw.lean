import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.DenseEvaluationBorel
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.Modifications
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.LawsAndTransfer

/-! Independent statements for `cor:continuous-path-law`, paper.tex §5.5.
The Borel structure is that of the uniform metric, by the upstream geometry.
The probability spaces retain their specified sigma-algebras. -/
open MeasureTheory Set TopologicalSpace

namespace ProbabilityFoundations.Ch05

/-- A process with everywhere continuous paths, bundled as a path-valued map. -/
def continuousProcessPath {T : ℝ} {Ω S : Type*} [TopologicalSpace S]
    (X : Time T → Ω → S) (hc : ∀ ω, Continuous (fun t => X t ω)) :
    Ω → C(Time T, S) := fun ω => ⟨fun t => X t ω, hc ω⟩

/-- The prescribed extension uses the specified event, with no assertion that
 the entire continuity locus is measurable. -/
noncomputable def constantPathExtension {T : ℝ} {Ω S : Type*} [TopologicalSpace S]
    (X : Time T → Ω → S) (G : Set Ω)
    (hc : ∀ ω ∈ G, Continuous (fun t => X t ω)) (s₀ : S) : Ω → C(Time T, S) := by
  classical
  exact fun ω => if h : ω ∈ G then ⟨fun t => X t ω, hc ω h⟩ else ContinuousMap.const _ s₀

namespace ProcessLawSpec

variable {T : ℝ} {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace S] [Nonempty S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]

def PathMapMeasurable : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (D : Set (Time T)), D.Countable → Dense D →
  ∀ (X : Time T → Ω → S) (hc : ∀ ω, Continuous (fun t => X t ω)),
    (∀ t, Measurable (X t)) → Measurable (continuousProcessPath X hc)

def PathLawMarginals : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (D : Set (Time T)), D.Countable → Dense D →
  ∀ (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Time T → Ω → S) (hc : ∀ ω, Continuous (fun t => X t ω)),
    (∀ t, Measurable (X t)) →
    IsProbabilityMeasure (Measure.map (continuousProcessPath X hc) P) ∧
    ∀ (n : ℕ) (τ : Fin n → Time T),
      Measure.map (fun f : C(Time T, S) => fun i => f (τ i))
        (Measure.map (continuousProcessPath X hc) P) =
      Measure.map (fun ω => fun i => X (τ i) ω) P

/-- Finite sets of dense times suffice; repetitions and order in a finite tuple
carry no additional information. -/
def PathMeasureUnique : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (D : Set (Time T)), D.Countable → Dense D →
  ∀ (μ ν : Measure C(Time T, S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ I : Finset D,
      Measure.map (fun f : C(Time T, S) => fun i : I => f i.1.1) μ =
      Measure.map (fun f : C(Time T, S) => fun i : I => f i.1.1) ν) → μ = ν

/-- This formulation directly accepts finite tuples, on different probability spaces. -/
def ProcessLawUnique : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (D : Set (Time T)), D.Countable → Dense D →
  ∀ (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Ω → C(Time T, S)) (H : Ω' → C(Time T, S)),
    Measurable F → Measurable H →
    (∀ (n : ℕ) (τ : Fin n → D),
      Measure.map (fun ω => fun i => F ω (τ i).1) P =
      Measure.map (fun ω => fun i => H ω (τ i).1) Q) →
    Measure.map F P = Measure.map H Q

/-- All original finite-dimensional laws, at arbitrary times, are preserved. -/
def ConstantExtensionProperties : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (D : Set (Time T)), D.Countable → Dense D →
  ∀ (P : Measure Ω) [IsProbabilityMeasure P] (X : Time T → Ω → S)
    (G : Set Ω) (hG : MeasurableSet G) (hP : P G = 1)
    (hc : ∀ ω ∈ G, Continuous (fun t => X t ω)) (s₀ : S),
    (∀ t, Measurable (X t)) →
    let F := constantPathExtension X G hc s₀
    Measurable F ∧ IsProbabilityMeasure (Measure.map F P) ∧
    (∀ ω ∈ G, ∀ t, F ω t = X t ω) ∧
    (∀ ω ∉ G, ∀ t, F ω t = s₀) ∧
    ModificationsSpec.modificationValue P X (fun t ω => F ω t) ∧
    ∀ (n : ℕ) (τ : Fin n → Time T),
      Measure.map (fun ω => fun i => F ω (τ i)) P =
      Measure.map (fun ω => fun i => X (τ i) ω) P

/-- Uniqueness after extension, comparing the original finite-dimensional laws. -/
def ConstantExtensionUnique : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (D : Set (Time T)), D.Countable → Dense D →
  ∀ (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Time T → Ω → S) (Y : Time T → Ω' → S)
    (G : Set Ω) (K : Set Ω') (hG : MeasurableSet G) (hK : MeasurableSet K)
    (hP : P G = 1) (hQ : Q K = 1)
    (hc : ∀ ω ∈ G, Continuous (fun t => X t ω))
    (hd : ∀ ω ∈ K, Continuous (fun t => Y t ω)) (s₀ s₁ : S),
    (∀ t, Measurable (X t)) → (∀ t, Measurable (Y t)) →
    (∀ (n : ℕ) (τ : Fin n → D),
      Measure.map (fun ω => fun i => X (τ i).1 ω) P =
      Measure.map (fun ω => fun i => Y (τ i).1 ω) Q) →
    Measure.map (constantPathExtension X G hc s₀) P =
    Measure.map (constantPathExtension Y K hd s₁) Q

/-- Closed interfaces used to compare the complete quantified theorem types. -/
def pathMapMeasurableType : Prop :=
  ∀ {Ω S : Type*} [MeasurableSpace Ω] [MetricSpace S] [Nonempty S]
    [SeparableSpace S] [MeasurableSpace S] [BorelSpace S],
    PathMapMeasurable (Ω := Ω) (S := S)

def pathLawMarginalsType : Prop :=
  ∀ {Ω S : Type*} [MeasurableSpace Ω] [MetricSpace S] [Nonempty S]
    [SeparableSpace S] [MeasurableSpace S] [BorelSpace S],
    PathLawMarginals (Ω := Ω) (S := S)

def pathMeasureUniqueType : Prop :=
  ∀ {S : Type*} [MetricSpace S] [Nonempty S]
    [SeparableSpace S] [MeasurableSpace S] [BorelSpace S],
    PathMeasureUnique (S := S)

def processLawUniqueType : Prop :=
  ∀ {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MetricSpace S] [Nonempty S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S],
    ProcessLawUnique (Ω := Ω) (Ω' := Ω') (S := S)

def constantExtensionPropertiesType : Prop :=
  ∀ {Ω S : Type*} [MeasurableSpace Ω] [MetricSpace S] [Nonempty S]
    [SeparableSpace S] [MeasurableSpace S] [BorelSpace S],
    ConstantExtensionProperties (Ω := Ω) (S := S)

def constantExtensionUniqueType : Prop :=
  ∀ {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MetricSpace S] [Nonempty S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S],
    ConstantExtensionUnique (Ω := Ω) (Ω' := Ω') (S := S)

end ProcessLawSpec
end ProbabilityFoundations.Ch05
