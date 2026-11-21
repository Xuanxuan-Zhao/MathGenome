import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statement of `paper.tex`, Lemma `d13:19:maximal-lemma`.
The strict superlevel set of a supremum is represented by an existential
quantifier over positive times. This remains correct when the sums or averages
are unbounded, without using the conditionally complete real `sSup`.
For an arbitrary L¹ representative the sets are null-measurable; for measurable
representatives they are measurable, also on an uncompleted probability space.
The L¹ norm on the right is written explicitly as the integral of the norm. -/
namespace Specs.D13Unified.Ch19.MaximalLemma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
universe u v

def finiteMaximumType := {X : Type u} → (X → X) → (X → ℝ) → ℕ → X → ℝ

/-- The finite maximum of S₀ = 0, S₁, ..., S_N. -/
def finiteMaximum {X : Type u} (T : X → X) (f : X → ℝ) : ℕ → X → ℝ :=
  Nat.rec (fun _ => 0) (fun n m x => max (m x) (MeasureDefinitions.ergodicSum T f (n + 1) x))

def finitePositiveSetType := {X : Type u} → (X → X) → (X → ℝ) → ℕ → Set X

def finitePositiveSet {X : Type u} (T : X → X) (f : X → ℝ) (N : ℕ) : Set X :=
  {x | ∃ k : ℕ, 0 < k ∧ k ≤ N ∧ 0 < MeasureDefinitions.ergodicSum T f k x}

def infinitePositiveSetType := {X : Type u} → (X → X) → (X → ℝ) → Set X

def infinitePositiveSet {X : Type u} (T : X → X) (f : X → ℝ) : Set X :=
  {x | ∃ k : ℕ, 0 < k ∧ 0 < MeasureDefinitions.ergodicSum T f k x}

def maximalAverageSetType := {X : Type u} → {𝕜 : Type v} → [NormedAddCommGroup 𝕜] →
  (X → X) → (X → 𝕜) → ℝ → Set X

def maximalAverageSet {X : Type u} {𝕜 : Type v} [NormedAddCommGroup 𝕜]
    (T : X → X) (h : X → 𝕜) (α : ℝ) : Set X :=
  {x | ∃ n : ℕ, 0 < n ∧ α < MeasureDefinitions.ergodicAverage T (fun y => ‖h y‖) n x}

def finiteMaximum_characterizationStatement : Prop :=
  ∀ {X : Type u} (T : X → X) (f : X → ℝ) (N : ℕ) (x : X),
    0 ≤ finiteMaximum T f N x ∧
    (∀ k : ℕ, k ≤ N → MeasureDefinitions.ergodicSum T f k x ≤ finiteMaximum T f N x) ∧
    (∃ k : ℕ, k ≤ N ∧ finiteMaximum T f N x = MeasureDefinitions.ergodicSum T f k x)

def finiteMaximum_posStatement : Prop :=
  ∀ {X : Type u} (T : X → X) (f : X → ℝ) (N : ℕ),
    finitePositiveSet T f N = {x | 0 < finiteMaximum T f N x}

def finiteRegularityStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    ∀ f : X → ℝ, Integrable f μ → ∀ N : ℕ,
      Integrable (finiteMaximum T f N) μ ∧ NullMeasurableSet (finitePositiveSet T f N) μ

def measurableStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X), Measurable T →
    ∀ f : X → ℝ, Measurable f →
      (∀ N : ℕ, Measurable (finiteMaximum T f N) ∧ MeasurableSet (finitePositiveSet T f N)) ∧
      MeasurableSet (infinitePositiveSet T f)

def finite_maximalStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    ∀ f : X → ℝ, Integrable f μ → ∀ N : ℕ,
      0 ≤ ∫ x in finitePositiveSet T f N, f x ∂μ

/-- The increasing-set passage, including convergence of the restricted integrals. -/
def infinite_passageStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    ∀ f : X → ℝ, Integrable f μ →
      Monotone (finitePositiveSet T f) ∧
      infinitePositiveSet T f = ⋃ N : ℕ, finitePositiveSet T f N ∧
      NullMeasurableSet (infinitePositiveSet T f) μ ∧
      Tendsto (fun N => ∫ x in finitePositiveSet T f N, f x ∂μ) atTop
        (𝓝 (∫ x in infinitePositiveSet T f, f x ∂μ))

def infinite_maximalStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    ∀ f : X → ℝ, Integrable f μ → 0 ≤ ∫ x in infinitePositiveSet T f, f x ∂μ

/-- The algebraic bridge used for both real and complex h. -/
def averageSet_eqStatement : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [NormedAddCommGroup 𝕜]
    (T : X → X) (h : X → 𝕜) (α : ℝ),
    maximalAverageSet T h α = infinitePositiveSet T (fun x => ‖h x‖ - α)

def maximal_inequalityStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ],
    MeasureDefinitions.PreservesMeasure T μ → ∀ h : X → 𝕜, Integrable h μ →
    ∀ α : ℝ, 0 < α → NullMeasurableSet (maximalAverageSet T h α) μ ∧
      μ (maximalAverageSet T h α) ≤ ENNReal.ofReal ((∫ x, ‖h x‖ ∂μ) / α)

end
end Specs.D13Unified.Ch19.MaximalLemma
