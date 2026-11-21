import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.VitaliHahnSaksUniformity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.MeasureTheory.Measure.Sum

/-! Independent statements for the full finite-control-measure Vitali--Hahn--Saks
 theorem, paper.tex:9734--9814. Weak convergence in the compact application is
 convergence against every continuous linear functional on the norm dual of
 `C₀(K, 𝕜) = C(K, 𝕜)`. The displayed representation equalities identify the
 given native scalar measures with this dual; the pairing has no conjugation. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal ZeroAtInfty
universe u

namespace Specs.ExpandedFA.Compactness.VitaliHahnSaks

open _root_.ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec

/-- Uniform absolute continuity of the genuine total variations. -/
def UniformVariation {α : Type u} [MeasurableSpace α] {𝕜 : Type*} [RCLike 𝕜]
    (ρ : Measure α) (μ : ℕ → VectorMeasure α 𝕜) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
    ρ s < ENNReal.ofReal δ → (⨆ n, (μ n).variation s) < ENNReal.ofReal ε

/-- Existence and uniqueness of the finite countably additive setwise limit,
 with its original null-set absolute continuity. -/
def LimitConclusion {α : Type u} [MeasurableSpace α] {𝕜 : Type*} [RCLike 𝕜]
    (ρ : Measure α) (μ : ℕ → VectorMeasure α 𝕜) : Prop :=
  ∃! ν : VectorMeasure α 𝕜, IsFiniteMeasure ν.variation ∧
    (∀ s, MeasurableSet s → Tendsto (fun n => μ n s) atTop (𝓝 (ν s))) ∧
    (∀ s, MeasurableSet s → ρ s = 0 → ν s = 0)

def SignedTheorem : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ρ : Measure α) [IsFiniteMeasure ρ]
    (μ : ℕ → SignedMeasure α),
    (∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0) →
    (∀ s, MeasurableSet s → ∃ l : ℝ, Tendsto (fun n => μ n s) atTop (𝓝 l)) →
    UniformVariation ρ μ ∧ LimitConclusion ρ μ

def ComplexTheorem : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ρ : Measure α) [IsFiniteMeasure ρ]
    (μ : ℕ → ComplexMeasure α),
    (∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0) →
    (∀ s, MeasurableSet s → ∃ l : ℂ, Tendsto (fun n => μ n s) atTop (𝓝 l)) →
    UniformVariation ρ μ ∧ LimitConclusion ρ μ

/-- The manuscript's geometric control measure, indexed from zero.
 `variation.real univ` is the total variation norm. -/
noncomputable def controlMeasure {X : Type u} [MeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (μ : ℕ → VectorMeasure X 𝕜) : Measure X :=
  Measure.sum fun n => ENNReal.ofReal ((1 / 2 : ℝ)^n /
    (1 + (μ n).variation.real univ)) • (μ n).variation

def ControlMeasureTheorem (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ℕ → VectorMeasure X 𝕜),
    (∀ n, FiniteScalarRadon (μ n)) →
    IsFiniteMeasure (controlMeasure μ) ∧
    _root_.ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon
      (controlMeasure μ) ∧
    (∀ n, (μ n).variation ≪ controlMeasure μ)

/-- Weak convergence of regular scalar measures under the Riesz--Markov
 identification with the norm dual of `C₀`. The witnesses are the ordinary
 multiplication-integral functionals; the implementation proves they exist
 for every finite Radon measure and are unique. The tests are all members
 of the dual of that norm dual. -/
def MeasureWeakConverges {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    {𝕜 : Type} [RCLike 𝕜] (μ : ℕ → VectorMeasure X 𝕜)
    (ν : VectorMeasure X 𝕜) : Prop :=
  ∃ (L : ℕ → (C₀(X, 𝕜) →L[𝕜] 𝕜)) (L₀ : C₀(X, 𝕜) →L[𝕜] 𝕜),
    (∀ n f, L n f = scalarIntegral (μ n) f) ∧
    (∀ f, L₀ f = scalarIntegral ν f) ∧
    (∀ T : (C₀(X, 𝕜) →L[𝕜] 𝕜) →L[𝕜] 𝕜,
      Tendsto (fun n => T (L n)) atTop (𝓝 (T L₀)))

/-- The weak-convergence application has native finite Radon measures as its
 objects; it assumes no separate convergence of their set evaluations. -/
def WeakApplication (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → VectorMeasure X 𝕜) (ν : VectorMeasure X 𝕜),
    (∀ n, FiniteScalarRadon (μ n)) → FiniteScalarRadon ν →
    MeasureWeakConverges μ ν →
    (∀ s, MeasurableSet s → Tendsto (fun n => μ n s) atTop (𝓝 (ν s))) ∧
    UniformVariation (controlMeasure μ) μ ∧
    (∀ s, MeasurableSet s → controlMeasure μ s = 0 → ν s = 0)

/-- Set evaluation, with its bound one, on the full norm dual. -/
def SetEvaluation (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (s : Set X), MeasurableSet s →
    ∃ T : (C₀(X, 𝕜) →L[𝕜] 𝕜) →L[𝕜] 𝕜, (∀ L, ‖T L‖ ≤ ‖L‖) ∧
      ∀ (μ : VectorMeasure X 𝕜), FiniteScalarRadon μ →
        ∀ L : C₀(X, 𝕜) →L[𝕜] 𝕜,
          (∀ f, L f = scalarIntegral μ f) → T L = μ s

def ControlMeasures : Prop := ∀ (𝕜 : Type) [RCLike 𝕜], ControlMeasureTheorem.{u} 𝕜

def SignedWeakApplication : Prop := WeakApplication.{u} ℝ

def ComplexWeakApplication : Prop := WeakApplication.{u} ℂ

def SignedSetEvaluation : Prop := SetEvaluation.{u} ℝ

def ComplexSetEvaluation : Prop := SetEvaluation.{u} ℂ

end Specs.ExpandedFA.Compactness.VitaliHahnSaks
