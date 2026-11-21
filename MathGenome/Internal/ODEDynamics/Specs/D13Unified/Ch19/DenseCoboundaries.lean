import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.CompositionIsometry
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Independent statement of paper.tex, Lemma `d13:19:dense-coboundaries`.
All functions and spaces are real. Boundedness and invariance are a.e.; the
quantitative conclusion uses one full-measure set for every positive time. -/
namespace Specs.D13Unified.Ch19.DenseCoboundaries
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
universe u

def truncateType := {X : Type u} → (X → ℝ) → ℕ → X → ℝ

def boundedCoboundariesType := {X : Type u} → [MeasurableSpace X] →
  (p : ℝ≥0∞) → [Fact (1 ≤ p)] → (T : X → X) → (μ : Measure X) →
  MeasureDefinitions.PreservesMeasure T μ → Set (Lp ℝ p μ)

/-- Symmetric real truncation at height n. -/
def truncate {X : Type u} (f : X → ℝ) (n : ℕ) : X → ℝ :=
  fun x => max (-(n : ℝ)) (min (n : ℝ) (f x))

/-- The same class in L¹ or L², retaining bounded representatives for both
components and using the actual composition isometry. -/
def boundedCoboundaries {X : Type u} [MeasurableSpace X] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (T : X → X) (μ : Measure X)
    (hT : MeasureDefinitions.PreservesMeasure T μ) : Set (Lp ℝ p μ) :=
  {d | ∃ v g : Lp ℝ p μ, MemLp v ∞ μ ∧ MemLp g ∞ μ ∧
    (v : X → ℝ) ∘ T =ᵐ[μ] v ∧
    d = v + (g - CompositionIsometry.composition ℝ p T μ hT g)}

def truncationStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → ℝ), MemLp f 2 μ →
    (∀ n, MemLp (truncate f n) ∞ μ) ∧
    Tendsto (fun n => eLpNorm (truncate f n - f) 2 μ) atTop (𝓝 0) ∧
    ((f ∘ T =ᵐ[μ] f) → ∀ n, truncate f n ∘ T =ᵐ[μ] truncate f n)

def densityStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ] (hT : MeasureDefinitions.PreservesMeasure T μ),
    Dense (boundedCoboundaries 2 T μ hT) ∧ Dense (boundedCoboundaries 1 T μ hT)

/-- For every representation d=v+(I-U)g, convergence is to that v. The
pointwise statement refers to the canonical representatives and averages;
the separate norm statement is convergence in the actual L¹ space. -/
def convergenceStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ] (hT : MeasureDefinitions.PreservesMeasure T μ)
    (v g : Lp ℝ 1 μ), MemLp v ∞ μ → MemLp g ∞ μ →
    (v : X → ℝ) ∘ T =ᵐ[μ] v →
    let d := v + (g - CompositionIsometry.composition ℝ 1 T μ hT g)
    (∀ᵐ x ∂μ, (∀ n : ℕ, 0 < n →
      MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x =
        v x + (g x - g (T^[n] x)) / (n : ℝ)) ∧
      (∀ n : ℕ, 0 < n →
        |MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x - v x| ≤
          2 * (eLpNorm g ∞ μ).toReal / (n : ℝ)) ∧
      Tendsto (fun n => MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x)
        atTop (𝓝 (v x))) ∧
    Tendsto (fun n => CompositionIsometry.average ℝ 1 T μ hT n d) atTop (𝓝 v)
end
end Specs.D13Unified.Ch19.DenseCoboundaries
