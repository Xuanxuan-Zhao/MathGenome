import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! Independent interfaces for the local graph comparison in paper.tex:2574–2580.
The canonical measured objects use the actual iterated integral, with diagonal
zero, on arbitrary metric spaces. No transport or norm estimate is a field of
these definitions. All scalar representatives are allowed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace P102.Trace.MeasuredFractional

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {E : Type*} [NormedAddCommGroup E]
local instance : DecidableEq X := Classical.decEq X

/-- The metric kernel with the stipulated value on the diagonal. -/
def metricKernel (m : ℕ) (s : ℝ) (p : ℝ≥0∞) (z : X × X) : ℝ≥0∞ :=
  if z.1 = z.2 then 0 else
    (ENNReal.ofReal (dist z.1 z.2) ^ ((m : ℝ) + s * p.toReal))⁻¹

/-- The section measure of the singular metric kernel. Its measurability as a
function of the first point is proved from lower semicontinuity and Fatou's
lemma, without a separability assumption. -/
def metricTransition (m : ℕ) (μ : Measure X) (s : ℝ) (p : ℝ≥0∞) :
    ProbabilityTheory.Kernel X X := by
  classical
  exact if h : Measurable (fun x => μ.withDensity (fun y => metricKernel m s p (x, y))) then
    ⟨fun x => μ.withDensity (fun y => metricKernel m s p (x, y)), h⟩
  else 0

/-- Iterated measure weighted by the singular metric kernel. This construction
also works when the Borel metric space is not second countable. -/
def metricPairMeasure (m : ℕ) (μ : Measure X) (s : ℝ) (p : ℝ≥0∞) :
    Measure (X × X) := μ.compProd (metricTransition m μ s p)

def metricIncrement (g : X → E) (z : X × X) : E := g z.1 - g z.2

/-- Extended Lp mass; no implicit finiteness or measurability convention. -/
def lpMass (μ : Measure X) (p : ℝ≥0∞) (g : X → E) : ℝ≥0∞ :=
  ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ

/-- The original iterated integral, including for non-Borel representatives. -/
def metricEnergy (m : ℕ) (μ : Measure X) (s : ℝ) (p : ℝ≥0∞)
    (g : X → E) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, if x = y then 0 else
    ‖g x - g y‖ₑ ^ p.toReal /
      ENNReal.ofReal (dist x y) ^ ((m : ℝ) + s * p.toReal) ∂μ ∂μ

def metricSeminorm (m : ℕ) (μ : Measure X) (s : ℝ) (p : ℝ≥0∞)
    (g : X → E) : ℝ≥0∞ := metricEnergy m μ s p g ^ (1 / p.toReal)

def metricNorm (m : ℕ) (μ : Measure X) (s : ℝ) (p : ℝ≥0∞)
    (g : X → E) : ℝ≥0∞ := eLpNorm g p μ + metricSeminorm m μ s p g

namespace Expected
universe u v

def metricEnergyType := {X : Type u} → [MetricSpace X] → [MeasurableSpace X] →
  {E : Type v} → [NormedAddCommGroup E] →
  ℕ → Measure X → ℝ → ℝ≥0∞ → (X → E) → ℝ≥0∞

def metricEnergyValue : metricEnergyType := by
  classical
  exact fun m μ s p g => ∫⁻ x, ∫⁻ y, if x = y then 0 else
    ‖g x - g y‖ₑ ^ p.toReal /
      ENNReal.ofReal (dist x y) ^ ((m : ℝ) + s * p.toReal) ∂μ ∂μ

def metricSeminormType := {X : Type u} → [MetricSpace X] → [MeasurableSpace X] →
  {E : Type v} → [NormedAddCommGroup E] →
  ℕ → Measure X → ℝ → ℝ≥0∞ → (X → E) → ℝ≥0∞

def metricSeminormValue : metricSeminormType := fun m μ s p g =>
  metricEnergy m μ s p g ^ (1 / p.toReal)

def metricNormType := {X : Type u} → [MetricSpace X] → [MeasurableSpace X] →
  {E : Type v} → [NormedAddCommGroup E] →
  ℕ → Measure X → ℝ → ℝ≥0∞ → (X → E) → ℝ≥0∞

def metricNormValue : metricNormType := fun m μ s p g =>
  eLpNorm g p μ + metricSeminorm m μ s p g

/-- The canonical shared energy has the prescribed full formula. -/
def MetricEnergyDefinition : Prop :=
  @metricEnergy.{u, v} = @metricEnergyValue.{u, v}

/-- The canonical shared seminorm is the prescribed root of the energy. -/
def MetricSeminormDefinition : Prop :=
  @metricSeminorm.{u, v} = @metricSeminormValue.{u, v}

/-- The canonical shared norm is the sum of the two prescribed terms. -/
def MetricNormDefinition : Prop :=
  @metricNorm.{u, v} = @metricNormValue.{u, v}

def EnergyCongr : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X]
    {E : Type v} [NormedAddCommGroup E] (m : ℕ) (μ : Measure X)
    (s : ℝ) (p : ℝ≥0∞) {g h : X → E},
    g =ᵐ[μ] h → metricEnergy m μ s p g = metricEnergy m μ s p h

/-- No joint measurability assumption on the distance kernel or representative:
only the Borel metric structure and a.e. strong measurability are used.
In particular completed representatives qualify. -/
def WeightedIncrementIdentification : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {E : Type v} [NormedAddCommGroup E] (m : ℕ) (μ : Measure X) [SigmaFinite μ]
    (s : ℝ) (p : ℝ≥0∞),
    p ≠ 0 → p ≠ ∞ → ∀ g : X → E, AEStronglyMeasurable g μ →
      eLpNorm (metricIncrement g) p (metricPairMeasure m μ s p) =
        metricSeminorm m μ s p g

def NormTriangle : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {E : Type v} [NormedAddCommGroup E] (m : ℕ) (μ : Measure X) [SigmaFinite μ]
    (s : ℝ) (p : ℝ≥0∞),
    1 ≤ p → p ≠ ∞ → ∀ g h : X → E, MemLp g p μ → MemLp h p μ →
      metricNorm m μ s p (g + h) ≤ metricNorm m μ s p g + metricNorm m μ s p h

def NormFiniteSum : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {E : Type v} [NormedAddCommGroup E] (m : ℕ) (μ : Measure X) [SigmaFinite μ]
    (s : ℝ) (p : ℝ≥0∞),
    1 ≤ p → p ≠ ∞ → ∀ (ι : Type*) (t : Finset ι) (g : ι → X → E),
      (∀ i ∈ t, MemLp (g i) p μ) →
      metricNorm m μ s p (∑ i ∈ t, g i) ≤ ∑ i ∈ t, metricNorm m μ s p (g i)

/-- Definitional specialization to the accepted Euclidean energy. -/
def EuclideanEnergy : Prop :=
  ∀ {d : ℕ} {𝕜 : Type v} [RCLike 𝕜] (G : Set (P102.Fractional.Domain d))
    (s : ℝ) (p : ℝ≥0∞) (g : P102.Fractional.Domain d → 𝕜),
    metricEnergy d (volume.restrict G) s p g = P102.Fractional.energy G s p g

end Expected
end P102.Trace.MeasuredFractional

namespace P102.Trace.GraphFractionalTransport
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open MeasuredFractional

def graphMap {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (γ : Space m → ℝ) : Space m → Ambient m := e ∘ graph γ

def graphMeasure {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (γ : Space m → ℝ) (B : Set (Space m)) : Measure (Ambient m) :=
  (μHE[m] : Measure (Ambient m)).restrict (graphMap e γ '' B)

/-- All quantitative comparisons use one fixed positive finite constant, uniform
in the base ball, frame, graph of Lipschitz constant L, and representative. -/
def Comparison (m : ℕ) (s : ℝ) (p : ℝ≥0∞) (L C : ℝ≥0) : Prop :=
  ∀ (c : Space m) (R : ℝ), 0 < R → ∀ γ : Space m → ℝ,
    LipschitzOnWith L γ (Metric.ball c R) →
    ∀ (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (𝕜 : Type) [RCLike 𝕜]
      (g : Ambient m → 𝕜),
    let μb : Measure (Space m) := volume.restrict (Metric.ball c R)
    let ν := graphMeasure e γ (Metric.ball c R)
    let u := g ∘ graphMap e γ
    (lpMass μb p u ≤ (C : ℝ≥0∞) * lpMass ν p g) ∧
    (lpMass ν p g ≤ (C : ℝ≥0∞) * lpMass μb p u) ∧
    (eLpNorm u p μb ≤ (C : ℝ≥0∞) * eLpNorm g p ν) ∧
    (eLpNorm g p ν ≤ (C : ℝ≥0∞) * eLpNorm u p μb) ∧
    (metricEnergy m μb s p u ≤ (C : ℝ≥0∞) * metricEnergy m ν s p g) ∧
    (metricEnergy m ν s p g ≤ (C : ℝ≥0∞) * metricEnergy m μb s p u) ∧
    (metricSeminorm m μb s p u ≤ (C : ℝ≥0∞) * metricSeminorm m ν s p g) ∧
    (metricSeminorm m ν s p g ≤ (C : ℝ≥0∞) * metricSeminorm m μb s p u) ∧
    (MemLp g p ν ↔ MemLp u p μb)

namespace Expected

def LocalGraphComparison : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (s : ℝ), 0 < s → s < 1 →
    ∀ (p : ℝ≥0∞), 1 ≤ p → p < ∞ → ∀ L : ℝ≥0,
      ∃ C : ℝ≥0, 0 < C ∧ Comparison m s p L C

/-- This statement transports arbitrary almost-everywhere equal representatives
in both directions and also transports a.e. strong measurability. -/
def RepresentativeTransport : Prop :=
  ∀ (m : ℕ) (c : Space m) (R : ℝ), 0 < R → ∀ (γ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L γ (Metric.ball c R) →
    ∀ (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (E : Type*) [NormedAddCommGroup E]
      (g h : Ambient m → E),
    (g =ᵐ[graphMeasure e γ (Metric.ball c R)] h ↔
      g ∘ graphMap e γ =ᵐ[volume.restrict (Metric.ball c R)] h ∘ graphMap e γ) ∧
    (AEStronglyMeasurable g (graphMeasure e γ (Metric.ball c R)) ↔
      AEStronglyMeasurable (g ∘ graphMap e γ) (volume.restrict (Metric.ball c R)))

/-- The actual geometric measure comparison, as inequalities of pushforwards.
It is proved from graph distortion, not postulated as input data. The Borel
extension only changes values off B. -/
def PushforwardComparison : Prop :=
  ∀ (m : ℕ) (B : Set (Space m)), IsOpen B →
    ∀ (γ : Space m → ℝ) (L : ℝ≥0), LipschitzOnWith L γ B →
    ∀ e : Ambient m ≃ᵃⁱ[ℝ] Ambient m,
      ∃ f : Space m → Ambient m, MeasurableEmbedding f ∧ EqOn f (graphMap e γ) B ∧
        Measure.map f (volume.restrict B) ≤ graphMeasure e γ B ∧
        graphMeasure e γ B ≤
          ((graphConstant L : ℝ≥0∞) ^ m) • Measure.map f (volume.restrict B)

end Expected
end P102.Trace.GraphFractionalTransport
