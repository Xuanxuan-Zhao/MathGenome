import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Independent specification of paper.tex:4344–4353. `Point n` is the
shared Euclidean space, and the domain sigma-algebra is the shared completed
Lebesgue structure. Functions are finite-valued measurable representatives.
The maximal function takes values in [0,∞], so unbounded suprema are retained.
Radii in the supremum are strictly positive; the limit is the right-hand
neighborhood filter at zero. Average formulas extend to nonpositive radii
by the empty-ball convention, without changing their positive-radius meaning. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Specs.D11.Ch13.AveragesMaximalDefinition
open _root_.D11.Ch03

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value n

variable {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

def locallyIntegrable_type := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], (Point n → 𝕜) → Prop

def locallyIntegrable_value : locallyIntegrable_type := fun {n} _ _ _ _ _ f =>
  Measurable f ∧ ∀ K : Set (Point n), IsCompact K →
    Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
      ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n).restrict K) f

def average_type := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜),
  locallyIntegrable_value f → ℝ → Point n → 𝕜

def average_value : average_type := fun {n} _ _ _ _ _ f _ r x =>
  ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball x r)).toReal⁻¹ •
    ∫ y in Metric.ball x r, f y ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)

def absoluteAverage_type := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜),
  locallyIntegrable_value f → ℝ → Point n → ℝ

def absoluteAverage_value : absoluteAverage_type := fun {n} _ _ _ _ _ f _ r x =>
  ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball x r)).toReal⁻¹ *
    ∫ y in Metric.ball x r, ‖f y‖ ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)

def oscillationAverage_type := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜),
  locallyIntegrable_value f → ℝ → Point n → ℝ

def oscillationAverage_value : oscillationAverage_type := fun {n} _ _ _ _ _ f _ r x =>
  ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball x r)).toReal⁻¹ *
    ∫ y in Metric.ball x r, ‖f y - f x‖ ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)

def maximal_type := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜),
  locallyIntegrable_value f → Point n → ℝ≥0∞

def maximal_value : maximal_type := fun f hf x =>
  ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (absoluteAverage_value f hf r x)

def lebesguePoint_type := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜),
  locallyIntegrable_value f → Point n → Prop

def lebesguePoint_value : lebesguePoint_type := fun f hf x =>
  Tendsto (fun r => oscillationAverage_value f hf r x) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- This is integrability on every compact set, with actual measurability. -/
def locallyIntegrable_iff : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜),
  locallyIntegrable_value f ↔ Measurable f ∧
    ∀ K : Set (Point n), IsCompact K → IntegrableOn f K (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)

def ball_measurable : Prop := ∀ {n : ℕ} [NeZero n], ∀ (x : Point n) (r : ℝ),
  MeasurableSet (Metric.ball x r)

def ball_measure : Prop := ∀ {n : ℕ} [NeZero n], ∀ (x : Point n) (r : ℝ), 0 < r →
  0 < (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball x r) ∧
  (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball x r) < ∞ ∧
  0 < ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball x r)).toReal

def locallyIntegrable_norm : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜),
  locallyIntegrable_value f → locallyIntegrable_value (fun y => ‖f y‖)

def locallyIntegrable_sub_const : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜),
  locallyIntegrable_value f → ∀ c : 𝕜, locallyIntegrable_value (fun y => f y - c)

def scalarIntegrable_ball : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜),
  locallyIntegrable_value f → ∀ (x : Point n) (r : ℝ),
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
    ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n).restrict (Metric.ball x r)) f

def average_formula : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜)
  (hf : locallyIntegrable_value f) (r : ℝ) (x : Point n),
  average_value f hf r x = ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball x r)).toReal⁻¹ •
    ∫ y in Metric.ball x r, f y ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)

def absoluteAverage_eq_average : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜)
  (hf : locallyIntegrable_value f)
  (hn : locallyIntegrable_value (fun y => ‖f y‖)) (r : ℝ) (x : Point n),
  absoluteAverage_value f hf r x = average_value (fun y => ‖f y‖) hn r x

def oscillationAverage_eq_average : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜)
  (hf : locallyIntegrable_value f) (x : Point n)
  (hn : locallyIntegrable_value (fun y => ‖f y - f x‖)) (r : ℝ),
  oscillationAverage_value f hf r x = average_value (fun y => ‖f y - f x‖) hn r x

def absoluteAverage_nonneg : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜)
  (hf : locallyIntegrable_value f) (r : ℝ) (x : Point n),
  0 ≤ absoluteAverage_value f hf r x

def maximal_formula : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜)
  (hf : locallyIntegrable_value f)
  (hn : locallyIntegrable_value (fun y => ‖f y‖)) (x : Point n),
  maximal_value f hf x =
    ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (average_value (fun y => ‖f y‖) hn r x)

def lebesguePoint_iff : Prop := ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ∀ (f : Point n → 𝕜)
  (hf : locallyIntegrable_value f) (x : Point n)
  (hn : locallyIntegrable_value (fun y => ‖f y - f x‖)),
  lebesguePoint_value f hf x ↔
    Tendsto (fun r => average_value (fun y => ‖f y - f x‖) hn r x)
      (𝓝[>] (0 : ℝ)) (𝓝 0)

end Specs.D11.Ch13.AveragesMaximalDefinition
