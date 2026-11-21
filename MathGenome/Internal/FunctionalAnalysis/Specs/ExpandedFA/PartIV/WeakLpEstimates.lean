import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WeakLpBanach
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Set
open scoped ENNReal

namespace ExpandedFA.PartIV.WeakLpEstimatesSpec

/-- The strong Lp norm controls the Banach weak-Lp norm, with constant one. -/
def StrongToWeakStatement : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ), 1 < p →
  ∀ f : Ω → E, AEStronglyMeasurable f μ →
    weakLpN μ p f ≤ eLpNorm f (ENNReal.ofReal p) μ

/-- Comparison of the two Banach weak norms on a finite measure space. -/
def WeakExponentStatement : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (p q : ℝ), 1 < q → q ≤ p →
  ∀ f : Ω → E,
    weakLpN μ q f ≤ (μ univ) ^ (1 / q - 1 / p) * weakLpN μ p f

/-- The sharp finite-measure weak-to-strong estimate; infinite values are allowed. -/
def WeakToStrongStatement : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (p q : ℝ), 1 ≤ q → q < p →
  ∀ f : Ω → E, AEStronglyMeasurable f μ →
    eLpNorm f (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((p / (p - q)) ^ (1 / q)) *
        (μ univ) ^ (1 / q - 1 / p) * weakLpQ μ p f

/-- A constant depending only on the three exponents works uniformly in the
finite measure space and in the real or complex scalar function. -/
def InterpolationStatement : Prop :=
  ∀ p q r : ℝ, 1 < q → q < p → p < r →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E],
    ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (θ : ℝ),
      1 / p = θ / q + (1 - θ) / r →
    ∀ f : Ω → E, AEStronglyMeasurable f μ →
      eLpNorm f (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * weakLpN μ q f ^ θ * weakLpN μ r f ^ (1 - θ)

/-- The original radial witness on the Euclidean unit ball. Real powers use
Lean's total convention at the origin, a null singleton for positive dimension. -/
noncomputable def radialWitness {𝕜 : Type} [RCLike 𝕜] (d : ℕ) (p : ℝ) :
    EuclideanSpace ℝ (Fin d) → 𝕜 :=
  fun x => ((‖x‖ ^ (-(d : ℝ) / p) : ℝ) : 𝕜)

/-- Strong Lp embeds in weak Lp, and the displayed radial function witnesses
strictness on every positive-dimensional Euclidean unit ball. -/
def StrictInclusionStatement : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (d : ℕ), 0 < d → ∀ p : ℝ, 1 < p →
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (Metric.ball 0 1)
  let w : EuclideanSpace ℝ (Fin d) → 𝕜 := radialWitness d p
  (∀ f : EuclideanSpace ℝ (Fin d) → 𝕜,
    MemLp f (ENNReal.ofReal p) μ → weakLpN μ p f < ∞) ∧
  AEStronglyMeasurable w μ ∧
  weakLpQ μ p w < ∞ ∧
  weakLpN μ p w < ∞ ∧
  ¬ MemLp w (ENNReal.ofReal p) μ

/-- The zero-measure and zero-quasi-norm cases are included explicitly. -/
def ZeroCasesStatement : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E],
  (∀ (f : Ω → E) (p : ℝ), 0 < p →
    weakLpQ (0 : Measure Ω) p f = 0 ∧ weakLpN (0 : Measure Ω) p f = 0 ∧
      eLpNorm f (ENNReal.ofReal p) (0 : Measure Ω) = 0) ∧
  (∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (p : ℝ), 1 < p →
    AEStronglyMeasurable f μ → weakLpQ μ p f = 0 →
      f =ᵐ[μ] 0 ∧ ∀ q : ℝ, 0 < q → eLpNorm f (ENNReal.ofReal q) μ = 0)

end ExpandedFA.PartIV.WeakLpEstimatesSpec
