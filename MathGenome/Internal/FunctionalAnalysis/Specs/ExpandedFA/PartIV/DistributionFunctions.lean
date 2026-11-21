import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.LeftRightLim

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV

namespace DistributionFunctionsSpec

/-- Expected type of the distribution of the modulus. -/
def DistributionType :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
    Measure Ω → (Ω → E) → ℝ → ℝ≥0∞

noncomputable def DistributionValue : DistributionType :=
  fun μ f t => μ {x | t < ‖f x‖}

def PrimitiveType := (ℝ → ℝ≥0∞) → ℝ → ℝ≥0∞

noncomputable def PrimitiveValue : PrimitiveType :=
  fun h s => ∫⁻ t in Ioo 0 s, h t

def AntitoneStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) (f : Ω → E), Antitone (DistributionValue μ f)

def RightContinuousStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ t : ℝ,
      ContinuousWithinAt (DistributionValue μ f) (Ici t) t

def LeftLimitStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ t : ℝ,
      Function.leftLim (DistributionValue μ f) t = μ {x | t ≤ ‖f x‖}

def LimitBoundsStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (fs : ℕ → Ω → E),
    Measurable (fun x => ‖f x‖) → (∀ n, Measurable (fun x => ‖fs n x‖)) →
    (∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) →
    ∀ t : ℝ, 0 < t →
      DistributionValue μ f t ≤ liminf (fun n => DistributionValue μ (fs n) t) atTop ∧
      liminf (fun n => DistributionValue μ (fs n) t) atTop ≤
        limsup (fun n => DistributionValue μ (fs n) t) atTop ∧
      limsup (fun n => DistributionValue μ (fs n) t) atTop ≤
        Function.leftLim (DistributionValue μ f) t

def CountableJumpsStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) (f : Ω → E),
    {t : ℝ | ¬ ContinuousAt (DistributionValue μ f) t}.Countable ∧
    {t : ℝ | μ {x | t ≤ ‖f x‖} ≠ DistributionValue μ f t}.Countable

def LevelConvergenceStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (fs : ℕ → Ω → E),
    Measurable (fun x => ‖f x‖) → (∀ n, Measurable (fun x => ‖fs n x‖)) →
    (∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) →
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n => DistributionValue μ (fs n) t) atTop (𝓝 (DistributionValue μ f t))

def LayerCakeStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ h : ℝ → ℝ≥0∞, Measurable h →
      (∫⁻ x, PrimitiveValue h ‖f x‖ ∂μ) =
        ∫⁻ t in Ioi 0, DistributionValue μ f t * h t

def TailStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ h : ℝ → ℝ≥0∞, Measurable h →
    ∀ a : ℝ, 0 ≤ a →
      (∫⁻ x in {x | a < ‖f x‖}, PrimitiveValue h ‖f x‖ ∂μ) =
        DistributionValue μ f a * PrimitiveValue h a +
          ∫⁻ t in Ioi a, DistributionValue μ f t * h t

def PowerDecayStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (q : ℝ), 0 < q →
    MemLp f (ENNReal.ofReal q) μ →
      Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ q) * DistributionValue μ f t)
        atTop (𝓝 0)

end DistributionFunctionsSpec
end ExpandedFA.PartIV
