import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition

/-! Centered Euclidean ball averages for finite-valued measurable representatives
(paper.tex:4344–4353). All integrals below are taken in the shared completed
Lebesgue space. Local integrability is tested on every compact set.
The integral constructors use the previously established scalar integral,
with integrability proved before evaluation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch13.AveragesMaximalDefinition
open D11.Ch03
open D11.Ch06

private theorem borel_ball_measurable {n : ℕ} (x : Point n) (r : ℝ) :
    MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet

private theorem borel_compact_measurable {n : ℕ} (K : Set (Point n)) (hK : IsCompact K) :
    MeasurableSet K := hK.measurableSet

private theorem borel_compact_finite {n : ℕ} [NeZero n]
    (K : Set (Point n)) (hK : IsCompact K) : LebesgueMeasures.borelMeasure n K < ∞ := by
  change (volume : Measure (Point n)) K < ∞
  exact hK.measure_lt_top

private theorem borel_ball_positive {n : ℕ} [NeZero n]
    (x : Point n) (r : ℝ) (hr : 0 < r) :
    0 < LebesgueMeasures.borelMeasure n (Metric.ball x r) := by
  change 0 < (volume : Measure (Point n)) (Metric.ball x r)
  exact Metric.measure_ball_pos _ x hr

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := LebesgueMeasures.lebesgueSpace n

variable {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

def locallyIntegrable (f : Point n → 𝕜) : Prop :=
  Measurable f ∧ ∀ K : Set (Point n), IsCompact K →
    ScalarIntegral.scalarIntegrable ((LebesgueMeasures.lebesgue n).restrict K) f

theorem locallyIntegrable_iff (f : Point n → 𝕜) :
    locallyIntegrable f ↔ Measurable f ∧
      ∀ K : Set (Point n), IsCompact K → IntegrableOn f K (LebesgueMeasures.lebesgue n) := by
  constructor
  · rintro ⟨hm, hK⟩
    exact ⟨hm, fun K h => ((ScalarIntegral.scalarIntegrable_iff _ _).mp (hK K h)).2⟩
  · rintro ⟨hm, hK⟩
    exact ⟨hm, fun K h => (ScalarIntegral.scalarIntegrable_iff _ _).mpr ⟨hm, hK K h⟩⟩

/-- Closed or open Euclidean balls are measured in the completed structure. -/
theorem ball_measurable (x : Point n) (r : ℝ) :
    MeasurableSet (Metric.ball x r) :=
  LebesgueMeasures.native_borel_le n _ (borel_ball_measurable x r)

private theorem compact_measure_eq (K : Set (Point n)) (hK : IsCompact K) :
    LebesgueMeasures.lebesgue n K = LebesgueMeasures.borelMeasure n K := by
  exact (LebesgueMeasures.lebesgue_apply n K (LebesgueMeasures.native_borel_le n _ (borel_compact_measurable K hK))).trans
    (LebesgueMeasures.native_outer_agreement n K).symm

/-- The covering construction is finite on Euclidean compact sets. -/
instance lebesgueFiniteOnCompacts : IsFiniteMeasureOnCompacts (LebesgueMeasures.lebesgue n) where
  lt_top_of_isCompact := by
    intro K hK
    rw [compact_measure_eq K hK]
    exact borel_compact_finite K hK

theorem ball_measure (x : Point n) (r : ℝ) (hr : 0 < r) :
    0 < LebesgueMeasures.lebesgue n (Metric.ball x r) ∧
    LebesgueMeasures.lebesgue n (Metric.ball x r) < ∞ ∧
    0 < (LebesgueMeasures.lebesgue n (Metric.ball x r)).toReal := by
  have heq : LebesgueMeasures.lebesgue n (Metric.ball x r) = LebesgueMeasures.borelMeasure n (Metric.ball x r) :=
    (LebesgueMeasures.lebesgue_apply n _ (ball_measurable x r)).trans
      (LebesgueMeasures.native_outer_agreement n _).symm
  have hp : 0 < LebesgueMeasures.lebesgue n (Metric.ball x r) := by
    rw [heq]
    exact borel_ball_positive x r hr
  have ht : LebesgueMeasures.lebesgue n (Metric.ball x r) < ∞ := measure_ball_lt_top
  exact ⟨hp, ht, ENNReal.toReal_pos hp.ne' ht.ne⟩

theorem locallyIntegrable_norm (f : Point n → 𝕜) (hf : locallyIntegrable f) :
    locallyIntegrable (fun y => ‖f y‖) := by
  apply (locallyIntegrable_iff _).mpr
  exact ⟨hf.1.norm, fun K hK => (((locallyIntegrable_iff f).mp hf).2 K hK).norm⟩

theorem locallyIntegrable_sub_const (f : Point n → 𝕜) (hf : locallyIntegrable f) (c : 𝕜) :
    locallyIntegrable (fun y => f y - c) := by
  apply (locallyIntegrable_iff _).mpr
  refine ⟨hf.1.sub measurable_const, fun K hK => ?_⟩
  exact (((locallyIntegrable_iff f).mp hf).2 K hK).sub
    (integrableOn_const (hK.measure_ne_top (μ := LebesgueMeasures.lebesgue n)))

theorem scalarIntegrable_ball (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (x : Point n) (r : ℝ) :
    ScalarIntegral.scalarIntegrable ((LebesgueMeasures.lebesgue n).restrict (Metric.ball x r)) f := by
  apply (ScalarIntegral.scalarIntegrable_iff _ _).mpr
  exact ⟨hf.1, (((locallyIntegrable_iff f).mp hf).2 _
    (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall⟩

def average (f : Point n → 𝕜) (hf : locallyIntegrable f) (r : ℝ) (x : Point n) : 𝕜 :=
  (LebesgueMeasures.lebesgue n (Metric.ball x r)).toReal⁻¹ •
    ScalarIntegral.scalarIntegral ((LebesgueMeasures.lebesgue n).restrict (Metric.ball x r)) f
      (scalarIntegrable_ball f hf x r)

def absoluteAverage (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (x : Point n) : ℝ :=
  average (fun y => ‖f y‖) (locallyIntegrable_norm f hf) r x

def oscillationAverage (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (x : Point n) : ℝ :=
  average (fun y => ‖f y - f x‖)
    (locallyIntegrable_norm _ (locallyIntegrable_sub_const f hf (f x))) r x

/-- The supremum is extended nonnegative, and ranges over all positive real radii. -/
def maximal (f : Point n → 𝕜) (hf : locallyIntegrable f) (x : Point n) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (absoluteAverage f hf r x)

/-- This depends on the value of the chosen representative at `x`. -/
def lebesguePoint (f : Point n → 𝕜) (hf : locallyIntegrable f) (x : Point n) : Prop :=
  Tendsto (fun r => oscillationAverage f hf r x) (𝓝[>] (0 : ℝ)) (𝓝 0)

theorem average_formula (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (x : Point n) :
    average f hf r x = (LebesgueMeasures.lebesgue n (Metric.ball x r)).toReal⁻¹ •
      ∫ y in Metric.ball x r, f y ∂(LebesgueMeasures.lebesgue n) := rfl

theorem absoluteAverage_eq_average (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hn : locallyIntegrable (fun y => ‖f y‖)) (r : ℝ) (x : Point n) :
    absoluteAverage f hf r x = average (fun y => ‖f y‖) hn r x := rfl

theorem oscillationAverage_eq_average (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (x : Point n) (hn : locallyIntegrable (fun y => ‖f y - f x‖)) (r : ℝ) :
    oscillationAverage f hf r x = average (fun y => ‖f y - f x‖) hn r x := rfl

theorem absoluteAverage_nonneg (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (x : Point n) : 0 ≤ absoluteAverage f hf r x := by
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg (fun _ => norm_nonneg _))

theorem maximal_formula (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hn : locallyIntegrable (fun y => ‖f y‖)) (x : Point n) :
    maximal f hf x =
      ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (average (fun y => ‖f y‖) hn r x) := rfl

theorem lebesguePoint_iff (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (x : Point n) (hn : locallyIntegrable (fun y => ‖f y - f x‖)) :
    lebesguePoint f hf x ↔
      Tendsto (fun r => average (fun y => ‖f y - f x‖) hn r x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := Iff.rfl

end D11.Ch13.AveragesMaximalDefinition
