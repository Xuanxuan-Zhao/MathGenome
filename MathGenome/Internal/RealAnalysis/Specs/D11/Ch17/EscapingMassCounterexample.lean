import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
The source is paper.tex:5300–5309. `LebesgueReal` is the real line with
completed Borel Lebesgue measure, not just its Borel restriction. It is a
measurable-space type tag, with the same points as ℝ. Natural index n represents
the paper's positive integer n+1, so the intervals are exactly [n+1,n+2],
including both endpoints. All control and convergence predicates are the shared
ones. In particular spatial tails quantify over all measurable finite-mass sets.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace Specs.D11.Ch17.EscapingMassCounterexample

abbrev LebesgueReal := NullMeasurableSpace ℝ (volume : Measure ℝ)
abbrev lebesgue : Measure LebesgueReal := (volume : Measure ℝ).completion

def movingInterval (n : ℕ) : Set ℝ :=
  Icc ((n + 1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ) + 1)

def movingIndicator_type := ℕ → LebesgueReal → ℝ
def movingIndicator_value : movingIndicator_type := fun n =>
  (movingInterval n).indicator (fun _ => 1)

open Specs.D11.Ch17.UniformControls Specs.D11.Ch07.ConvergenceDefinitions

def measurable_integrable : Prop :=
  integrableFamily_value lebesgue movingIndicator_value

def integral_on_set : Prop := ∀ (n : ℕ) (A : Set LebesgueReal), MeasurableSet A →
  absoluteIntegral_value lebesgue (movingIndicator_value n) A =
    lebesgue (A ∩ movingInterval n)

def norm_one : Prop := ∀ n : ℕ,
  absoluteIntegral_value lebesgue (movingIndicator_value n) univ = 1

def deviation_measure_one : Prop := ∀ n : ℕ,
  lebesgue (deviationSet_value (movingIndicator_value n) (fun _ => 0) (1/2)) = 1

def small_set_control : Prop := uiSmall_value lebesgue movingIndicator_value

def pointwise_zero : Prop := pointwiseConverges_value movingIndicator_value (fun _ => 0)

def locally_in_measure_zero : Prop :=
  locallyInMeasureConverges_value lebesgue movingIndicator_value (fun _ => 0)

def no_spatial_tails : Prop := ¬ spatialTails_value lebesgue movingIndicator_value

def no_L1_convergence : Prop :=
  ¬ lpConverges_value lebesgue 1 movingIndicator_value (fun _ => 0)

def no_global_in_measure : Prop :=
  ¬ inMeasureConverges_value lebesgue movingIndicator_value (fun _ => 0)

end Specs.D11.Ch17.EscapingMassCounterexample
