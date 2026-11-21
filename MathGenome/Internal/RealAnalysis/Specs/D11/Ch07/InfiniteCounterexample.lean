import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! The moving-interval example in paper.tex:2451–2468.
The domain is the real line with the completion of Borel Lebesgue measure.
`NullMeasurableSpace` is Mathlib's type tag for precisely that sigma-algebra;
it has the same points as `ℝ`. In particular the local assertion quantifies
over all Lebesgue-measurable finite-measure sets, not just Borel sets. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace D11.Ch07.InfiniteCounterexample

def movingInterval (n : ℕ) : Set ℝ := Ico (n : ℝ) ((n : ℝ) + 1)

def movingIndicator {𝕜 : Type} [RCLike 𝕜] (n : ℕ) : ℝ → 𝕜 :=
  (movingInterval n).indicator (fun _ => 1)

end D11.Ch07.InfiniteCounterexample

namespace Specs.D11.Ch07.InfiniteCounterexample

open _root_.D11.Ch07.InfiniteCounterexample
open Specs.D11.Ch07.ConvergenceDefinitions

local notation "mL" => (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ volume))
local notation "μL" => Measure.completion (volume : Measure ℝ)

def measurable_sequence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜],
    ∀ n, @Measurable ℝ 𝕜 mL _ (movingIndicator n)

def pointwise_convergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    pointwiseConverges_value (movingIndicator (𝕜 := 𝕜)) (fun _ => 0)

def local_convergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    @locallyInMeasureConverges_value ℝ 𝕜 _ mL μL movingIndicator (fun _ => 0)

def half_deviation_measure : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜], ∀ n,
    μL (@deviationSet_value ℝ 𝕜 _ (movingIndicator n) (fun _ => 0) (1 / 2)) = 1

def no_global_convergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    ¬ @inMeasureConverges_value ℝ 𝕜 _ mL μL movingIndicator (fun _ => 0)

def no_almost_uniform_convergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    ¬ @almostUniformConverges_value ℝ 𝕜 _ mL μL movingIndicator (fun _ => 0)

def infinite_mass : Prop := μL Set.univ = ∞

end Specs.D11.Ch07.InfiniteCounterexample
