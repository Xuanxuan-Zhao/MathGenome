import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.SymmetricInfiniteMeans
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace P207.FiniteStopCounterexample
noncomputable section

/-- The fair nearest-neighbor move law on the integers. -/
def move : PMF ℤ := Walk.integerKernel (1 / 2) (by norm_num) (by norm_num) 0

/-- Independent fair moves, indexed from zero. -/
@[instance_reducible] def law : Measure (ℕ → ℤ) :=
  Measure.infinitePi (fun _ : ℕ => move.toMeasure)

instance : IsProbabilityMeasure law := by unfold law; infer_instance

/-- Integer walk started at zero, realized by its independent moves. -/
def path (ω : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, ω k

def process (n : ℕ) (ω : ℕ → ℤ) : ℝ := (path ω n : ℝ)

theorem measurable_process (n : ℕ) : Measurable (process n) := by
  unfold process path
  fun_prop

/-- Exactly the natural filtration of the real walk. -/
def filtration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℤ)) :=
  P207.naturalFiltration process measurable_process

/-- First entrance at +1, including time zero. -/
def stop (ω : ℕ → ℤ) : WithTop ℕ := Markov.hittingTime {1} (path ω)

/-- Zero is explicitly assigned on the infinite layer. -/
def terminal : (ℕ → ℤ) → ℝ :=
  P207.fullStoppedValue process stop (fun _ => 0)

namespace Spec

/-- The full counterexample, including its canonical whole-path law. -/
def counterexample : Prop :=
  law.map path = Walk.integerLaw (1 / 2) (by norm_num) (by norm_num) 0 ∧
  P207.IsMartingale process filtration law ∧
  (∀ᵐ ω ∂law, ∀ k, |process (k + 1) ω - process k ω| = 1) ∧
  P207.IsDiscreteStoppingTime filtration stop ∧
  (∀ᵐ ω ∂law, stop ω < ⊤) ∧
  (∫⁻ ω, ENat.toENNReal (stop ω) ∂law) = ⊤ ∧
  (∀ ω, process 0 ω = 0) ∧
  (∀ᵐ ω ∂law, terminal ω = 1) ∧
  Integrable terminal law ∧
  (∫ ω, terminal ω ∂law) = 1 ∧
  (∫ ω, process 0 ω ∂law) = 0 ∧
  (∫ ω, terminal ω ∂law) ≠ (∫ ω, process 0 ω ∂law)

end Spec
end
end P207.FiniteStopCounterexample
