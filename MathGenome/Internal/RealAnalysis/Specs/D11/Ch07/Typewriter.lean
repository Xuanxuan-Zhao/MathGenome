import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Data.Nat.Log

/-! The typewriter example, paper.tex:2436–2451.
The domain is the actual half-open interval, with the ordinary completion
of its restricted real Lebesgue measure. The scalar codomain retains its
Borel structure. Index zero is assigned zero; the paper starts at index one.
`Nat.log 2 n` decodes the unique block containing a positive index.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace Specs.D11.Ch07.Typewriter

abbrev Interval := {x : ℝ // x ∈ Ico (0 : ℝ) 1}
def intervalMeasure : Measure Interval := Measure.comap Subtype.val volume
abbrev Domain := NullMeasurableSpace Interval intervalMeasure
def μ : Measure Domain := intervalMeasure.completion

def coordinate (x : Domain) : ℝ := (show Interval from x).val

def cell (k j : ℕ) : Set Domain :=
  {x | coordinate x ∈ Ico ((j : ℝ) / (2 : ℝ)^k) (((j : ℝ) + 1) / (2 : ℝ)^k)}

def sequence_type := ℕ → Domain → ℝ
def sequence_value : sequence_type := fun n =>
  if n = 0 then 0 else
    (cell (Nat.log 2 n) (n - 2^(Nat.log 2 n))).indicator (fun _ => 1)

def indexing : Prop := ∀ k j : ℕ, j < 2^k →
  sequence_value (2^k+j) = (cell k j).indicator (fun _ => 1)

def measurable_sequence : Prop := ∀ n, Measurable (sequence_value n)

def block_power_integral : Prop := ∀ (p : ℝ), 1 ≤ p → ∀ k j : ℕ, j < 2^k →
  ConvergenceDefinitions.powerIntegral_value μ p (sequence_value (2^k+j)) =
    ENNReal.ofReal ((2 : ℝ)^k)⁻¹

def lp_convergence : Prop := ∀ (p : ℝ), 1 ≤ p →
  ConvergenceDefinitions.lpConverges_value μ p sequence_value (fun _ => 0)

def measure_convergence : Prop :=
  ConvergenceDefinitions.inMeasureConverges_value μ sequence_value (fun _ => 0)

def infinitely_one : Prop := ∀ x : Domain, ∀ N : ℕ,
  ∃ n ≥ N, sequence_value n x = 1

def infinitely_zero : Prop := ∀ x : Domain, ∀ N : ℕ,
  ∃ n ≥ N, sequence_value n x = 0

def nowhere_convergent : Prop := ∀ x : Domain, ¬ ∃ c : ℝ,
  Tendsto (fun n => sequence_value n x) atTop (𝓝 c)

end Specs.D11.Ch07.Typewriter
