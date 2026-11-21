import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.TopologyComparison

/-! Example d10:13:strict-comparisons. Natural indices are shifted by one,
so index n represents the paper's positive integer n+1. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D10Topology.Ch13.StrictComparisons
abbrev Interval := Set.Icc (0 : ℝ) 1

def powers (n : ℕ) (x : Interval) : ℝ := (x : ℝ) ^ (n + 1)
def powerLimit (x : Interval) : ℝ := if (x : ℝ) = 1 then 1 else 0
def tents (n : ℕ) (x : Interval) : ℝ := max 0 (1 - |(n + 1 : ℝ) * x - 1|)
def dilations (n : ℕ) (x : ℝ) : ℝ := x / (n + 1 : ℝ)

def powersType := ℕ → Interval → ℝ
def powerLimitType := Interval → ℝ
def dilationsType := ℕ → ℝ → ℝ

def power_example : Prop :=
  (∀ n, Continuous (powers n)) ∧
  (∀ x, Tendsto (fun n => powers n x) atTop (𝓝 (powerLimit x))) ∧
  ¬ Continuous powerLimit ∧ ¬ TendstoUniformly powers powerLimit atTop

def tent_example : Prop :=
  (∀ n, Continuous (tents n)) ∧
  Continuous (fun _ : Interval => (0 : ℝ)) ∧
  (∀ x, Tendsto (fun n => tents n x) atTop (𝓝 0)) ∧
  (∀ (n : ℕ) (x : Interval), (x : ℝ) = 1 / (n + 1 : ℝ) → tents n x = 1) ∧
  ¬ TendstoUniformly tents (fun _ => 0) atTop ∧
  ¬ Tendsto tents atTop
    (@nhds (Interval → ℝ) FunctionTopologies.compactConvergenceTopology (fun _ => 0))

def dilation_example : Prop :=
  (∀ n, Continuous (dilations n)) ∧
  (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn dilations (fun _ => 0) atTop K) ∧
  ¬ TendstoUniformly dilations (fun _ => 0) atTop ∧
  (∀ n : ℕ, (⨆ x : ℝ, min 1 (|x| / (n + 1 : ℝ))) = 1)

def strict_continuous_topologies : Prop :=
  FunctionTopologies.compactConvergenceContinuousTopology (X := Interval) (Y := ℝ) <
    FunctionTopologies.pointwiseContinuousTopology ∧
  FunctionTopologies.uniformContinuousTopology (X := ℝ) (Y := ℝ) <
    FunctionTopologies.compactConvergenceContinuousTopology
end Specs.D10Topology.Ch13.StrictComparisons
