import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent interface for the first paragraph of the proof of
`K03.15.cantor_function`, paper.tex:3630–3644. All functions below have
ambient domain ℝ, but every assertion is on [0,1]. Values outside that
interval are immaterial. Iteration starts at zero, exactly as in the paper.
The limit is the canonical pointwise `limUnder`; no existence or regularity
is assumed in this definition. -/
namespace Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit

open Set Filter
open scoped Topology

noncomputable def step (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 1/3 then h (3*x)/2 else
    if x ≤ 2/3 then 1/2 else 1/2 + h (3*x-2)/2

noncomputable def iterate : ℕ → ℝ → ℝ
  | 0 => id
  | n+1 => step (iterate n)

noncomputable def limit (x : ℝ) : ℝ := limUnder atTop (fun n => iterate n x)

noncomputable def supDistance (h g : ℝ → ℝ) : ℝ :=
  sSup ((fun x => |h x - g x|) '' Icc (0 : ℝ) 1)

def stepType := (ℝ → ℝ) → ℝ → ℝ
noncomputable def stepValue : stepType := step
def iterateType := ℕ → ℝ → ℝ
noncomputable def iterateValue : iterateType := iterate
def limitType := ℝ → ℝ
noncomputable def limitValue : limitType := limit
def supDistanceType := (ℝ → ℝ) → (ℝ → ℝ) → ℝ
noncomputable def supDistanceValue : supDistanceType := supDistance

def stepPreserves : Prop := ∀ h : ℝ → ℝ,
  ContinuousOn h (Icc 0 1) → h 0 = 0 → h 1 = 1 →
  ContinuousOn (step h) (Icc 0 1) ∧ step h 0 = 0 ∧ step h 1 = 1 ∧
    (MonotoneOn h (Icc 0 1) → MonotoneOn (step h) (Icc 0 1))

def stepContraction : Prop := ∀ h g : ℝ → ℝ,
  ContinuousOn h (Icc 0 1) → h 0 = 0 → h 1 = 1 →
  ContinuousOn g (Icc 0 1) → g 0 = 0 → g 1 = 1 →
  supDistance (step h) (step g) ≤ (1/2) * supDistance h g

def iterateEquations : Prop :=
  iterate 0 = id ∧ ∀ n, iterate (n+1) = step (iterate n)

def iterateProperties : Prop := ∀ n,
  ContinuousOn (iterate n) (Icc 0 1) ∧ iterate n 0 = 0 ∧ iterate n 1 = 1 ∧
  MonotoneOn (iterate n) (Icc 0 1)

def geometricIncrement : Prop := ∀ n,
  supDistance (iterate (n+1)) (iterate n) ≤
    (1/2 : ℝ)^n * supDistance (iterate 1) (iterate 0)

def uniformConvergence : Prop :=
  Ch12.Uniform.realUniformConvergesValue
    (fun n (x : Icc (0 : ℝ) 1) => iterate n x)
    (fun x => limit x)

def limitProperties : Prop :=
  ContinuousOn limit (Icc 0 1) ∧ MonotoneOn limit (Icc 0 1) ∧
  limit 0 = 0 ∧ limit 1 = 1 ∧ MapsTo limit (Icc 0 1) (Icc 0 1)

def fixedPoint : Prop := ∀ x ∈ Icc (0 : ℝ) 1, limit x = step limit x

end Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit
