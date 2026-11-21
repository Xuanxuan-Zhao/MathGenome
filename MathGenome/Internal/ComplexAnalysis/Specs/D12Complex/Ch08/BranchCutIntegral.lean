import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The ordinary, absolutely convergent integral of paper.tex:2181–2215.
The endpoint assertions concern ordinary one-sided truncated integrals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Specs.D12Complex.Ch08.BranchCutIntegral

def branch_cut_integrable_type : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    IntegrableOn (fun x : ℝ => x ^ (s - 1) / (1 + x)) (Ioi 0)

def branch_cut_integral_type : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    (∫ x : ℝ in Ioi 0, x ^ (s - 1) / (1 + x)) =
      Real.pi / Real.sin (Real.pi * s)

/-- Each improper endpoint exists independently; these are ordinary integrals,
not symmetric principal values. The same limits hold for absolute values. -/
def branch_cut_improper_type : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    Tendsto (fun ε : ℝ => ∫ x in ε..1, x ^ (s - 1) / (1 + x))
      (𝓝[>] 0) (𝓝 (∫ x in Ioc (0 : ℝ) 1, x ^ (s - 1) / (1 + x))) ∧
    Tendsto (fun R : ℝ => ∫ x in (1 : ℝ)..R, x ^ (s - 1) / (1 + x))
      atTop (𝓝 (∫ x in Ioi (1 : ℝ), x ^ (s - 1) / (1 + x))) ∧
    Tendsto (fun ε : ℝ => ∫ x in ε..1, |x ^ (s - 1) / (1 + x)|)
      (𝓝[>] 0) (𝓝 (∫ x in Ioc (0 : ℝ) 1, |x ^ (s - 1) / (1 + x)|)) ∧
    Tendsto (fun R : ℝ => ∫ x in (1 : ℝ)..R, |x ^ (s - 1) / (1 + x)|)
      atTop (𝓝 (∫ x in Ioi (1 : ℝ), |x ^ (s - 1) / (1 + x)|)) ∧
    (∫ x in Ioc (0 : ℝ) 1, x ^ (s - 1) / (1 + x)) +
      (∫ x in Ioi (1 : ℝ), x ^ (s - 1) / (1 + x)) =
        Real.pi / Real.sin (Real.pi * s)

def branch_cut_diverges_zero_type : Prop :=
  Tendsto (fun ε : ℝ => ∫ x in ε..1, x ^ ((0 : ℝ) - 1) / (1 + x))
    (𝓝[>] 0) atTop

def branch_cut_diverges_one_type : Prop :=
  Tendsto (fun R : ℝ => ∫ x in (1 : ℝ)..R, x ^ ((1 : ℝ) - 1) / (1 + x))
    atTop atTop

end Specs.D12Complex.Ch08.BranchCutIntegral
