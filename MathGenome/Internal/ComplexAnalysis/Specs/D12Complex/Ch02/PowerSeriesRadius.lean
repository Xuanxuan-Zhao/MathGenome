import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements for the convergence portion of paper.tex, D12.02.01.
The radius is an extended nonnegative real, with no positivity or finiteness
hypothesis. No assertion is made on its boundary. -/

open Filter
open scoped Topology NNReal ENNReal

namespace D12Complex

/-- The extended limsup of the nth roots of the coefficient norms.
At n = 0 the exponent is 0 by the field division convention; this one
term does not affect the limsup at infinity. -/
noncomputable def powerSeriesRootLimsup (c : ℕ → ℂ) : ℝ≥0∞ :=
  limsup (fun n => ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop

/-- Cauchy--Hadamard radius; extended inversion includes 0⁻¹ = ∞ and ∞⁻¹ = 0. -/
noncomputable def powerSeriesRadius (c : ℕ → ℂ) : ℝ≥0∞ :=
  (powerSeriesRootLimsup c)⁻¹

end D12Complex

namespace Specs.D12Complex.Ch02.PowerSeriesRadius

open _root_.D12Complex

def rootLimsup_type := (ℕ → ℂ) → ℝ≥0∞
noncomputable def rootLimsup_value : rootLimsup_type :=
  fun c => limsup (fun n => ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop

def radius_type := (ℕ → ℂ) → ℝ≥0∞
noncomputable def radius_value : radius_type := fun c => (powerSeriesRootLimsup c)⁻¹

/-- Absolute convergence at every point strictly inside the radius. -/
def summable_norm_inside_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), (‖z - a‖₊ : ℝ≥0∞) < powerSeriesRadius c →
    Summable (fun n => ‖c n * (z - a) ^ n‖)

/-- Ordinary complex convergence follows as well. -/
def summable_inside_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), (‖z - a‖₊ : ℝ≥0∞) < powerSeriesRadius c →
    Summable (fun n => c n * (z - a) ^ n)

/-- Outside the radius even the necessary term test fails. -/
def not_tendsto_zero_outside_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), powerSeriesRadius c < (‖z - a‖₊ : ℝ≥0∞) →
    ¬ Tendsto (fun n => c n * (z - a) ^ n) atTop (𝓝 0)

def not_summable_outside_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), powerSeriesRadius c < (‖z - a‖₊ : ℝ≥0∞) →
    ¬ Summable (fun n => c n * (z - a) ^ n)

/-- Divergence in the ordinary sequential sense, without any choice of sum. -/
def not_convergent_partialSums_outside_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), powerSeriesRadius c < (‖z - a‖₊ : ℝ≥0∞) →
    ¬ ∃ s : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, c n * (z - a) ^ n)
      atTop (𝓝 s)

/-- Absolute uniform convergence on every smaller closed disk. Besides uniform
convergence of the complex partial sums and of their absolute-value series,
a summable scalar majorant is supplied on the entire disk. -/
def uniform_closedDisk_type : Prop :=
  ∀ (c : ℕ → ℂ) (a : ℂ) (r : ℝ), 0 ≤ r → ENNReal.ofReal r < powerSeriesRadius c →
    Summable (fun n => ‖c n‖ * r ^ n) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, c n * (z - a) ^ n)
      (fun z => ∑' n, c n * (z - a) ^ n) atTop (Metric.closedBall a r) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, ‖c n * (z - a) ^ n‖)
      (fun z => ∑' n, ‖c n * (z - a) ^ n‖) atTop (Metric.closedBall a r)

/-- Covers every polynomial coefficient sequence, including the zero sequence. -/
def radius_eq_top_of_eventually_zero_type : Prop :=
  ∀ (c : ℕ → ℂ), (∀ᶠ n in atTop, c n = 0) → powerSeriesRadius c = ⊤

/-- Explicit independence from the convention for the zeroth root term. -/
def rootLimsup_eq_with_zeroTerm_type : Prop :=
  ∀ (c : ℕ → ℂ) (b : ℝ≥0∞), powerSeriesRootLimsup c =
    limsup (fun n => if n = 0 then b else
      ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop

end Specs.D12Complex.Ch02.PowerSeriesRadius
