import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PowerSeriesCalculus

/-! Independent statements for paper.tex:337–352, the algebra and uniqueness
part of D12.02.02. Composition is allocated separately. All disks are strictly
inside both input radii; no assertion concerns a boundary of convergence. -/

open Filter
open scoped Topology NNReal ENNReal

namespace D12Complex.SeriesAlgebra

/-- Coefficientwise addition at a common center. -/
def addCoefficients (c d : ℕ → ℂ) (n : ℕ) : ℂ := c n + d n

/-- The Cauchy coefficient, including both endpoint terms. -/
def mulCoefficients (c d : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), c j * d (n - j)

/-- Absolute uniform convergence on a closed disk, including a summable
coefficient majorant and convergence of the series of absolute values. -/
def AbsoluteUniformOnDisk (c : ℕ → ℂ) (a : ℂ) (r : ℝ) (f : ℂ → ℂ) : Prop :=
  Summable (fun n => ‖c n‖ * r ^ n) ∧
  TendstoUniformlyOn
    (fun N z => ∑ n ∈ Finset.range N, c n * (z - a) ^ n)
    f atTop (Metric.closedBall a r) ∧
  TendstoUniformlyOn
    (fun N z => ∑ n ∈ Finset.range N, ‖c n * (z - a) ^ n‖)
    (fun z => ∑' n, ‖c n * (z - a) ^ n‖) atTop (Metric.closedBall a r)

end D12Complex.SeriesAlgebra

namespace Specs.D12Complex.Ch02.SeriesAlgebra

open _root_.D12Complex _root_.D12Complex.PowerSeriesCalculus _root_.D12Complex.SeriesAlgebra

def sum_add_type : Prop :=
  ∀ (c d : ℕ → ℂ) (a z : ℂ),
    z ∈ convergenceDisk c a → z ∈ convergenceDisk d a →
    Summable (fun n => ‖addCoefficients c d n * (z - a) ^ n‖) ∧
    HasSum (fun n => addCoefficients c d n * (z - a) ^ n)
      (seriesSum c a z + seriesSum d a z)

def sum_mul_type : Prop :=
  ∀ (c d : ℕ → ℂ) (a z : ℂ),
    z ∈ convergenceDisk c a → z ∈ convergenceDisk d a →
    Summable (fun n => ‖mulCoefficients c d n * (z - a) ^ n‖) ∧
    HasSum (fun n => mulCoefficients c d n * (z - a) ^ n)
      (seriesSum c a z * seriesSum d a z)

def uniform_add_type : Prop :=
  ∀ (c d : ℕ → ℂ) (a : ℂ) (r : ℝ), 0 ≤ r →
    ENNReal.ofReal r < powerSeriesRadius c → ENNReal.ofReal r < powerSeriesRadius d →
    AbsoluteUniformOnDisk (addCoefficients c d) a r
      (fun z => seriesSum c a z + seriesSum d a z)

def uniform_mul_type : Prop :=
  ∀ (c d : ℕ → ℂ) (a : ℂ) (r : ℝ), 0 ≤ r →
    ENNReal.ofReal r < powerSeriesRadius c → ENNReal.ofReal r < powerSeriesRadius d →
    AbsoluteUniformOnDisk (mulCoefficients c d) a r
      (fun z => seriesSum c a z * seriesSum d a z)

/-- Uniqueness from actual local convergent representations of the same function.
No derivative regularity or absolute convergence is added as a premise. -/
def coefficients_unique_type : Prop :=
  ∀ (c d : ℕ → ℂ) (a : ℂ) (f : ℂ → ℂ),
    (∀ᶠ z in 𝓝 a, HasSum (fun n => c n * (z - a) ^ n) (f z)) →
    (∀ᶠ z in 𝓝 a, HasSum (fun n => d n * (z - a) ^ n) (f z)) → c = d

end Specs.D12Complex.Ch02.SeriesAlgebra
