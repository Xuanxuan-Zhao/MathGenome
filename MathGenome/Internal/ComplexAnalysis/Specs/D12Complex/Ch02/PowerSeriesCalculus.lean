import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PowerSeriesRadius
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Factorial.Basic

/-! Independent specifications for the calculus part of paper.tex:296–335.
The coefficient operations are formal and make sense even at radius zero.
Analytic conclusions are restricted to the open convergence disk. -/

open Filter
open scoped Topology NNReal ENNReal

namespace D12Complex.PowerSeriesCalculus

/-- The actual scalar sum, centered at a. -/
noncomputable def seriesSum (c : ℕ → ℂ) (a z : ℂ) : ℂ :=
  ∑' n, c n * (z - a) ^ n

/-- The coefficients after one formal differentiation, reindexed from zero. -/
def derivativeCoefficients (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n + 1 : ℕ) * c (n + 1)

/-- Repeated formal differentiation. The explicit factorial formula is a target below. -/
def iteratedCoefficients (c : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => c
  | k + 1 => derivativeCoefficients (iteratedCoefficients c k)

/-- The formal primitive with constant coefficient zero. -/
noncomputable def primitiveCoefficients (c : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => c n / (n + 1 : ℕ)

/-- Extended radii cover both an empty disk at R=0 and the whole plane at R=∞. -/
def convergenceDisk (c : ℕ → ℂ) (a : ℂ) : Set ℂ :=
  {z | (‖z - a‖₊ : ℝ≥0∞) < powerSeriesRadius c}

end D12Complex.PowerSeriesCalculus

namespace Specs.D12Complex.Ch02.PowerSeriesCalculus

open _root_.D12Complex _root_.D12Complex.PowerSeriesCalculus

/-- The nth coefficient of the kth derivative is (n+k)!/n! times c(n+k).
The ascending factorial avoids truncated natural-number division. -/
def iteratedCoefficients_formula_type : Prop :=
  ∀ (c : ℕ → ℂ) (k n : ℕ), iteratedCoefficients c k n =
    ((n + 1).ascFactorial k : ℂ) * c (n + k)

def radius_derivative_type : Prop :=
  ∀ c : ℕ → ℂ, powerSeriesRadius (derivativeCoefficients c) = powerSeriesRadius c

def radius_iterated_type : Prop :=
  ∀ (c : ℕ → ℂ) (k : ℕ),
    powerSeriesRadius (iteratedCoefficients c k) = powerSeriesRadius c

def radius_primitive_type : Prop :=
  ∀ c : ℕ → ℂ, powerSeriesRadius (primitiveCoefficients c) = powerSeriesRadius c

def hasDerivAt_sum_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), z ∈ convergenceDisk c a →
    HasDerivAt (seriesSum c a) (seriesSum (derivativeCoefficients c) a z) z

def holomorphic_sum_type : Prop :=
  ∀ (c : ℕ → ℂ) (a : ℂ), HolomorphicOn (convergenceDisk c a) (seriesSum c a)

def iteratedDeriv_sum_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ) (k : ℕ), z ∈ convergenceDisk c a →
    iteratedDeriv k (seriesSum c a) z = seriesSum (iteratedCoefficients c k) a z

/-- Every derivative series converges absolutely uniformly on each smaller closed
 disk, to the actual kth derivative. A summable majorant and uniform convergence
 of the series of absolute values are included. -/
def uniform_derivatives_type : Prop :=
  ∀ (c : ℕ → ℂ) (a : ℂ) (k : ℕ) (r : ℝ),
    0 ≤ r → ENNReal.ofReal r < powerSeriesRadius c →
    Summable (fun n => ‖iteratedCoefficients c k n‖ * r ^ n) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, iteratedCoefficients c k n * (z - a) ^ n)
      (iteratedDeriv k (seriesSum c a)) atTop (Metric.closedBall a r) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, ‖iteratedCoefficients c k n * (z - a) ^ n‖)
      (fun z => ∑' n, ‖iteratedCoefficients c k n * (z - a) ^ n‖)
      atTop (Metric.closedBall a r)

def holomorphic_iterated_type : Prop :=
  ∀ (c : ℕ → ℂ) (a : ℂ) (k : ℕ),
    HolomorphicOn (convergenceDisk c a) (iteratedDeriv k (seriesSum c a))

def primitive_sum_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), z ∈ convergenceDisk c a →
    seriesSum (primitiveCoefficients c) a z =
      ∑' n, (c n / (n + 1 : ℕ)) * (z - a) ^ (n + 1)

def hasDerivAt_primitive_type : Prop :=
  ∀ (c : ℕ → ℂ) (a z : ℂ), z ∈ convergenceDisk c a →
    HasDerivAt (seriesSum (primitiveCoefficients c) a) (seriesSum c a z) z

def coefficient_identification_type : Prop :=
  ∀ (c : ℕ → ℂ) (a : ℂ) (n : ℕ), 0 < powerSeriesRadius c →
    c n = iteratedDeriv n (seriesSum c a) a / (n.factorial : ℂ)

end Specs.D12Complex.Ch02.PowerSeriesCalculus
