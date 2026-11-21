import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SinCos
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Asymptotics.Defs

/-! Independent specification of paper.tex:2850–2881. All derivatives use real
increments. The functions are the previously constructed series/inverse functions.
The logarithm sum is indexed by k=0,…,n-1, corresponding to source index k+1.
Uniform estimates imply the stated local big-O results and include x=0 and n=0.
The power coefficient is the empty product 1 at order zero. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch06.ReferenceExpansions
open scoped BigOperators Topology
open Ch07.ExpConstruction Ch07.LogConstruction Ch07.RealPowers Ch07.SinCos

def falling (α : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (α - i)
def expPoly (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range (n+1), x^k / (k.factorial : ℝ)
def logPoly (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range n, (-1 : ℝ)^k * x^(k+1) / (k+1)
def powerPoly (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), falling α k / (k.factorial : ℝ) * x^k
def sinPoly (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), (-1 : ℝ)^j * x^(2*j+1) / ((2*j+1).factorial : ℝ)
def cosPoly (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), (-1 : ℝ)^j * x^(2*j) / ((2*j).factorial : ℝ)
def powerBound (α : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  |falling α (n+1)| * max ((1-r) ^ (α-n-1)) ((1+r) ^ (α-n-1))

def expDerivatives : Prop := ∀ k x,
  iteratedDeriv k realSeriesExpValue x = realSeriesExpValue x

def logDerivatives : Prop := ∀ k x, -1 < x →
  iteratedDeriv (k+1) (fun t => seriesLogValue (1+t)) x =
    (-1 : ℝ)^k * (k.factorial : ℝ) / (1+x)^(k+1)

def powerDerivatives : Prop := ∀ α k x, -1 < x →
  iteratedDeriv k (fun t => realPowerValue (1+t) α) x =
    falling α k * realPowerValue (1+x) (α-k)

def trigDerivatives : Prop := ∀ k x,
  iteratedDeriv (2*k) realSeriesSinValue x = (-1 : ℝ)^k * realSeriesSinValue x ∧
  iteratedDeriv (2*k+1) realSeriesSinValue x = (-1 : ℝ)^k * realSeriesCosValue x ∧
  iteratedDeriv (2*k) realSeriesCosValue x = (-1 : ℝ)^k * realSeriesCosValue x ∧
  iteratedDeriv (2*k+1) realSeriesCosValue x = (-1 : ℝ)^(k+1) * realSeriesSinValue x

def expDerivativeBound : Prop := ∀ n r, 0 < r → ∀ x, |x| ≤ r →
  |iteratedDeriv (n+1) realSeriesExpValue x| ≤ Real.exp r

def logDerivativeBound : Prop := ∀ n r, 0 < r → r < 1 → ∀ x, |x| ≤ r →
  |iteratedDeriv (n+1) (fun t => seriesLogValue (1+t)) x| ≤
    (n.factorial : ℝ) / (1-r)^(n+1)

def powerDerivativeBound : Prop := ∀ α n r, 0 < r → r < 1 → ∀ x, |x| ≤ r →
  |iteratedDeriv (n+1) (fun t => realPowerValue (1+t) α) x| ≤ powerBound α n r

def trigDerivativeBound : Prop := ∀ k x,
  |iteratedDeriv k realSeriesSinValue x| ≤ 1 ∧
  |iteratedDeriv k realSeriesCosValue x| ≤ 1

def expUniform : Prop := ∀ n r, 0 < r → ∀ x, |x| ≤ r →
  |realSeriesExpValue x - expPoly n x| ≤ Real.exp r / ((n+1).factorial : ℝ) * |x|^(n+1)

def logUniform : Prop := ∀ n r, 0 < r → r < 1 → ∀ x, |x| ≤ r →
  |seriesLogValue (1+x) - logPoly n x| ≤ |x|^(n+1) / ((n+1) * (1-r)^(n+1))

def powerUniform : Prop := ∀ α n r, 0 < r → r < 1 → ∀ x, |x| ≤ r →
  |realPowerValue (1+x) α - powerPoly α n x| ≤
    powerBound α n r / ((n+1).factorial : ℝ) * |x|^(n+1)

def sinUniform : Prop := ∀ m r, 0 < r → ∀ x, |x| ≤ r →
  |realSeriesSinValue x - sinPoly m x| ≤ |x|^(2*m+3) / ((2*m+3).factorial : ℝ)

def cosUniform : Prop := ∀ m r, 0 < r → ∀ x, |x| ≤ r →
  |realSeriesCosValue x - cosPoly m x| ≤ |x|^(2*m+2) / ((2*m+2).factorial : ℝ)

def expBigO : Prop := ∀ n, Asymptotics.IsBigO (𝓝 (0:ℝ))
  (fun x => realSeriesExpValue x - expPoly n x) (fun x => x^(n+1))
def logBigO : Prop := ∀ n, Asymptotics.IsBigO (𝓝 (0:ℝ))
  (fun x => seriesLogValue (1+x) - logPoly n x) (fun x => x^(n+1))
def powerBigO : Prop := ∀ α n, Asymptotics.IsBigO (𝓝 (0:ℝ))
  (fun x => realPowerValue (1+x) α - powerPoly α n x) (fun x => x^(n+1))
def sinBigO : Prop := ∀ m, Asymptotics.IsBigO (𝓝 (0:ℝ))
  (fun x => realSeriesSinValue x - sinPoly m x) (fun x => x^(2*m+3))
def cosBigO : Prop := ∀ m, Asymptotics.IsBigO (𝓝 (0:ℝ))
  (fun x => realSeriesCosValue x - cosPoly m x) (fun x => x^(2*m+2))
end Specs.SingleVariableAnalysis.Ch06.ReferenceExpansions
