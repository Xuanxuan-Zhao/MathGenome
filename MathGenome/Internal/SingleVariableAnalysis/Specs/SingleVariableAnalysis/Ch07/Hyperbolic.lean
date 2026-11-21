import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction
import Mathlib.Analysis.Complex.Trigonometric

/-!
Independent specification for the direct-function part of K03.07.hyperbolic,
paper.tex:1761–1801. The exponential in the definitions is the shared
factorial-series sum. All functions have real domain and real codomain.
The principal inverse functions are allocated to HyperbolicInverses.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.Hyperbolic

open Set Filter
open scoped Topology
open ExpConstruction

def realSinhType : Type := ℝ → ℝ
def realSinhValue : realSinhType :=
  fun x => (realSeriesExpValue x - realSeriesExpValue (-x)) / 2

def realCoshType : Type := ℝ → ℝ
def realCoshValue : realCoshType :=
  fun x => (realSeriesExpValue x + realSeriesExpValue (-x)) / 2

def realTanhType : Type := ℝ → ℝ
def realTanhValue : realTanhType := fun x => realSinhValue x / realCoshValue x

def canonicalSinh : Prop := ∀ x, realSinhValue x = Real.sinh x
def canonicalCosh : Prop := ∀ x, realCoshValue x = Real.cosh x
def canonicalTanh : Prop := ∀ x, realTanhValue x = Real.tanh x

def squareIdentity : Prop := ∀ x, realCoshValue x ^ 2 - realSinhValue x ^ 2 = 1
def coshPositive : Prop := ∀ x, 0 < realCoshValue x

def sinhDerivative : Prop := ∀ x, HasDerivAt realSinhValue (realCoshValue x) x
def coshDerivative : Prop := ∀ x, HasDerivAt realCoshValue (realSinhValue x) x
def tanhDerivative : Prop := ∀ x, HasDerivAt realTanhValue (1 / realCoshValue x ^ 2) x

def sinhStrictIncrease : Prop := StrictMono realSinhValue
def tanhStrictIncrease : Prop := StrictMono realTanhValue
def sinhRange : Prop := range realSinhValue = univ
def tanhRange : Prop := range realTanhValue = Ioo (-1) 1

def coshStrictDecrease : Prop := StrictAntiOn realCoshValue (Iic 0)
def coshStrictIncrease : Prop := StrictMonoOn realCoshValue (Ici 0)
def coshMinimum : Prop :=
  realCoshValue 0 = 1 ∧ ∀ x, 1 ≤ realCoshValue x ∧ (realCoshValue x = 1 ↔ x = 0)

def sinhLimitNegInfinity : Prop := Tendsto realSinhValue atBot atBot
def sinhLimitPosInfinity : Prop := Tendsto realSinhValue atTop atTop
def tanhLimitNegInfinity : Prop := Tendsto realTanhValue atBot (𝓝 (-1))
def tanhLimitPosInfinity : Prop := Tendsto realTanhValue atTop (𝓝 1)

def tanhExponentialQuotient : Prop :=
  ∀ x, realTanhValue x =
    (realSeriesExpValue (2 * x) - 1) / (realSeriesExpValue (2 * x) + 1)

def sinhOdd : Prop := ∀ x, realSinhValue (-x) = -realSinhValue x
def coshEven : Prop := ∀ x, realCoshValue (-x) = realCoshValue x
def tanhOdd : Prop := ∀ x, realTanhValue (-x) = -realTanhValue x

end Specs.SingleVariableAnalysis.Ch07.Hyperbolic
