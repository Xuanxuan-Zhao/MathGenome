import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Representation
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! K03.19.normalization_bridge, paper.tex:5058–5078.
All integrals are proper Darboux integrals. The function is only assumed
periodic and integrable on one period; weighted integrability and integrability
of the rescaled function are conclusions. Real functions use their canonical
embedding into ℂ, as in Representation. The integral origin and translation
of the function are separate parameters. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.NormalizationBridge
open Ch08.Integral PeriodicSetup
open scoped BigOperators

abbrev periodModeType := ℝ → ℤ → ℝ → ℂ
def periodModeValue : periodModeType := fun T n x => modeValue n (2 * Real.pi * x / T)

abbrev rescaleType := (ℝ → ℂ) → ℝ → ℝ → ℂ
def rescaleValue : rescaleType := fun f T t => f (T * t / (2 * Real.pi))

abbrev periodCoefficientType := (f : ℝ → ℂ) → (T a : ℝ) → (n : ℤ) →
  complexIntegrableValue (fun x => f x * periodModeValue T (-n) x) a (a+T) → ℂ
def periodCoefficientValue : periodCoefficientType := fun f T _ n h =>
  ((T⁻¹ : ℝ) : ℂ) * complexIntegralValue (fun x => f x * periodModeValue T (-n) x) h

abbrev PeriodWeights (f : ℝ → ℂ) (T a : ℝ) := ∀ n : ℤ,
  complexIntegrableValue (fun x => f x * periodModeValue T (-n) x) a (a+T)

abbrev periodPartialSumType := (f : ℝ → ℂ) → (T a : ℝ) →
  PeriodWeights f T a → ℕ → ℝ → ℂ
def periodPartialSumValue : periodPartialSumType := fun f T a h N x =>
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    periodCoefficientValue f T a n (h n) * periodModeValue T n x

/-- A real input has the same periodicity and componentwise integrability
when embedded into ℂ; all subsequent coefficient theorems therefore apply. -/
def realInputBridge : Prop := ∀ (f : ℝ → ℝ) (T b : ℝ),
  0 < T → Function.Periodic f T → realIntegrableValue f b (b+T) →
  Function.Periodic (fun x => (f x : ℂ)) T ∧
    complexIntegrableValue (fun x => (f x : ℂ)) b (b+T)

def weightedIntegrability : Prop := ∀ (f : ℝ → ℂ) (T b : ℝ),
  0 < T → Function.Periodic f T → complexIntegrableValue f b (b+T) →
  ∀ a : ℝ, PeriodWeights f T a

def originIndependence : Prop := ∀ (f : ℝ → ℂ) (T : ℝ),
  0 < T → Function.Periodic f T → ∀ (a b : ℝ) (n : ℤ)
    (ha : complexIntegrableValue (fun x => f x * periodModeValue T (-n) x) a (a+T))
    (hb : complexIntegrableValue (fun x => f x * periodModeValue T (-n) x) b (b+T)),
    periodCoefficientValue f T a n ha = periodCoefficientValue f T b n hb

def rescaledIntegrability : Prop := ∀ (f : ℝ → ℂ) (T b : ℝ),
  0 < T → Function.Periodic f T → complexIntegrableValue f b (b+T) →
  periodicComplexValue (rescaleValue f T)

def coefficientRescaling : Prop := ∀ (f : ℝ → ℂ) (T b : ℝ),
  0 < T → Function.Periodic f T → complexIntegrableValue f b (b+T) →
  ∀ (a : ℝ) (n : ℤ)
    (hg : complexIntegrableValue (fun t => rescaleValue f T t * modeValue (-n) t)
      (-Real.pi) Real.pi)
    (ha : complexIntegrableValue (fun x => f x * periodModeValue T (-n) x) a (a+T)),
  coefficientValue (rescaleValue f T) n hg = periodCoefficientValue f T a n ha

def translationPhase : Prop := ∀ (f : ℝ → ℂ) (T b : ℝ),
  0 < T → Function.Periodic f T → complexIntegrableValue f b (b+T) →
  ∀ (c a d : ℝ) (n : ℤ),
  ∃ hc : complexIntegrableValue
      (fun x => f (x+c) * periodModeValue T (-n) x) a (a+T),
  ∀ hd : complexIntegrableValue (fun x => f x * periodModeValue T (-n) x) d (d+T),
    periodCoefficientValue (fun x => f (x+c)) T a n hc =
      periodModeValue T n c * periodCoefficientValue f T d n hd

def partialSumRescaling : Prop := ∀ (f : ℝ → ℂ) (T b : ℝ),
  0 < T → Function.Periodic f T → complexIntegrableValue f b (b+T) →
  ∀ (a : ℝ) (h : PeriodWeights f T a)
    (hg : Representation.ComplexWeights (rescaleValue f T)) (N : ℕ) (t : ℝ),
  partialSumValue (rescaleValue f T) hg N t =
    periodPartialSumValue f T a h N (T * t / (2 * Real.pi))

/-- Convergence transfers by equality of the actual finite sums. -/
def pointwiseConvergenceTransfer : Prop := ∀ (f : ℝ → ℂ) (T b : ℝ),
  0 < T → Function.Periodic f T → complexIntegrableValue f b (b+T) →
  ∀ (a : ℝ) (h : PeriodWeights f T a)
    (hg : Representation.ComplexWeights (rescaleValue f T)) (t : ℝ) (L : ℂ),
  Filter.Tendsto (fun N => partialSumValue (rescaleValue f T) hg N t)
      Filter.atTop (nhds L) ↔
    Filter.Tendsto (fun N => periodPartialSumValue f T a h N (T*t/(2*Real.pi)))
      Filter.atTop (nhds L)

/-- Uniform convergence is transported by the bijective change of variable. -/
def uniformConvergenceTransfer : Prop := ∀ (f : ℝ → ℂ) (T b : ℝ),
  0 < T → Function.Periodic f T → complexIntegrableValue f b (b+T) →
  ∀ (a : ℝ) (h : PeriodWeights f T a)
    (hg : Representation.ComplexWeights (rescaleValue f T)) (F : ℝ → ℂ),
  TendstoUniformly (fun N t => partialSumValue (rescaleValue f T) hg N t)
      (rescaleValue F T) Filter.atTop ↔
    TendstoUniformly (fun N x => periodPartialSumValue f T a h N x) F Filter.atTop

/-- Retain exactly the previously proved real/complex conversions. -/
def realRepresentations : Prop := Representation.zeroCoefficient ∧
  Representation.positiveCoefficient ∧ Representation.negativeCoefficient ∧
  Representation.finitePartialSum

end Specs.SingleVariableAnalysis.Ch19.NormalizationBridge
