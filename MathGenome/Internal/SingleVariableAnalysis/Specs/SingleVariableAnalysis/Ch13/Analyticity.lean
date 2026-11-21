import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
K03.13.analyticity, paper.tex:1437–1442.

Real analyticity means local equality to an ordinary scalar power series,
with a strictly positive radius. A witness r is chosen strictly below the
coefficient-root radius; shrinking a positive convergence neighborhood always
allows this. The sum predicates are the upstream ordered, inclusive partial
sum limits. In particular they are not replaced by unconditional summability.

Both codomains ℝ and ℂ have domain ℝ and scalar field ℝ for analyticity and
all derivatives. The set formulation applies in particular to any open real
interval. A function may be arbitrary off that interval.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Analyticity
open PowerSeries
open scoped ContDiff

def realCoefficientSeriesType := (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝ ℝ
noncomputable def realCoefficientSeriesValue : realCoefficientSeriesType :=
  fun a n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a n)

def complexRealCoefficientSeriesType := (ℕ → ℂ) → FormalMultilinearSeries ℝ ℝ ℂ
noncomputable def complexRealCoefficientSeriesValue : complexRealCoefficientSeriesType :=
  fun a n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a n)

def RealPowerSeriesRepresentsAtType := (ℕ → ℝ) → (ℝ → ℝ) → ℝ → Prop
noncomputable def RealPowerSeriesRepresentsAtValue : RealPowerSeriesRepresentsAtType :=
  fun a f c => ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < realPowerSeriesRadiusValue a ∧
    ∀ h : ℝ, |h| < r → RealPowerSeriesHasSumValue a c (c+h) (f (c+h))

def ComplexRealPowerSeriesRepresentsAtType := (ℕ → ℂ) → (ℝ → ℂ) → ℝ → Prop
noncomputable def ComplexRealPowerSeriesRepresentsAtValue : ComplexRealPowerSeriesRepresentsAtType :=
  fun a f c => ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < complexPowerSeriesRadiusValue a ∧
    ∀ h : ℝ, |h| < r → ComplexPowerSeriesHasSumValue a c ((c+h : ℝ) : ℂ) (f (c+h))

def RealAnalyticOnType := (ℝ → ℝ) → Set ℝ → Prop
noncomputable def RealAnalyticOnValue : RealAnalyticOnType :=
  fun f I => ∀ c ∈ I, ∃ a : ℕ → ℝ, RealPowerSeriesRepresentsAtValue a f c

def ComplexRealAnalyticOnType := (ℝ → ℂ) → Set ℝ → Prop
noncomputable def ComplexRealAnalyticOnValue : ComplexRealAnalyticOnType :=
  fun f I => ∀ c ∈ I, ∃ a : ℕ → ℂ, ComplexRealPowerSeriesRepresentsAtValue a f c

def realNeighborhoodIff : Prop := ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ),
  RealPowerSeriesRepresentsAtValue a f c ↔ ∃ r : ℝ, 0 < r ∧
    ∀ h : ℝ, |h| < r → RealPowerSeriesHasSumValue a c (c+h) (f (c+h))

def complexRealNeighborhoodIff : Prop := ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ),
  ComplexRealPowerSeriesRepresentsAtValue a f c ↔ ∃ r : ℝ, 0 < r ∧
    ∀ h : ℝ, |h| < r → ComplexPowerSeriesHasSumValue a c ((c+h : ℝ) : ℂ) (f (c+h))

def realRepresentationIff : Prop := ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ),
  RealPowerSeriesRepresentsAtValue a f c ↔ HasFPowerSeriesAt f (realCoefficientSeriesValue a) c

def complexRealRepresentationIff : Prop := ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ),
  ComplexRealPowerSeriesRepresentsAtValue a f c ↔
    HasFPowerSeriesAt f (complexRealCoefficientSeriesValue a) c

def realAnalyticOnIff : Prop := ∀ (f : ℝ → ℝ) (I : Set ℝ),
  RealAnalyticOnValue f I ↔ AnalyticOnNhd ℝ f I

def complexRealAnalyticOnIff : Prop := ∀ (f : ℝ → ℂ) (I : Set ℝ),
  ComplexRealAnalyticOnValue f I ↔ AnalyticOnNhd ℝ f I

def realAnalyticSmooth : Prop := ∀ (f : ℝ → ℝ) (I : Set ℝ),
  RealAnalyticOnValue f I → ContDiffOn ℝ ∞ f I

def complexRealAnalyticSmooth : Prop := ∀ (f : ℝ → ℂ) (I : Set ℝ),
  ComplexRealAnalyticOnValue f I → ContDiffOn ℝ ∞ f I

def realPowerSeriesAnalytic : Prop := ∀ (a : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    RealPowerSeriesHasSumValue a c x (f x)) →
  RealAnalyticOnValue f {x | ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a}

def complexRealPowerSeriesAnalytic : Prop := ∀ (a : ℕ → ℂ) (c : ℝ) (f : ℝ → ℂ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    ComplexPowerSeriesHasSumValue a c (x : ℂ) (f x)) →
  ComplexRealAnalyticOnValue f {x | ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a}

def realCoefficientDerivative : Prop := ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ),
  RealPowerSeriesRepresentsAtValue a f c → ∀ k : ℕ,
    iteratedDeriv k f c = (k.factorial : ℝ) * a k

def complexRealCoefficientDerivative : Prop := ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ),
  ComplexRealPowerSeriesRepresentsAtValue a f c → ∀ k : ℕ,
    iteratedDeriv k f c = (k.factorial : ℂ) * a k

end Specs.SingleVariableAnalysis.Ch13.Analyticity
