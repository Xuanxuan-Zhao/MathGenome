import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent specification for K03.07.sin_cos (paper.tex:1652–1667).
The functions are defined by the displayed factorial series.  The parameter k
is 1 for sine and 0 for cosine.  All ordinary partial sums include 0,…,N.
Uniform convergence uses one threshold over the whole closed disk, including
radius zero. Derivatives have real domain even when the codomain is complex.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.SinCos
open scoped BigOperators
open Ch11.PartialSums Ch11.Absolute Ch12.Uniform

def complexTerm (k : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  (-1)^n * z^(2*n+k) / ((2*n+k).factorial : ℂ)
def realTerm (k : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  (-1)^n * x^(2*n+k) / ((2*n+k).factorial : ℝ)

def seriesSinType : Type := ℂ → ℂ
def seriesSinValue : seriesSinType := fun z => ∑' n, complexTerm 1 z n
def seriesCosType : Type := ℂ → ℂ
def seriesCosValue : seriesCosType := fun z => ∑' n, complexTerm 0 z n
def realSeriesSinType : Type := ℝ → ℝ
def realSeriesSinValue : realSeriesSinType := fun x => ∑' n, realTerm 1 x n
def realSeriesCosType : Type := ℝ → ℝ
def realSeriesCosValue : realSeriesCosType := fun x => ∑' n, realTerm 0 x n

def complexAbsolute : Prop := ∀ z : ℂ,
  complexAbsolutelyConvergesValue (complexTerm 1 z) ∧
  complexAbsolutelyConvergesValue (complexTerm 0 z)
def realAbsolute : Prop := ∀ x : ℝ,
  realAbsolutelyConvergesValue (realTerm 1 x) ∧
  realAbsolutelyConvergesValue (realTerm 0 x)

def complexSeriesValue : Prop := ∀ z : ℂ,
  complexSeriesHasSumValue (complexTerm 1 z) (seriesSinValue z) ∧
  complexSeriesHasSumValue (complexTerm 0 z) (seriesCosValue z)
def realSeriesValue : Prop := ∀ x : ℝ,
  realSeriesHasSumValue (realTerm 1 x) (realSeriesSinValue x) ∧
  realSeriesHasSumValue (realTerm 0 x) (realSeriesCosValue x)

def complexUniformDisk : Prop := ∀ R : ℝ, 0 ≤ R →
  complexUniformConvergesValue
    (fun N (z : {z : ℂ // ‖z‖ ≤ R}) => complexPartialSumValue (complexTerm 1 z) N)
    (fun z => seriesSinValue z) ∧
  complexUniformConvergesValue
    (fun N (z : {z : ℂ // ‖z‖ ≤ R}) => complexPartialSumValue (complexTerm 0 z) N)
    (fun z => seriesCosValue z)
def realUniformDisk : Prop := ∀ R : ℝ, 0 ≤ R →
  realUniformConvergesValue
    (fun N (x : {x : ℝ // |x| ≤ R}) => realPartialSumValue (realTerm 1 x) N)
    (fun x => realSeriesSinValue x) ∧
  realUniformConvergesValue
    (fun N (x : {x : ℝ // |x| ≤ R}) => realPartialSumValue (realTerm 0 x) N)
    (fun x => realSeriesCosValue x)

def canonicalComplex : Prop := ∀ z : ℂ,
  seriesSinValue z = Complex.sin z ∧ seriesCosValue z = Complex.cos z
def canonicalReal : Prop := ∀ x : ℝ,
  realSeriesSinValue x = Real.sin x ∧ realSeriesCosValue x = Real.cos x

def realRestriction : Prop := ∀ x : ℝ,
  seriesSinValue (x : ℂ) = (realSeriesSinValue x : ℂ) ∧
  seriesCosValue (x : ℂ) = (realSeriesCosValue x : ℂ)

def realDerivatives : Prop := ∀ x : ℝ,
  HasDerivAt realSeriesSinValue (realSeriesCosValue x) x ∧
  HasDerivAt realSeriesCosValue (-realSeriesSinValue x) x

def complexRealDerivatives : Prop := ∀ x : ℝ,
  HasDerivAt (fun t : ℝ => seriesSinValue (t : ℂ)) (seriesCosValue (x : ℂ)) x ∧
  HasDerivAt (fun t : ℝ => seriesCosValue (t : ℂ)) (-seriesSinValue (x : ℂ)) x

def complexInitialValues : Prop := seriesSinValue 0 = 0 ∧ seriesCosValue 0 = 1
def realInitialValues : Prop := realSeriesSinValue 0 = 0 ∧ realSeriesCosValue 0 = 1

end Specs.SingleVariableAnalysis.Ch07.SinCos
