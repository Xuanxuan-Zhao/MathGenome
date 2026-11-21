import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent specification for K03.07.exp_construction, paper.tex:1542–1560.
Both functions are defined by their factorial series, rather than by a
canonical exponential or an assumed solution of a differential equation.
Partial sums include indices 0,…,N. Disk convergence uses a single index
for every complex argument of modulus at most R, including R=0.
The last two derivatives have real domain, even for the complex target.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.ExpConstruction
open scoped BigOperators
open Ch11.PartialSums Ch11.Absolute Ch12.Uniform

def seriesExpType : Type := ℂ → ℂ
def seriesExpValue : seriesExpType := fun z => ∑' n : ℕ, z^n / (n.factorial : ℂ)

def realSeriesExpType : Type := ℝ → ℝ
def realSeriesExpValue : realSeriesExpType := fun x => ∑' n : ℕ, x^n / (n.factorial : ℝ)

def absoluteConvergence : Prop :=
  ∀ z : ℂ, complexAbsolutelyConvergesValue (fun n => z^n / (n.factorial : ℂ))

def seriesValue : Prop :=
  ∀ z : ℂ, complexSeriesHasSumValue (fun n => z^n / (n.factorial : ℂ)) (seriesExpValue z)

def uniformDisk : Prop :=
  ∀ R : ℝ, 0 ≤ R → complexUniformConvergesValue
    (fun N (z : {z : ℂ // ‖z‖ ≤ R}) =>
      complexPartialSumValue (fun n => (z : ℂ)^n / (n.factorial : ℂ)) N)
    (fun z => seriesExpValue z)

def realSeriesValue : Prop :=
  ∀ x : ℝ, realSeriesHasSumValue (fun n => x^n / (n.factorial : ℝ)) (realSeriesExpValue x)

def canonicalComplex : Prop := ∀ z : ℂ, seriesExpValue z = Complex.exp z

def canonicalReal : Prop := ∀ x : ℝ, realSeriesExpValue x = Real.exp x

def realRestriction : Prop :=
  ∀ x : ℝ, seriesExpValue (x : ℂ) = (realSeriesExpValue x : ℂ)

def realDerivative : Prop :=
  ∀ x : ℝ, HasDerivAt realSeriesExpValue (realSeriesExpValue x) x

def complexRealDerivative : Prop :=
  ∀ x : ℝ, HasDerivAt (fun t : ℝ => seriesExpValue (t : ℂ)) (seriesExpValue (x : ℂ)) x

end Specs.SingleVariableAnalysis.Ch07.ExpConstruction
