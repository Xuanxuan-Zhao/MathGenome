import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.FiniteProjection
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Nonnegative
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! K03.19.bessel, paper.tex:4725–4741. The coefficients and norm use the
normalized proper Darboux integral on [-π,π]. We state the stronger fixed-interval
version, which in particular covers every periodic Riemann-integrable function.
The witnesses for weights and squared norms are available for every integrable
input; they are not additional regularity hypotheses. The real case uses the
canonical embedding into ℂ and the real proper integral of |f|².

`Summable` is appropriate here because every term is nonnegative. The supremum
and extended-sum statements identify the total with the nonnegative sum of the
manuscript, independently of any enumeration of ℤ. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Bessel
open Ch08.Integral PeriodicSetup Representation FiniteProjection
open scoped BigOperators

def squaredNormIntegrability : Prop := ∀ (f : ℝ → ℂ),
  complexIntegrableValue f (-Real.pi) Real.pi →
  realIntegrableValue (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi

def finiteBessel : Prop := ∀ (f : ℝ → ℂ)
  (_hf : complexIntegrableValue f (-Real.pi) Real.pi)
  (h : ComplexWeights f)
  (hs : realIntegrableValue (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi)
  (E : Finset ℤ),
  ∑ n ∈ E, ‖coefficientValue f n (h n)‖ ^ 2 ≤ normSquaredValue f hs

def coefficientsSummable : Prop := ∀ (f : ℝ → ℂ)
  (_hf : complexIntegrableValue f (-Real.pi) Real.pi) (h : ComplexWeights f),
  Summable (fun n => ‖coefficientValue f n (h n)‖ ^ 2)

def totalBessel : Prop := ∀ (f : ℝ → ℂ)
  (_hf : complexIntegrableValue f (-Real.pi) Real.pi) (h : ComplexWeights f)
  (hs : realIntegrableValue (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi),
  (∑' n : ℤ, ‖coefficientValue f n (h n)‖ ^ 2) ≤ normSquaredValue f hs

def nonnegativeSum : Prop := ∀ (f : ℝ → ℂ)
  (_hf : complexIntegrableValue f (-Real.pi) Real.pi) (h : ComplexWeights f)
  (hs : realIntegrableValue (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi),
  IsLUB (Set.range (fun E : Finset ℤ => ∑ n ∈ E, ‖coefficientValue f n (h n)‖ ^ 2))
    (∑' n : ℤ, ‖coefficientValue f n (h n)‖ ^ 2) ∧
  Ch11.Nonnegative.nonnegativeExtendedSumValue (fun n => ‖coefficientValue f n (h n)‖ ^ 2) =
    ENNReal.ofReal (∑' n : ℤ, ‖coefficientValue f n (h n)‖ ^ 2) ∧
  Ch11.Nonnegative.nonnegativeExtendedSumValue (fun n => ‖coefficientValue f n (h n)‖ ^ 2) ≤
    ENNReal.ofReal (normSquaredValue f hs) ∧
  Ch11.Nonnegative.nonnegativeExtendedSumValue (fun n => ‖coefficientValue f n (h n)‖ ^ 2) ≠ ⊤

def realBessel : Prop := ∀ (f : ℝ → ℝ)
  (_hf : realIntegrableValue f (-Real.pi) Real.pi),
  realIntegrableValue (fun x => |f x| ^ 2) (-Real.pi) Real.pi ∧
  ∀ (h : ComplexWeights (fun x => (f x : ℂ)))
    (hs : realIntegrableValue (fun x => |f x| ^ 2) (-Real.pi) Real.pi),
    (∀ E : Finset ℤ, ∑ n ∈ E, ‖coefficientValue (fun x => (f x : ℂ)) n (h n)‖ ^ 2 ≤
      (1 / (2 * Real.pi)) * realIntegralValue (fun x => |f x| ^ 2) hs) ∧
    Summable (fun n => ‖coefficientValue (fun x => (f x : ℂ)) n (h n)‖ ^ 2) ∧
    (∑' n : ℤ, ‖coefficientValue (fun x => (f x : ℂ)) n (h n)‖ ^ 2) ≤
      (1 / (2 * Real.pi)) * realIntegralValue (fun x => |f x| ^ 2) hs

end Specs.SingleVariableAnalysis.Ch19.Bessel
