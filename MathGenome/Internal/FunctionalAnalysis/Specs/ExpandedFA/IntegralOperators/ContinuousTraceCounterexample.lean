import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Polynomial.Eval.Defs
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions

/-! The circle is ℝ/ℤ, with Haar measure of mass one. The block index `m`
starts at zero in Lean and represents the manuscript's `m + 1`.
All definitions below are unconditional: no counterexample properties are
assumed in the definition of the series or the integral operator. -/
noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal
namespace ExpandedFA.IntegralOperators.ContinuousTraceCounterexample.Spec

abbrev Torus := AddCircle (1 : ℝ)
abbrev circleMeasure : Measure Torus := AddCircle.haarAddCircle
abbrev CircleL2 := Lp ℂ 2 circleMeasure
abbrev RealCircleL2 := Lp ℝ 2 circleMeasure

/-- The exact P,Q recursion in the manuscript. -/
def rudinShapiro : ℕ → Polynomial ℂ × Polynomial ℂ
  | 0 => (1, 1)
  | r + 1 =>
    let p := rudinShapiro r
    (p.1 + X ^ (2 ^ r) * p.2, p.1 - X ^ (2 ^ r) * p.2)

abbrev P (r : ℕ) := (rudinShapiro r).1
abbrev Q (r : ℕ) := (rudinShapiro r).2

/-- `blockStart m` is N_{m+1}. In particular the first block starts at 1. -/
def blockStart (m : ℕ) : ℕ := 1 + ∑ j ∈ Finset.range m, 2 ^ (2 * (j + 1))

def blockWeight (m : ℕ) : ℝ := ((2 : ℝ) ^ (m + 1))⁻¹ / (((m + 1 : ℕ) : ℝ) ^ 2)

def blockTerm (m : ℕ) (t : Torus) : ℂ :=
  (blockWeight m : ℂ) * (fourier 1 t) ^ blockStart m *
    (P (2 * (m + 1))).eval (fourier 1 t)

def complexSeries (t : Torus) : ℂ := ∑' m : ℕ, blockTerm m t

def realSeries (t : Torus) : ℝ := (complexSeries t).re

def convolutionKernel (f : Torus → ℝ) (xy : Torus × Torus) : ℂ :=
  (f (xy.1 - xy.2) : ℂ)

def realConvolutionKernel (f : Torus → ℝ) (xy : Torus × Torus) : ℝ :=
  f (xy.1 - xy.2)

/-- Full properties of the original continuous even convolution example,
using the existing product L² kernel assignment and singular-value S₁.
The explicit kernel regularity and symmetry are included for reviewability. -/
def CounterexampleProperties (f : Torus → ℝ) : Prop :=
  Continuous f ∧ Function.Even f ∧
  ¬ Summable (fun n : ℤ => ‖fourierCoeff (fun t => (f t : ℂ)) n‖) ∧
  Continuous (convolutionKernel f) ∧
  (∀ x y, convolutionKernel f (x, y) = convolutionKernel f (y, x)) ∧
  ∃ hk : MemLp (convolutionKernel f) 2 (circleMeasure.prod circleMeasure),
    let K := PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
      (hk.toLp (convolutionKernel f))
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap ∧
    IsSelfAdjoint K ∧
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue K ∧
    ¬ TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue K

def ExplicitCounterexample : Prop := CounterexampleProperties realSeries

/-- The same kernel acting on actual real-valued L², with its real singular
values and real trace-class predicate. -/
def RealCounterexampleProperties (f : Torus → ℝ) : Prop :=
  Continuous f ∧ Function.Even f ∧
  Continuous (realConvolutionKernel f) ∧
  (∀ x y, realConvolutionKernel f (x, y) = realConvolutionKernel f (y, x)) ∧
  ∃ hk : MemLp (realConvolutionKernel f) 2 (circleMeasure.prod circleMeasure),
    let K : RealCircleL2 →L[ℝ] RealCircleL2 :=
      PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
        (hk.toLp (realConvolutionKernel f))
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap ∧
    IsSelfAdjoint K ∧
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue K ∧
    ¬ TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue K

def ExplicitRealCounterexample : Prop := RealCounterexampleProperties realSeries

def ContinuousCounterexample : Prop :=
  ∃ f : Torus → ℝ, CounterexampleProperties f ∧ RealCounterexampleProperties f

end ExpandedFA.IntegralOperators.ContinuousTraceCounterexample.Spec
