import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Volterra on the ordinary a.e. quotient L²((0,1), Lebesgue).
All scalar-valued assertions are made for both real and complex scalars.
The kernel is the actual indicator of t < x, not a diagonal sequence model. -/
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Topology
namespace ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec

abbrev intervalMeasure : Measure ℝ := volume.restrict (Set.Ioo 0 1)
abbrev Space (𝕜 : Type) [RCLike 𝕜] := Lp 𝕜 2 intervalMeasure

def rawKernel (𝕜 : Type) [RCLike 𝕜] (p : ℝ × ℝ) : 𝕜 :=
  if p.2 < p.1 then 1 else 0

lemma rawKernel_memLp (𝕜 : Type) [RCLike 𝕜] :
    MemLp (rawKernel 𝕜) 2 (intervalMeasure.prod intervalMeasure) := by
  apply MemLp.of_bound (C := 1)
  · exact ((measurable_const.indicator (measurableSet_lt measurable_snd measurable_fst)) :
      Measurable ({p : ℝ × ℝ | p.2 < p.1}.indicator (fun _ => (1 : 𝕜)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      simp only [rawKernel]
      split <;> simp

def kernelValue (𝕜 : Type) [RCLike 𝕜] :
    Lp 𝕜 2 (intervalMeasure.prod intervalMeasure) :=
  (rawKernel_memLp 𝕜).toLp (rawKernel 𝕜)

def VolterraValue (𝕜 : Type) [RCLike 𝕜] : Space 𝕜 →L[𝕜] Space 𝕜 :=
  PartV.L2KernelSpec.OperatorValue intervalMeasure intervalMeasure (kernelValue 𝕜)

def VolterraType := ∀ (𝕜 : Type) [RCLike 𝕜], Space 𝕜 →L[𝕜] Space 𝕜

def singularValue (n : ℕ) : ℝ := (((n : ℝ) + 1 / 2) * Real.pi)⁻¹

/-- The representative formula specifies the original integration operator. -/
def IntegralFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (f : Space 𝕜),
  (VolterraValue 𝕜 f : ℝ → 𝕜) =ᵐ[intervalMeasure]
    fun x => ∫ t in Set.Ioo 0 x, f t

def HilbertSchmidt : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue (VolterraValue 𝕜)

def Compact : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  Compactness.DefinitionsSpec.IsCompactLinearMapValue (VolterraValue 𝕜).toLinearMap

def SingularValues : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ),
  TraceIdeals.TraceClassDefinitions.Spec.singularSequence (VolterraValue 𝕜) n =
    singularValue n

def NotTraceClass : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ¬ TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (VolterraValue 𝕜)

def KernelSquareNorm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ‖kernelValue 𝕜‖ ^ 2 = 1 / 2

def HilbertSchmidtSquareNorm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (h : TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue (VolterraValue 𝕜)),
  TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtNormValue
    ⟨VolterraValue 𝕜, h⟩ ^ 2 = 1 / 2

def SingularValueNotSummable : Prop := ¬ Summable singularValue

def NotTraceClassFromSingularValues : Prop := SingularValues → NotTraceClass

/-- In the real case this uses the real spectrum; the complex case is the
usual spectral characterization of quasinilpotence. -/
def ZeroSpectrum : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  spectrum 𝕜 (VolterraValue 𝕜) = {0}

/-- Norm-root quasinilpotence, including the real operator. Positive powers
are indexed by n+1 to avoid a zero exponent in the denominator. -/
def Quasinilpotent : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  Filter.Tendsto (fun n : ℕ => ‖(VolterraValue 𝕜) ^ (n + 1)‖ ^
    (1 / ((n + 1 : ℕ) : ℝ))) Filter.atTop (𝓝 0)

def NoNonzeroEigenvalue : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (z : 𝕜),
  z ≠ 0 → ∀ f : Space 𝕜, VolterraValue 𝕜 f = z • f → f = 0

/-- Index zero is 1; indices 2n+1 and 2n+2 are cosine and sine
at the positive integer frequency n+1. -/
def trigFunction (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 1 else if n % 2 = 1 then
    Real.sqrt 2 * Real.cos (2 * Real.pi * (((n + 1) / 2 : ℕ) : ℝ) * t)
  else Real.sqrt 2 * Real.sin (2 * Real.pi * ((n / 2 : ℕ) : ℝ) * t)

/-- Explicit representatives prevent an arbitrary basis with a matching sum
from being substituted for the ordinary trigonometric basis. -/
def TrigonometricDiagonal : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∃ b : HilbertBasis ℕ 𝕜 (Space 𝕜),
    (∀ n, (b n : ℝ → 𝕜) =ᵐ[intervalMeasure] fun t => (trigFunction n t : 𝕜)) ∧
    (∀ n, inner 𝕜 (b n) (VolterraValue 𝕜 (b n)) = if n = 0 then 1 / 2 else 0) ∧
    HasSum (fun n => inner 𝕜 (b n) (VolterraValue 𝕜 (b n))) (1 / 2)

/-- On the complexification, some orthonormal-basis diagonal families do
not even have an unordered sum. This rules out a basis-independent diagonal
trace for this operator. The real diagonal sum alone need not depend on basis. -/
def NotBasisIndependentTrace : Prop :=
  ¬ ∃ τ : ℂ, ∀ b : HilbertBasis ℕ ℂ (Space ℂ),
    HasSum (fun n => inner ℂ (b n) (VolterraValue ℂ (b n))) τ

/-- This diagonal sum has no trace-class operator-trace interpretation.
It does not assert that two real bases have different diagonal sums. -/
def Counterexample : Prop := IntegralFormula ∧ HilbertSchmidt ∧ Compact ∧
  SingularValues ∧ NotTraceClass ∧ ZeroSpectrum ∧ Quasinilpotent ∧ NoNonzeroEigenvalue ∧
  TrigonometricDiagonal ∧ NotBasisIndependentTrace

end ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec
