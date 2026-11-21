import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.PeriodicConvolution
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions

/-! Operator ideals for the canonical L¹ convolution operator on the circle,
with normalized Haar measure. Membership in L² concerns the original L¹
kernel's a.e. class. No continuity or pointwise sign hypothesis is imposed. -/
noncomputable section
open MeasureTheory

namespace ExpandedFA.Models.PeriodicConvolutionIdealsSpec
open PeriodicConvolutionSpec
open TraceIdeals.HilbertSchmidtDefinitions.Spec
open TraceIdeals.TraceClassDefinitions.Spec

def HilbertSchmidtCriterion : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T),
    IsHilbertSchmidtValue (operatorValue k) ↔ MemLp (k : Circle T → ℂ) 2 (Haar T)

/-- The finite Hilbert–Schmidt norm equals the L² norm of the same kernel. -/
def HilbertSchmidtNorm : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T)
    (hk : MemLp (k : Circle T → ℂ) 2 (Haar T))
    (hK : IsHilbertSchmidtValue (operatorValue k)),
    HilbertSchmidtNormValue ⟨operatorValue k, hK⟩ = ‖hk.toLp k‖

/-- Absolute summability is an additional condition, also for continuous kernels. -/
def TraceClassCriterion : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T),
    IsTraceClassValue (operatorValue k) ↔ Summable (fun n : ℤ => ‖fourierCoeff k n‖)

end ExpandedFA.Models.PeriodicConvolutionIdealsSpec
