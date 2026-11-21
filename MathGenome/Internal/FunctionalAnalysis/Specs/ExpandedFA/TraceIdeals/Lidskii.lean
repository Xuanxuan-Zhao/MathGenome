import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.WeylProducts

/-! Lidskii's theorem, paper.tex:11525–11532. The scalar field is complex,
and the Hilbert space may be zero or nonseparable. The spectral sum below
uses one index for EACH algebraic occurrence of EACH actual nonzero eigenvalue.
It is an unordered sum; absolute summability makes it equal to every ordered
listing with algebraic multiplicity. No normality premise is present. -/
noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.Lidskii.Spec

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The nonzero point spectrum, without imposing a choice of ordering. -/
abbrev NonzeroEigenvalues (T : H →L[ℂ] H) :=
  {z : ℂ // z ≠ 0 ∧ Module.End.HasEigenvalue T.toLinearMap z}

/-- Each scalar occurs exactly `dim maxGenEigenspace` times. The upstream
compact spectral theorem proves this dimension is finite at nonzero scalars. -/
def EigenvalueIndex (T : H →L[ℂ] H) :=
  Σ z : NonzeroEigenvalues T, Fin (WeylProducts.Spec.algebraicMultiplicity T z.val)

def eigenvalue (T : H →L[ℂ] H) (i : EigenvalueIndex T) : ℂ := i.1.val

/-- The full conclusion for every trace-class operator. The first conjunct is
absolute convergence, and the second is the trace identity with algebraic
multiplicity. Neither a spectral decomposition nor a summation certificate
is an assumption. -/
def Lidskii : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceClassDefinitions.Spec.IsTraceClassValue T →
      Summable (fun i : EigenvalueIndex T => ‖eigenvalue T i‖) ∧
      HasSum (eigenvalue T) (TraceClassDefinitions.Spec.TraceValue T)

/-- The absolute-convergence conclusion, also with the Weyl trace-norm bound. -/
def AbsoluteEigenvalueSum : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceClassDefinitions.Spec.IsTraceClassValue T →
      Summable (fun i : EigenvalueIndex T => ‖eigenvalue T i‖) ∧
      (∑' i : EigenvalueIndex T, ‖eigenvalue T i‖) ≤
        TraceClassDefinitions.Spec.TraceNormValue T

end ExpandedFA.TraceIdeals.Lidskii.Spec
