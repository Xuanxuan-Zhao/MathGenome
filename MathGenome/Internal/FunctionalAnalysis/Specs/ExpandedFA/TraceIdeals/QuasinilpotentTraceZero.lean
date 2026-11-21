import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! The quasinilpotent stage of `fa2:p2:lidskii`, paper.tex:11534–11561.
The Hilbert space is arbitrary, including zero and nonseparable spaces.
Spectrum containment, rather than equality, retains the zero-space case.
The trace and trace-class predicate are exactly the shared upstream objects. -/
noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.QuasinilpotentTraceZero.Spec

def TraceVanishes : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : H →L[ℂ] H),
    TraceClassDefinitions.Spec.IsTraceClassValue Q →
    spectrum ℂ Q ⊆ {0} → TraceClassDefinitions.Spec.TraceValue Q = 0

end ExpandedFA.TraceIdeals.QuasinilpotentTraceZero.Spec
