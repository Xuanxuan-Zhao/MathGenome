import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.Lidskii

/-! Spectral moments in the proof of paper.tex:11153–11163. The index is the
complete upstream algebraic multiset of T, not that of its power. -/
noncomputable section
universe u
namespace ExpandedFA.FredholmDeterminant.HilbertSchmidtPowerTraces.Spec
open TraceIdeals

def TraceClassPowers : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue T →
    ∀ n : ℕ, TraceClassDefinitions.Spec.IsTraceClassValue (T ^ (n + 2))

def PowerTraces : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue T →
    ∀ n : ℕ,
      Summable (fun i : Lidskii.Spec.EigenvalueIndex T =>
        ‖Lidskii.Spec.eigenvalue T i ^ (n + 2)‖) ∧
      HasSum (fun i : Lidskii.Spec.EigenvalueIndex T =>
        Lidskii.Spec.eigenvalue T i ^ (n + 2))
        (TraceClassDefinitions.Spec.TraceValue (T ^ (n + 2)))

def FullConclusion : Prop := TraceClassPowers.{u} ∧ PowerTraces.{u}

end ExpandedFA.FredholmDeterminant.HilbertSchmidtPowerTraces.Spec
