import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02TopologicalSum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08BoundedInverse

/-!
Independent statements of Theorem `fa2:p1:c08:splitting`, paper.tex 1697–1704.
The scalar field is real or complex, and completeness is in the given norms.
Bounded linear maps are native continuous linear maps. Complementedness uses
exactly the shared topological direct-sum definition, with inherited subspace
topologies. Both equivalences retain their stated hypotheses and include zero
spaces. Range closedness is explicit in the left-inverse conclusion.
-/

namespace ExpandedFA.P1.C08Splitting.Spec

universe u v w

def RightInverseCriterion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F), Function.Surjective T →
      ((∃ S : F →L[𝕜] E, T.comp S = ContinuousLinearMap.id 𝕜 F) ↔
        C02TopologicalSum.Spec.ComplementedValue T.ker)

def LeftInverseCriterion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F), Function.Injective T →
      ((∃ S : F →L[𝕜] E, S.comp T = ContinuousLinearMap.id 𝕜 E) ↔
        IsClosed (T.range : Set F) ∧
          C02TopologicalSum.Spec.ComplementedValue T.range)

end ExpandedFA.P1.C08Splitting.Spec
