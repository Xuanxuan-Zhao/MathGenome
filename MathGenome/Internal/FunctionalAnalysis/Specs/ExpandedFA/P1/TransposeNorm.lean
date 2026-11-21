import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators

/-!
Independent specification of the transpose-norm clause of
`fa2:p1:c05:bidual-isometry`, paper.tex:961–989.
The transpose is the shared map `f ↦ f.comp T` on continuous scalar-linear
duals, with their native operator norms. Both scalar fields are included;
neither space is assumed complete or nonzero.
-/

namespace ExpandedFA.P1.TransposeNorm.Spec

universe u v w

/-- Every bounded scalar-linear map has the same norm as its Banach transpose. -/
def BanachTransposeNormEquality : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ‖C04Annihilators.Spec.BanachTransposeValue 𝕜 E F T‖ = ‖T‖

end ExpandedFA.P1.TransposeNorm.Spec
