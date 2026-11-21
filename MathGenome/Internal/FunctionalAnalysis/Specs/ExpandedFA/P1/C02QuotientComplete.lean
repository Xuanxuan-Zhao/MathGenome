import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for `fa2:p1:c02:quotient-complete`, paper.tex
lines 404–408. The quotient is the algebraic quotient by the original
closed subspace, with exactly the distance norm fixed upstream.
Banach completeness means that every norm Cauchy sequence converges.
Both scalar fields and the zero space are included.
-/

namespace ExpandedFA.P1.C02QuotientComplete.Spec

/-- A Banach space modulo a closed linear subspace is Banach in its
distance quotient norm. -/
def QuotientComplete : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    letI := C02QuotientNorm.Spec.quotientNormedGroupValue 𝕜 E M hM
    C01Banach.Spec.IsBanachSpaceValue E →
      C01Banach.Spec.IsBanachSpaceValue (E ⧸ M)

/-- Every Cauchy sequence in the quotient converges to an actual coset. -/
def QuotientCauchyConverges : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    letI := C02QuotientNorm.Spec.quotientNormedGroupValue 𝕜 E M hM
    C01Banach.Spec.IsBanachSpaceValue E →
      ∀ z : ℕ → E ⧸ M,
        C01Banach.Spec.NormCauchySequenceValue (E ⧸ M) z →
          ∃ x : E,
            C01Banach.Spec.NormConvergesToValue (E ⧸ M) z (M.mkQ x)

end ExpandedFA.P1.C02QuotientComplete.Spec
