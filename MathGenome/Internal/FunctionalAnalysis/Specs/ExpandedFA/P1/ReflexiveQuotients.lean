import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Restriction
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-!
The quotient clause of `fa2:p1:c14:stability`, paper.tex:2767–2796.
The quotient is by the original closed scalar-linear subspace, with the
distance quotient norm. Reflexivity means surjectivity of its canonical
evaluation map into the continuous scalar-linear bidual. No separability,
nontriviality, or norm-minimizing representative is assumed.
-/

namespace ExpandedFA.P1.ReflexiveQuotients.Spec

universe u v

/-- The quotient dual is identified isometrically with the annihilator by
composition with the quotient projection, with its action specified. -/
def QuotientDualIsometry : Prop :=
  C04DualMaps.Spec.QuotientDualIsometry.{u, v}

/-- A closed linear quotient of a reflexive real or complex Banach space
is canonically reflexive in the distance quotient norm. -/
def QuotientReflexive : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
      letI : IsClosed (M : Set E) := hM
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (E ⧸ M)

end ExpandedFA.P1.ReflexiveQuotients.Spec
