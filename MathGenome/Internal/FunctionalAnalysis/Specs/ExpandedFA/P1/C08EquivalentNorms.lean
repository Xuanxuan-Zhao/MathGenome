import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08BoundedInverse

/-!
Independent statement of `fa2:p1:c08:equivalent-norms`, paper.tex 1647–1653.
Both norms are definite seminorms on the same original vector space. The
shared norm interface constructs their norm metrics, uniformities and topologies;
each completeness assumption refers to its own displayed norm. No topology is
fixed in advance, and neither the space nor the hypothesis constant is required
to be nonzero. `RCLike` includes both manuscript scalar fields.
-/

namespace ExpandedFA.P1.C08EquivalentNorms.Spec

open ExpandedFA.P1.C01Norm

universe u v

/-- A one-sided comparison of complete norms implies mutual positive bounds
and equality of the norm topologies on the original vector space. -/
def EquivalentCompleteNorms : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p q : Seminorm 𝕜 E)
    (hp : ∀ x, p x = 0 → x = 0) (hq : ∀ x, q x = 0 → x = 0),
    @CompleteSpace E (normedGroup p hp).toUniformSpace →
    @CompleteSpace E (normedGroup q hq).toUniformSpace →
    ∀ C : ℝ, (∀ x, q x ≤ C * p x) →
      ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
        (∀ x, q x ≤ A * p x) ∧ (∀ x, p x ≤ D * q x) ∧
        (normedGroup p hp).toUniformSpace.toTopologicalSpace =
          (normedGroup q hq).toUniformSpace.toTopologicalSpace

end ExpandedFA.P1.C08EquivalentNorms.Spec
