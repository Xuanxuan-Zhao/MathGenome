import MathGenome.Internal.Specs.D07.Ch05.CentralizersNormalizers
import MathGenome.Internal.Specs.D07.Ch18.NilpotenceCriteria

/-!
Independent specification of `K07.18.normalizer_condition`, paper.tex:5073–5087.

Nilpotence means that some upper central term is the whole group, as in
the prerequisite `NilpotenceCriteria` specification and `Group.IsNilpotent`.
The normalizer is the canonical subgroup defined by equality under conjugation.
Both inequalities are strict subgroup inclusions. There is no finiteness or
nontriviality assumption on either the ambient group or the subgroup.
-/

namespace Specs.D07.Ch18.NormalizerCondition

universe u

def StrictNormalizerCondition : Prop :=
  ∀ (G : Type u) [Group G], Group.IsNilpotent G →
    ∀ H : Subgroup G, H < ⊤ → H < Subgroup.normalizer (H : Set G)

end Specs.D07.Ch18.NormalizerCondition
