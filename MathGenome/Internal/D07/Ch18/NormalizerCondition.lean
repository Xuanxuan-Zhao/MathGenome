import MathGenome.Internal.Specs.D07.Ch18.NormalizerCondition

/-!
The normalizer condition for arbitrary nilpotent groups, paper.tex:5073–5087.
Mathlib's theorem uses exactly upper-central-series termination and requires
no finiteness assumption. Its `NormalizerCondition` unfolds to the strict
inclusion asserted here for every proper subgroup.
-/

namespace D07.Ch18.NormalizerCondition

universe u

theorem normalizer_condition (G : Type u) [Group G] (hG : Group.IsNilpotent G)
    (H : Subgroup G) (hH : H < ⊤) : H < Subgroup.normalizer (H : Set G) :=
  @Group.normalizerCondition_of_isNilpotent G _ hG H hH

end D07.Ch18.NormalizerCondition
