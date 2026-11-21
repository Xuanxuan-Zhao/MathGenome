import MathGenome.Internal.D07.Ch04.CorrespondenceTheorem
import MathGenome.Internal.Specs.D07.Ch04.ThirdIsomorphism

/-!
The third isomorphism theorem (`K07.04.third_isomorphism`, paper.tex:718–730).
The subgroup M/N is the image of M under the canonical projection.
Its normality follows from the upstream correspondence theorem. Mathlib's
third-isomorphism equivalence uses exactly this subgroup, and its forward
map is the iterated quotient lift, giving the stated representative formula.
-/

namespace D07.Ch04.ThirdIsomorphism

universe u

theorem quotient_subgroup_normal (G : Type u) [Group G]
    (N M : Subgroup G) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    (M.map (QuotientGroup.mk' N)).Normal :=
  (D07.Ch04.CorrespondenceTheorem.image_normal_iff G N M hNM).mpr
    (inferInstance : M.Normal)

theorem third_isomorphism (G : Type u) [Group G]
    (N M : Subgroup G) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    ∃ e : ((G ⧸ N) ⧸ M.map (QuotientGroup.mk' N)) ≃* (G ⧸ M),
      ∀ g : G,
        e (QuotientGroup.mk' (M.map (QuotientGroup.mk' N))
          (QuotientGroup.mk' N g)) = QuotientGroup.mk' M g := by
  exact ⟨QuotientGroup.quotientQuotientEquivQuotient N M hNM,
    fun g => QuotientGroup.quotientQuotientEquivQuotient_apply_mk N M hNM g⟩

end D07.Ch04.ThirdIsomorphism
