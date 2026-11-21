import MathGenome.Internal.Specs.D07.Ch04.CorrespondenceTheorem
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
Independent specification of `K07.04.third_isomorphism`, paper.tex:718–730.

As in the subgroup correspondence, `M/N` means the subgroup
`M.map (QuotientGroup.mk' N)` of `G/N`. Both N and M are explicitly
normal in G. The library's normal-image instance supplies the group
structure on the outer quotient; its normality is also a separate
conclusion below, rather than an additional hypothesis.

The isomorphism is multiplicative and is prescribed on every double
coset. There are no finiteness, commutativity, or nontriviality assumptions.
In particular N = M, trivial subgroups, and the trivial group are allowed.
-/

namespace Specs.D07.Ch04.ThirdIsomorphism

universe u

/-- The subgroup M/N is normal in G/N. -/
def QuotientSubgroupNormal : Prop :=
  ∀ (G : Type u) [Group G] (N M : Subgroup G) [N.Normal] [M.Normal],
    N ≤ M → (M.map (QuotientGroup.mk' N)).Normal

/-- The third isomorphism theorem, with its canonical value on representatives.
The displayed formula also expresses compatibility with both projections. -/
def CanonicalIsomorphism : Prop :=
  ∀ (G : Type u) [Group G] (N M : Subgroup G) [N.Normal] [M.Normal],
    N ≤ M →
      ∃ e : ((G ⧸ N) ⧸ M.map (QuotientGroup.mk' N)) ≃* (G ⧸ M),
        ∀ g : G,
          e (QuotientGroup.mk' (M.map (QuotientGroup.mk' N))
            (QuotientGroup.mk' N g)) = QuotientGroup.mk' M g

end Specs.D07.Ch04.ThirdIsomorphism
