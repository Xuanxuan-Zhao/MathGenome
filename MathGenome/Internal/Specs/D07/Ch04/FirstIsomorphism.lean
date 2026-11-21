import MathGenome.Internal.Specs.D07.Ch01.InjectiveKernel
import MathGenome.Internal.Specs.D07.Ch04.QuotientUniversalProperty

/-!
Independent specification of `K07.04.first_isomorphism`, paper.tex:691–700.

The kernel and image are the canonical subgroups from `KernelImage`.
The kernel is normal for every homomorphism, so the quotient uses its
canonical group structure without any extra hypothesis. The projection
`QuotientGroup.mk' f.ker` represents the left coset `g ker f`, as established
by the upstream quotient specification. The formulas below specify the
forward maps, in addition to the existence of group isomorphisms.
The source and target are arbitrary groups in possibly different universes;
in particular no finiteness, commutativity, or nontriviality is required.
-/

namespace Specs.D07.Ch04.FirstIsomorphism

universe u v

/-- The quotient by the kernel is isomorphic to the image by the map induced
by the original homomorphism. Coercion from the image subgroup to `H` makes
the representative formula an equality in the original target. -/
def FirstIsomorphism : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    ∃ e : G ⧸ f.ker ≃* f.range,
      ∀ g : G, (e (QuotientGroup.mk' f.ker g) : H) = f g

/-- For a surjective homomorphism the target of the induced isomorphism is
the whole original target group, with the same representative formula. -/
def FirstIsomorphismOfSurjective : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    Function.Surjective f →
      ∃ e : G ⧸ f.ker ≃* H,
        ∀ g : G, e (QuotientGroup.mk' f.ker g) = f g

end Specs.D07.Ch04.FirstIsomorphism
