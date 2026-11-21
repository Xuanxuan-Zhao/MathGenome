import MathGenome.Internal.Specs.D07.Ch18.SylowNormalizer

/-!
Normalizer of a Sylow normalizer, `K07.18.sylow_normalizer`.

The library theorem applies to groups with finitely many Sylow subgroups.
Ambient finiteness supplies that hypothesis here. Its normalizers use the
same ambient group G, and no nilpotence or normality assumption is needed.
-/

namespace D07.Ch18.SylowNormalizer

universe u

theorem normalizer_normalizer (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Sylow p G) :
    Subgroup.normalizer (Subgroup.normalizer (P : Set G) : Set G) =
      Subgroup.normalizer (P : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  exact P.normalizer_normalizer

end D07.Ch18.SylowNormalizer
