import Mathlib.GroupTheory.Sylow

/-!
Independent statement of `K07.18.sylow_normalizer`, paper.tex:5087–5103.

`Sylow p G` is a maximal p-subgroup. In a finite group this agrees with
the full p-part cardinality definition, as established in the upstream
Sylow-definition entry. `Subgroup.normalizer S` consists of the elements
whose conjugation preserves the set `S`. Both normalizers below are in G.
The prime need not divide the group order, and the trivial group is allowed.
-/

namespace Specs.D07.Ch18.SylowNormalizer

universe u

/-- The normalizer of any Sylow subgroup of a finite group is self-normalizing. -/
def NormalizerNormalizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    ∀ P : Sylow p G,
      Subgroup.normalizer (Subgroup.normalizer (P : Set G) : Set G) =
        Subgroup.normalizer (P : Set G)

end Specs.D07.Ch18.SylowNormalizer
