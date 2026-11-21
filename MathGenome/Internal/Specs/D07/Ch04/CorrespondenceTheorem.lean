import MathGenome.Internal.Specs.D07.Ch01.KernelImage
import MathGenome.Internal.Specs.D07.Ch04.QuotientConstruction
import Mathlib.GroupTheory.Index

/-!
Independent specification of `K07.04.correspondence_theorem`, paper.tex:710–719.

The subgroup denoted by H/N is the image `H.map (QuotientGroup.mk' N)`.
Inverse image is `Subgroup.comap`. The order equivalence specifies both maps,
so it includes preservation of inclusion in both directions. Normality is
normality in G or G/N respectively, not merely normality inside H.

The last quotient is only a left-coset *set*: H is not assumed normal.
Its representative formula makes the bijection canonical. Finiteness is
stated for the coset spaces, with no finiteness assumption on G. Natural
indices are compared only under that finite-coset-space hypothesis.
-/

namespace Specs.D07.Ch04.CorrespondenceTheorem

universe u

def InverseImageContains : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)), N ≤ L.comap (QuotientGroup.mk' N)

def ImageInverseImage : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)),
    (L.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = L

def InverseImageImage : Prop :=
  ∀ (G : Type u) [Group G] (N H : Subgroup G) [N.Normal], N ≤ H →
    (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = H

def SubgroupCorrespondence : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    ∃ e : Subgroup (G ⧸ N) ≃o Set.Ici N,
      (∀ L : Subgroup (G ⧸ N), (e L).val = L.comap (QuotientGroup.mk' N)) ∧
      (∀ H : Set.Ici N, e.symm H = H.val.map (QuotientGroup.mk' N))

def InverseImageNormalIff : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)),
    (L.comap (QuotientGroup.mk' N)).Normal ↔ L.Normal

def ImageNormalIff : Prop :=
  ∀ (G : Type u) [Group G] (N H : Subgroup G) [N.Normal] (_hNH : N ≤ H),
    (H.map (QuotientGroup.mk' N)).Normal ↔ H.Normal

def CosetBijection : Prop :=
  ∀ (G : Type u) [Group G] (N H : Subgroup G) [N.Normal], N ≤ H →
    ∃ e : (G ⧸ H) ≃ ((G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)),
      ∀ g : G, e (QuotientGroup.mk g) =
        QuotientGroup.mk (QuotientGroup.mk' N g)

def CosetFiniteIff : Prop :=
  ∀ (G : Type u) [Group G] (N H : Subgroup G) [N.Normal], N ≤ H →
    (Finite (G ⧸ H) ↔ Finite ((G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)))

def FiniteIndicesAgree : Prop :=
  ∀ (G : Type u) [Group G] (N H : Subgroup G) [N.Normal], N ≤ H →
    [Finite (G ⧸ H)] → H.index = (H.map (QuotientGroup.mk' N)).index

end Specs.D07.Ch04.CorrespondenceTheorem
