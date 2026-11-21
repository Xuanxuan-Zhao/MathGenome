import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
Independent specification of `K07.05.centralizers_normalizers`
(paper.tex:878–890, chapters/M07.05.tex:62–74).

The canonical objects are `Subgroup.centralizer S` and `Subgroup.normalizer S`.
Their carriers are identified with the two displayed source sets, using the
image under `s ↦ g * s * g⁻¹` for `gSg⁻¹`. In particular the normalizer
requires equality of sets, rather than only preservation in one direction.
All statements concern arbitrary groups and arbitrary (possibly empty) subsets.
For a subgroup `H`, `H.subgroupOf (Subgroup.normalizer (H : Set G))` is its
realization inside its normalizer, with exactly the inherited group operations.
No finiteness, commutativity, or nontriviality hypothesis is imposed.
-/

namespace Specs.D07.Ch05.CentralizersNormalizers

universe u

def CentralizerCarrier : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G),
    (Subgroup.centralizer S : Set G) = {g | ∀ s ∈ S, g * s = s * g}

def NormalizerCarrier : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G),
    (Subgroup.normalizer S : Set G) =
      {g | (fun s => g * s * g⁻¹) '' S = S}

def CentralizerIsSubgroup : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G),
    ∃ C : Subgroup G, (C : Set G) = {g | ∀ s ∈ S, g * s = s * g}

def NormalizerIsSubgroup : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G),
    ∃ N : Subgroup G, (N : Set G) =
      {g | (fun s => g * s * g⁻¹) '' S = S}

def CentralizerLeNormalizer : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G),
    Subgroup.centralizer S ≤ Subgroup.normalizer S

def SubgroupLeNormalizer : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    H ≤ Subgroup.normalizer (H : Set G)

def NormalInNormalizer : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal

def NormalIffNormalizerEqTop : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    H.Normal ↔ Subgroup.normalizer (H : Set G) = ⊤

end Specs.D07.Ch05.CentralizersNormalizers
