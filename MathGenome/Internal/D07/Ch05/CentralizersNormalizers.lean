import MathGenome.Internal.Specs.D07.Ch05.CentralizersNormalizers

/-!
Centralizers and normalizers (`K07.05.centralizers_normalizers`).
The carrier bridges check the source's multiplication order and set equality
against the canonical Mathlib subgroups. The normality statement is taken in
the normalizer itself, without assuming normality in the original group.
-/

namespace D07.Ch05.CentralizersNormalizers

universe u

theorem centralizer_carrier (G : Type u) [Group G] (S : Set G) :
    (Subgroup.centralizer S : Set G) = {g | ∀ s ∈ S, g * s = s * g} := by
  ext g
  exact forall₂_congr fun _ _ => eq_comm

theorem normalizer_carrier (G : Type u) [Group G] (S : Set G) :
    (Subgroup.normalizer S : Set G) =
      {g | (fun s => g * s * g⁻¹) '' S = S} := by
  ext g
  exact Subgroup.mem_normalizer_iff_conj_image_eq

theorem centralizer_is_subgroup (G : Type u) [Group G] (S : Set G) :
    ∃ C : Subgroup G, (C : Set G) = {g | ∀ s ∈ S, g * s = s * g} :=
  ⟨Subgroup.centralizer S, centralizer_carrier G S⟩

theorem normalizer_is_subgroup (G : Type u) [Group G] (S : Set G) :
    ∃ N : Subgroup G, (N : Set G) =
      {g | (fun s => g * s * g⁻¹) '' S = S} :=
  ⟨Subgroup.normalizer S, normalizer_carrier G S⟩

theorem centralizer_le_normalizer (G : Type u) [Group G] (S : Set G) :
    Subgroup.centralizer S ≤ Subgroup.normalizer S :=
  Subgroup.centralizer_le_normalizer S

theorem subgroup_le_normalizer (G : Type u) [Group G] (H : Subgroup G) :
    H ≤ Subgroup.normalizer (H : Set G) :=
  H.le_normalizer

theorem normal_in_normalizer (G : Type u) [Group G] (H : Subgroup G) :
    (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal :=
  Subgroup.normal_in_normalizer

theorem normal_iff_normalizer_eq_top (G : Type u) [Group G] (H : Subgroup G) :
    H.Normal ↔ Subgroup.normalizer (H : Set G) = ⊤ :=
  Subgroup.normalizer_eq_top_iff.symm

end D07.Ch05.CentralizersNormalizers
