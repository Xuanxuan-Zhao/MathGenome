import MathGenome.Internal.D07.Ch01.KernelImage
import MathGenome.Internal.D07.Ch04.QuotientConstruction
import MathGenome.Internal.Specs.D07.Ch04.CorrespondenceTheorem

/-!
The subgroup correspondence, paper.tex:710–719. The projection's preimage
and image give inverse order maps; surjectivity also reflects normality.
For arbitrary H containing N, the map of left-coset sets sends gH to
(gN)(H/N). Its injectivity uses the preimage-image identity, and its
surjectivity uses surjectivity of the projection. No group structure on
G/H or on the outer coset space is used.
-/

namespace D07.Ch04.CorrespondenceTheorem

universe u

theorem inverse_image_contains (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)) : N ≤ L.comap (QuotientGroup.mk' N) :=
  QuotientGroup.le_comap_mk' N L

theorem image_inverse_image (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)) :
    (L.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = L :=
  (QuotientGroup.comapMk'OrderIso N).symm_apply_apply L

theorem inverse_image_image (G : Type u) [Group G] (N H : Subgroup G) [N.Normal]
    (hNH : N ≤ H) :
    (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = H := by
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hNH]

theorem subgroup_correspondence (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    ∃ e : Subgroup (G ⧸ N) ≃o Set.Ici N,
      (∀ L : Subgroup (G ⧸ N), (e L).val = L.comap (QuotientGroup.mk' N)) ∧
      (∀ H : Set.Ici N, e.symm H = H.val.map (QuotientGroup.mk' N)) :=
  ⟨QuotientGroup.comapMk'OrderIso N, fun _ => rfl, fun _ => rfl⟩

theorem inverse_image_normal_iff (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)) :
    (L.comap (QuotientGroup.mk' N)).Normal ↔ L.Normal :=
  Subgroup.normal_comap_iff_of_surjective
    (D07.Ch04.QuotientConstruction.projection_surjective G N)

theorem image_normal_iff (G : Type u) [Group G] (N H : Subgroup G) [N.Normal]
    (hNH : N ≤ H) :
    (H.map (QuotientGroup.mk' N)).Normal ↔ H.Normal := by
  rw [← inverse_image_normal_iff G N, inverse_image_image G N H hNH]

theorem coset_bijection (G : Type u) [Group G] (N H : Subgroup G) [N.Normal]
    (hNH : N ≤ H) :
    ∃ e : (G ⧸ H) ≃ ((G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)),
      ∀ g : G, e (QuotientGroup.mk g) =
        QuotientGroup.mk (QuotientGroup.mk' N g) := by
  let π := QuotientGroup.mk' N
  let f : (G ⧸ H) → ((G ⧸ N) ⧸ H.map π) :=
    Quotient.map' π (fun a b hab => by
      apply QuotientGroup.leftRel_apply.mpr
      simpa only [map_mul, map_inv] using
        Subgroup.mem_map_of_mem π (QuotientGroup.leftRel_apply.mp hab))
  have hinj : Function.Injective f := by
    intro a b
    refine Quotient.inductionOn₂' a b (fun a b hab => ?_)
    have hmem : a⁻¹ * b ∈ (H.map π).comap π := by
      change π (a⁻¹ * b) ∈ H.map π
      simpa only [map_mul, map_inv] using QuotientGroup.eq.mp hab
    rw [inverse_image_image G N H hNH] at hmem
    exact QuotientGroup.eq.mpr hmem
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, rfl⟩ := D07.Ch04.QuotientConstruction.projection_surjective G N r
    exact ⟨QuotientGroup.mk g, rfl⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem coset_finite_iff (G : Type u) [Group G] (N H : Subgroup G) [N.Normal]
    (hNH : N ≤ H) :
    Finite (G ⧸ H) ↔ Finite ((G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)) := by
  obtain ⟨e, _⟩ := coset_bijection G N H hNH
  exact e.finite_iff

theorem finite_indices_agree (G : Type u) [Group G] (N H : Subgroup G) [N.Normal]
    (hNH : N ≤ H) [Finite (G ⧸ H)] :
    H.index = (H.map (QuotientGroup.mk' N)).index := by
  obtain ⟨e, _⟩ := coset_bijection G N H hNH
  exact Nat.card_congr e

end D07.Ch04.CorrespondenceTheorem
