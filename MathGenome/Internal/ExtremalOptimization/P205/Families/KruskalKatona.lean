import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.KruskalKatona
import MathGenome.Internal.ExtremalOptimization.P205.Families.ColexInitialShadow

open Finset

namespace P205.Families

/-- Transport the iterated Kruskal--Katona bound from the increasing
enumeration to an arbitrary finite linearly ordered ground set. -/
theorem iterated_shadow_le_of_initial {α : Type*} [LinearOrder α] [Fintype α]
    {k : ℕ} {𝒜 𝒞 : Finset (Finset α)}
    (h𝒜 : ∀ A ∈ 𝒜, A.card = k) (hc : 𝒞.card ≤ 𝒜.card)
    (h𝒞 : Finset.Colex.IsInitSeg 𝒞 k) (j : ℕ) :
    ((Finset.shadow^[j]) 𝒞).card ≤ ((Finset.shadow^[j]) 𝒜).card := by
  let e := (increasingEnumeration α).symm
  have hsized : (mapFamily e 𝒜 : Set (Finset (Fin (Fintype.card α)))).Sized k := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    rw [card_image_of_injective _ e.injective]
    exact h𝒜 t ht
  have hcard : (mapFamily e 𝒞).card ≤ (mapFamily e 𝒜).card := by
    change (mapFamily e.toEmbedding 𝒞).card ≤ (mapFamily e.toEmbedding 𝒜).card
    simpa only [mapFamily_card e.toEmbedding] using hc
  have hinit : Finset.Colex.IsInitSeg (mapFamily e 𝒞) k :=
    (mapFamily_isInitSeg e).mpr h𝒞
  have h := Finset.iterated_kk (k := j) hsized hcard hinit
  change ((Finset.shadow^[j]) (mapFamily e.toEmbedding 𝒞)).card ≤
    ((Finset.shadow^[j]) (mapFamily e.toEmbedding 𝒜)).card at h
  rw [← shadow_transport _ _ e.toEmbedding 𝒞 j,
    ← shadow_transport _ _ e.toEmbedding 𝒜 j] at h
  simpa only [mapFamily_card e.toEmbedding] using h

/-- Theorem 2.7: the colex segment of size `m` minimizes every lower
shadow through rank zero. `initialColex` is the shared canonical `I_k(m)`.-/
theorem kruskal_katona : Spec.KruskalKatona := by
  intro α _ _ k m 𝒜 _hk _hkn h𝒜 hm j _hj
  apply iterated_shadow_le_of_initial h𝒜 _ (initial_properties α k m).1 j
  rw [(initial_properties α k m).2, hm]
  exact Nat.min_le_left _ _

end P205.Families
