import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.ColexInitialShadow
import Mathlib.Combinatorics.SetFamily.KruskalKatona

open Finset
open scoped FinsetFamily symmDiff
namespace P205.Families

/-- The paper's I_k(m), using the shared canonical construction in the Specs. -/
noncomputable def I : Spec.InitialColexType := @initialColex

lemma mem_colexLayer {α : Type*} [LinearOrder α] [Fintype α]
    {k : ℕ} {s : Colex (Finset α)} :
    s ∈ colexLayer α k ↔ (ofColex s).card = k := by
  simp only [colexLayer, mem_image, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro h
    exact ⟨ofColex s, h, by simp⟩

lemma card_colexLayer (α : Type*) [LinearOrder α] [Fintype α] (k : ℕ) :
    (colexLayer α k).card = Nat.choose (Fintype.card α) k := by
  rw [colexLayer, card_image_of_injective _ toColex.injective, card_powersetCard, card_univ]

theorem initial_properties : Spec.InitialProperties := by
  intro α _ _ k m
  let L := colexLayer α k
  let q := min m L.card
  let e := L.orderEmbOfCardLe (Nat.min_le_right m L.card)
  have he (i : Fin q) : (ofColex (e i)).card = k :=
    mem_colexLayer.mp (L.orderEmbOfCardLe_mem _ i)
  constructor
  · constructor
    · intro s hs
      obtain ⟨_, hx, rfl⟩ := mem_image.mp hs
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact he i
    · intro s t hs ht
      obtain ⟨_, hx, rfl⟩ := mem_image.mp hs
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      let j := (L.orderIsoOfFin rfl).symm ⟨toColex t, mem_colexLayer.mpr ht.2⟩
      have hej : L.orderEmbOfFin rfl j = toColex t := by
        exact congrArg Subtype.val ((L.orderIsoOfFin rfl).apply_symm_apply _)
      have hji : j < Fin.castLE (Nat.min_le_right m L.card) i := by
        apply (L.orderEmbOfFin rfl).lt_iff_lt.mp
        simpa [e, L, Finset.orderEmbOfCardLe, hej] using ht.1
      have hjq : j.val < q := (show j.val < i.val from hji).trans i.isLt
      apply mem_image.mpr
      refine ⟨toColex t, ?_, rfl⟩
      apply mem_image.mpr
      refine ⟨⟨j.val, hjq⟩, mem_univ _, ?_⟩
      exact hej
  · change ((univ.image e).image ofColex).card = _
    rw [card_image_of_injective _ ofColex.injective,
      card_image_of_injective _ e.injective, card_univ, Fintype.card_fin]
    exact congrArg (min m) (card_colexLayer α k)

theorem initial_unique : Spec.InitialUnique := by
  intro α _ _ k m 𝒜 hm h𝒜 hcard
  have hi := initial_properties α k m
  have hc : (initialColex α k m).card = 𝒜.card := by
    rw [hi.2, Nat.min_eq_left hm, hcard]
  rcases h𝒜.total hi.1 with h | h
  · exact eq_of_subset_of_card_le h hc.le
  · exact (eq_of_subset_of_card_le h hc.ge).symm

theorem shadow_initial : Spec.ShadowInitial := by
  intro α _ _ k 𝒜 h
  exact h.shadow

theorem shadow_endpoint : Spec.ShadowEndpoint := by
  intro α _ _ k 𝒜 S hS h𝒜 hSm hmax
  have hEq : 𝒜 = Finset.Colex.initSeg S := by
    ext A
    rw [Finset.Colex.mem_initSeg]
    constructor
    · intro hA
      exact ⟨(h𝒜.1 hSm).trans (h𝒜.1 hA).symm, hmax A hA⟩
    · rintro ⟨hcard, hle⟩
      rcases hle.eq_or_lt with heq | hlt
      · simpa only [toColex_inj.mp heq] using hSm
      · exact h𝒜.2 hSm ⟨hlt, hcard.symm.trans (h𝒜.1 hSm)⟩
  rw [hEq, Finset.Colex.shadow_initSeg hS]

theorem iterated_initial : Spec.IteratedInitial := by
  intro α _ _ k j 𝒜 h
  induction j with
  | zero => simpa using h
  | succ j ih =>
    simpa [Function.iterate_succ_apply', Nat.sub_sub] using ih.shadow

theorem greatest_difference : Spec.GreatestDifference := by
  intro α _ A B h
  rw [Finset.Colex.toColex_lt_toColex_iff_max'_mem]
  exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨h, hx⟩⟩

theorem linear_colex : Spec.LinearColex := by
  intro α _ A B
  simpa only [toColex_inj] using lt_trichotomy (toColex A) (toColex B)

theorem colex_transport : Spec.ColexTransport := by
  intro α β _ _ e A B
  exact ⟨Finset.Colex.toColex_image_le_toColex_image e.strictMono,
    Finset.Colex.toColex_image_lt_toColex_image e.strictMono,
    card_image_of_injective _ e.injective⟩

theorem binary_characterization : Spec.BinaryCharacterization := by
  intro α _ _ A B
  let r : α → ℕ := fun x => ((increasingEnumeration α).symm x).val
  have hr : StrictMono r := Fin.val_strictMono.comp (increasingEnumeration α).symm.strictMono
  have hv (s : Finset α) : ∑ i ∈ s.image r, 2 ^ i = binaryValue s := by
    rw [sum_image]
    · rfl
    · exact fun a _ b _ h => hr.injective h
  constructor
  · rw [← Finset.Colex.toColex_image_le_toColex_image hr,
      ← Finset.geomSum_le_geomSum_iff_toColex_le_toColex (by decide : 2 ≤ 2), hv, hv]
  · rw [← Finset.Colex.toColex_image_lt_toColex_image hr,
      ← Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex (by decide : 2 ≤ 2), hv, hv]

lemma mapFamily_shadow {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (𝒜 : Finset (Finset α)) :
    mapFamily f (Finset.shadow 𝒜) = Finset.shadow (mapFamily f 𝒜) := by
  ext B
  simp only [mapFamily, mem_image, mem_shadow_iff]
  constructor
  · rintro ⟨t, ⟨s, hs, a, ha, rfl⟩, rfl⟩
    exact ⟨s.image f, ⟨s, hs, rfl⟩, f a, mem_image.mpr ⟨a, ha, rfl⟩,
      (image_erase f.injective s a).symm⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    exact ⟨s.erase a, ⟨s, hs, a, ha, rfl⟩, image_erase f.injective s a⟩

theorem shadow_transport : Spec.ShadowTransport := by
  intro α β _ _ f 𝒜 j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply', mapFamily_shadow, ih]

theorem boundary_cases : Spec.BoundaryCases := by
  intro α _ _
  constructor
  · intro k
    have h : initialColex α k 0 = ∅ := card_eq_zero.mp (by
      rw [(initial_properties α k 0).2]
      simp)
    rw [h, shadow_empty]
  · intro 𝒜 h𝒜 hne
    ext t
    rw [mem_singleton]
    constructor
    · intro ht
      obtain ⟨s, hs, a, ha, rfl⟩ := mem_shadow_iff.mp ht
      apply card_eq_zero.mp
      rw [card_erase_of_mem ha, h𝒜.1 hs]
    · rintro rfl
      obtain ⟨s, hs⟩ := hne
      obtain ⟨a, rfl⟩ := card_eq_one.mp (h𝒜.1 hs)
      exact mem_shadow_iff.mpr ⟨{a}, hs, a, mem_singleton_self _, by simp⟩

lemma mapFamily_card {α β : Type*} [DecidableEq β] (f : α ↪ β)
    (𝒜 : Finset (Finset α)) : (mapFamily f 𝒜).card = 𝒜.card :=
  card_image_of_injective _ (Finset.image_injective f.injective)

lemma mapFamily_inverse {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (𝒜 : Finset (Finset α)) :
    mapFamily e.symm (mapFamily e 𝒜) = 𝒜 := by
  simp [mapFamily, image_image, Function.comp_def]

lemma mapFamily_isInitSeg_of {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) {k : ℕ} {𝒜 : Finset (Finset α)}
    (h : Finset.Colex.IsInitSeg 𝒜 k) : Finset.Colex.IsInitSeg (mapFamily e 𝒜) k := by
  constructor
  · intro s hsm
    obtain ⟨a, ha, heq⟩ := (show ∃ A ∈ 𝒜, A.image e = s from mem_image.mp hsm)
    subst s
    rw [card_image_of_injective _ e.injective]
    exact h.1 ha
  · intro s t hsm ht
    obtain ⟨a, ha, heq⟩ := (show ∃ A ∈ 𝒜, A.image e = s from mem_image.mp hsm)
    subst s
    have htcard : (t.image e.symm).card = k := by
      rw [card_image_of_injective _ e.symm.injective, ht.2]
    have htlt : toColex (t.image e.symm) < toColex a := by
      have hx := (Finset.Colex.toColex_image_lt_toColex_image e.symm.strictMono).mpr ht.1
      simpa [image_image, Function.comp_def] using hx
    change t ∈ 𝒜.image (Finset.image e)
    refine mem_image.mpr ⟨t.image e.symm, h.2 ha ⟨htlt, htcard⟩, ?_⟩
    simp [image_image, Function.comp_def]

lemma mapFamily_isInitSeg {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) {k : ℕ} {𝒜 : Finset (Finset α)} :
    Finset.Colex.IsInitSeg (mapFamily e 𝒜) k ↔ Finset.Colex.IsInitSeg 𝒜 k := by
  constructor
  · intro h
    have hx := mapFamily_isInitSeg_of e.symm h
    simpa [mapFamily, image_image, Function.comp_def] using hx
  · exact mapFamily_isInitSeg_of e

theorem segment_transport : Spec.SegmentTransport := by
  intro α β _ _ _ _ e k m 𝒜
  refine ⟨mapFamily_isInitSeg e, ?_⟩
  have ha := mapFamily_isInitSeg_of e (initial_properties α k m).1
  have hb := (initial_properties β k m).1
  have hc : (mapFamily e (initialColex α k m)).card = (initialColex β k m).card := by
    change (Finset.image (Finset.image e) (initialColex α k m)).card = _
    rw [card_image_of_injective _ (Finset.image_injective e.injective),
      (initial_properties α k m).2,
      (initial_properties β k m).2, Fintype.card_congr e.toEquiv]
  rcases ha.total hb with h | h
  · exact eq_of_subset_of_card_le h hc.ge
  · exact (eq_of_subset_of_card_le h hc.le).symm

theorem enumeration_transport : Spec.EnumerationTransport := by
  intro α _ _ k m j
  have hs := (segment_transport (Fin (Fintype.card α)) α
    (increasingEnumeration α) k m ∅).2
  refine ⟨hs, ?_⟩
  have ht := shadow_transport _ _ (increasingEnumeration α).toEmbedding
    (initialColex (Fin (Fintype.card α)) k m) j
  change mapFamily (increasingEnumeration α) _ =
    (Finset.shadow^[j]) (mapFamily (increasingEnumeration α) _) at ht
  rw [hs] at ht
  exact ht

end P205.Families
