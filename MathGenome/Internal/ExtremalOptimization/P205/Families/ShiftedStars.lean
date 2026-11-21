import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.ShiftedStars
import MathGenome.Internal.ExtremalOptimization.P205.Families.Shifting
import MathGenome.Internal.ExtremalOptimization.P205.Families.ErdosKoRadoBound
import Mathlib.Data.Finset.Max

open Finset

namespace P205.Families.ShiftedStars

variable {α : Type*} [LinearOrder α]

/-- Closure under replacements inside a specified ordered ground set. -/
def Closed (X : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ i ∈ X, ∀ j ∈ X, i < j → ∀ A ∈ F,
    i ∉ A → j ∈ A → insert i (A.erase j) ∈ F

def avoiding (F : Finset (Finset α)) (x : α) := F.filter (x ∉ ·)

def residual (F : Finset (Finset α)) (x : α) :=
  (F.filter (x ∈ ·)).image (fun A => A.erase x)

lemma mem_avoiding {F : Finset (Finset α)} {x : α} {A : Finset α} :
    A ∈ avoiding F x ↔ A ∈ F ∧ x ∉ A := by simp [avoiding]

lemma mem_residual {F : Finset (Finset α)} {x : α} {A : Finset α} :
    A ∈ residual F x ↔ x ∉ A ∧ insert x A ∈ F := by
  simp only [residual, mem_image, mem_filter]
  constructor
  · rintro ⟨B, ⟨hB, hxB⟩, rfl⟩
    exact ⟨notMem_erase _ _, by simpa only [insert_erase hxB] using hB⟩
  · rintro ⟨hxA, hA⟩
    exact ⟨insert x A, ⟨hA, mem_insert_self _ _⟩, erase_insert hxA⟩

lemma split_card (F : Finset (Finset α)) (x : α) :
    (avoiding F x).card + (residual F x).card = F.card := by
  have hinj : Set.InjOn (fun A : Finset α => A.erase x) (F.filter (x ∈ ·)) := by
    intro A hA B hB h
    have h' := congrArg (insert x) h
    simpa only [insert_erase (mem_filter.mp hA).2,
      insert_erase (mem_filter.mp hB).2] using h'
  rw [residual, card_image_of_injOn hinj, avoiding]
  simpa [add_comm] using card_filter_add_card_filter_not (s := F) (p := fun A => x ∈ A)

lemma avoiding_layer {X : Finset α} {F : Finset (Finset α)} {k : ℕ} {x : α}
    (hF : F ⊆ X.powersetCard k) : avoiding F x ⊆ (X.erase x).powersetCard k := by
  intro A hA
  obtain ⟨hAF, hxA⟩ := mem_avoiding.mp hA
  obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp (hF hAF)
  exact mem_powersetCard.mpr ⟨fun a ha => mem_erase.mpr ⟨fun h => hxA (h ▸ ha), hAX ha⟩, hAk⟩

lemma residual_layer {X : Finset α} {F : Finset (Finset α)} {k : ℕ} {x : α}
    (hF : F ⊆ X.powersetCard k) : residual F x ⊆ (X.erase x).powersetCard (k - 1) := by
  intro A hA
  obtain ⟨hxA, hAF⟩ := mem_residual.mp hA
  obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp (hF hAF)
  apply mem_powersetCard.mpr
  refine ⟨fun a ha => mem_erase.mpr ⟨fun h => hxA (h ▸ ha), hAX (mem_insert_of_mem ha)⟩, ?_⟩
  rw [card_insert_of_notMem hxA] at hAk
  omega

lemma residual_closed {X : Finset α} {F : Finset (Finset α)} {x : α}
    (hF : Closed X F) : Closed (X.erase x) (residual F x) := by
  intro i hi j hj hij A hA hiA hjA
  obtain ⟨hxA, hAF⟩ := mem_residual.mp hA
  have hix := (mem_erase.mp hi).1
  have hjx := (mem_erase.mp hj).1
  apply mem_residual.mpr
  refine ⟨by simp [hxA, hix.symm], ?_⟩
  have hh := hF i (mem_of_mem_erase hi) j (mem_of_mem_erase hj) hij
    (insert x A) hAF (by simp [hix, hiA]) (mem_insert_of_mem hjA)
  have he : insert i ((insert x A).erase j) = insert x (insert i (A.erase j)) := by
    ext a
    simp only [mem_insert, mem_erase]
    grind
  rwa [he] at hh

/-- The last-point residual is intersecting because a spare smaller point can
replace the last point in one of two allegedly disjoint residual members. -/
lemma residual_intersecting {X : Finset α} {F : Finset (Finset α)} {k : ℕ} {x : α}
    (hk : 1 ≤ k) (hx : x ∈ X) (hmax : ∀ i ∈ X.erase x, i < x)
    (hn : 2 * k < X.card) (hF : F ⊆ X.powersetCard k)
    (hi : (F : Set (Finset α)).Intersecting) (hc : Closed X F) :
    (residual F x : Set (Finset α)).Intersecting := by
  intro C hC D hD hd
  have hCk := (mem_powersetCard.mp (residual_layer hF hC)).2
  have hDk := (mem_powersetCard.mp (residual_layer hF hD)).2
  have hsmall : (C ∪ D).card < (X.erase x).card := by
    have hu := card_union_le C D
    rw [card_erase_of_mem hx]
    omega
  obtain ⟨i, hiX, hiCD⟩ := exists_mem_notMem_of_card_lt_card hsmall
  have hiC : i ∉ C := fun h => hiCD (mem_union_left _ h)
  have hiD : i ∉ D := fun h => hiCD (mem_union_right _ h)
  have hix : i ≠ x := (mem_erase.mp hiX).1
  obtain ⟨hxC, hCF⟩ := mem_residual.mp hC
  obtain ⟨hxD, hDF⟩ := mem_residual.mp hD
  have hmove := hc i (mem_of_mem_erase hiX) x hx (hmax i hiX)
    (insert x C) hCF (by simp [hix, hiC]) (mem_insert_self _ _)
  rw [erase_insert hxC] at hmove
  apply hi hmove hDF
  apply disjoint_left.mpr
  intro a ha hb
  simp only [mem_insert] at ha hb
  rcases ha with rfl | ha
  · exact (hb.elim hix hiD)
  · rcases hb with rfl | hb
    · exact hxC ha
    · exact disjoint_left.mp hd ha hb

lemma star_eq_of_contains {X : Finset α} {F : Finset (Finset α)} {k : ℕ} {c : α}
    (hk : 1 ≤ k) (hn : 2 * k ≤ X.card) (hc : c ∈ X)
    (hF : F ⊆ X.powersetCard k) (hcard : F.card = (X.card - 1).choose (k - 1))
    (hcenter : ∀ A ∈ F, c ∈ A) : F = fullStar X k c := by
  apply eq_of_subset_of_card_le
  · intro A hA
    exact mem_filter.mpr ⟨hF hA, hcenter A hA⟩
  · rw [(fullStar_attains X k c hk hn hc).2.2, hcard]

lemma rank_one_classification {X : Finset α} {F : Finset (Finset α)}
    (hn : 2 < X.card) (hF : F ⊆ X.powersetCard 1)
    (hcard : F.card = (X.card - 1).choose (1 - 1)) :
    ∃ c ∈ X, F = fullStar X 1 c := by
  have hcard' : F.card = 1 := by simpa using hcard
  obtain ⟨A, hFA⟩ := card_eq_one.mp hcard'
  have hAF : A ∈ F := by rw [hFA]; simp
  obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp (hF hAF)
  obtain ⟨c, rfl⟩ := card_eq_one.mp hAk
  refine ⟨c, hAX (mem_singleton_self _), ?_⟩
  apply star_eq_of_contains (by omega) (by omega) (hAX (mem_singleton_self _)) hF hcard
  intro B hB
  have he : B = {c} := by simpa [hFA] using hB
  simp [he]

/-- A set avoiding the center cannot meet every member of a residual full star. -/
lemma contains_center_of_residual_star {X : Finset α} {F : Finset (Finset α)}
    {k : ℕ} {x c : α} (hk : 2 ≤ k) (hn : 2 * k < X.card) (hx : x ∈ X)
    (hc : c ∈ X.erase x) (hF : F ⊆ X.powersetCard k)
    (hi : (F : Set (Finset α)).Intersecting)
    (hstar : residual F x = fullStar (X.erase x) (k - 1) c) :
    ∀ A ∈ F, x ∉ A → c ∈ A := by
  intro A hA hxA
  by_contra hcA
  have hAY : A ⊆ X.erase x := by
    intro a ha
    exact mem_erase.mpr ⟨fun he => hxA (he ▸ ha), (mem_powersetCard.mp (hF hA)).1 ha⟩
  have hcYA : c ∈ X.erase x \ A := mem_sdiff.mpr ⟨hc, hcA⟩
  have hroom : k - 1 ≤ (X.erase x \ A).card := by
    rw [card_sdiff_of_subset hAY, card_erase_of_mem hx, (mem_powersetCard.mp (hF hA)).2]
    omega
  obtain ⟨B, hcB, hBYA, hBk⟩ := exists_subsuperset_card_eq
    (singleton_subset_iff.mpr hcYA) (by simp; omega : ({c} : Finset α).card ≤ k - 1) hroom
  have hBF : B ∈ residual F x := by
    rw [hstar]
    apply mem_filter.mpr
    exact ⟨mem_powersetCard.mpr ⟨hBYA.trans sdiff_subset, hBk⟩, hcB (mem_singleton_self _)⟩
  have hB := (mem_residual.mp hBF).2
  apply hi hA hB
  apply disjoint_left.mpr
  intro a ha hb
  rcases mem_insert.mp hb with rfl | hb
  · exact hxA ha
  · exact (mem_sdiff.mp (hBYA hb)).2 ha

/-- Pascal's identity in the subtraction notation used in the EKR bound. -/
lemma pascal_bound {n k : ℕ} (hk : 2 ≤ k) (hn : 2 * k < n) :
    (n - 1).choose (k - 1) = (n - 2).choose (k - 1) + (n - 2).choose (k - 2) := by
  have hn' : n - 1 = (n - 2) + 1 := by omega
  have hk' : k - 1 = (k - 2) + 1 := by omega
  rw [hn', hk', Nat.choose_succ_succ']
  rw [← hk', add_comm]

/-- The two last-point slices attain their respective bounds. The avoiding
slice is allowed to be in the critical range; no equality classification for
that slice is used. -/
lemma split_extremal {X : Finset α} {F : Finset (Finset α)} {k : ℕ} {x : α}
    (hk : 2 ≤ k) (hn : 2 * k < X.card) (hx : x ∈ X)
    (hmax : ∀ i ∈ X.erase x, i < x) (hF : F ⊆ X.powersetCard k)
    (hi : (F : Set (Finset α)).Intersecting) (hc : Closed X F)
    (hcard : F.card = (X.card - 1).choose (k - 1)) :
    (avoiding F x).card = (X.card - 2).choose (k - 1) ∧
    (residual F x).card = (X.card - 2).choose (k - 2) := by
  have hi0 : (avoiding F x : Set (Finset α)).Intersecting := by
    intro A hA B hB
    exact hi (mem_avoiding.mp hA).1 (mem_avoiding.mp hB).1
  have hi1 := residual_intersecting (by omega) hx hmax hn hF hi hc
  have hb0 := erdosKoRadoBound (X.erase x) k (avoiding F x) (by omega)
    (by rw [card_erase_of_mem hx]; omega) (avoiding_layer hF) hi0
  have hb1 := erdosKoRadoBound (X.erase x) (k - 1) (residual F x) (by omega)
    (by rw [card_erase_of_mem hx]; omega) (residual_layer hF) hi1
  have hsplit := split_card F x
  rw [card_erase_of_mem hx] at hb0 hb1
  have hn' : X.card - 1 - 1 = X.card - 2 := by omega
  have hk' : k - 1 - 1 = k - 2 := by omega
  rw [hn'] at hb0
  rw [hn', hk'] at hb1
  rw [hcard, pascal_bound hk hn] at hsplit
  omega

/-- Induction on the rank, uniformly over the finite ordered ground set. -/
theorem closed_extremal_is_fullStar (k : ℕ) :
    ∀ (X : Finset α) (F : Finset (Finset α)),
      1 ≤ k → 2 * k < X.card → F ⊆ X.powersetCard k →
      (F : Set (Finset α)).Intersecting → Closed X F →
      F.card = (X.card - 1).choose (k - 1) →
      ∃ c ∈ X, F = fullStar X k c := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro X F hk hn hF hi hc hcard
    by_cases hk1 : k = 1
    · subst k
      exact rank_one_classification hn hF hcard
    have hk2 : 2 ≤ k := by omega
    have hX : X.Nonempty := card_pos.mp (by omega)
    let x := X.max' hX
    have hx : x ∈ X := max'_mem X hX
    have hmax : ∀ i ∈ X.erase x, i < x := by
      intro i hi
      exact lt_max'_of_mem_erase_max' X hX hi
    have hYcard : (X.erase x).card = X.card - 1 := card_erase_of_mem hx
    have h1card := (split_extremal hk2 hn hx hmax hF hi hc hcard).2
    have hi1 := residual_intersecting hk hx hmax hn hF hi hc
    obtain ⟨c, hcY, hstar⟩ := ih (k - 1) (by omega) (X.erase x) (residual F x)
      (by omega) (by rw [hYcard]; omega) (residual_layer hF) hi1
      (residual_closed hc) (by
        rw [hYcard]
        have hn' : X.card - 1 - 1 = X.card - 2 := by omega
        have hk' : k - 1 - 1 = k - 2 := by omega
        simpa only [hn', hk'] using h1card)
    refine ⟨c, mem_of_mem_erase hcY, ?_⟩
    apply star_eq_of_contains hk (by omega) (mem_of_mem_erase hcY) hF hcard
    intro A hA
    by_cases hxA : x ∈ A
    · have hAr : A.erase x ∈ residual F x := by
        apply mem_residual.mpr
        exact ⟨notMem_erase _ _, by simpa only [insert_erase hxA] using hA⟩
      rw [hstar] at hAr
      exact mem_of_mem_erase (mem_filter.mp hAr).2
    · exact contains_center_of_residual_star hk2 hn hx hcY hF hi hstar A hA hxA

theorem shifted_extremal_is_fullStar : Specs.P205.Families.ShiftedStars.classification := by
  intro n k F hk hn hsize hi hstable hcard
  have hF : F ⊆ (univ : Finset (Fin n)).powersetCard k := by
    intro A hA
    exact mem_powersetCard.mpr ⟨subset_univ _, hsize hA⟩
  have hclosed : Closed (univ : Finset (Fin n)) F := by
    intro i _ j _ hij A hA hiA hjA
    have hh := UV.compress_mem_compression (u := ({i} : Finset (Fin n))) (v := {j}) hA
    change UV.compress {i} {j} A ∈ Shifting.shift i j F at hh
    rw [hstable i j hij, Shifting.shift_rule i j (ne_of_lt hij), ite_eq_left ⟨hiA, hjA⟩] at hh
    exact hh
  obtain ⟨c, _, hstar⟩ := closed_extremal_is_fullStar k univ F hk
    (by simpa using hn) hF hi hclosed (by simpa using hcard)
  exact ⟨c, hstar⟩

end P205.Families.ShiftedStars
