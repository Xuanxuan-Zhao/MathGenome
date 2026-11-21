import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.ErdosKoRadoBound
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Data.Fintype.EquivFin

open Finset
namespace P205.Families

/-- Transport each member to the subtype of the ground set, then enumerate that subtype. -/
theorem erdosKoRadoBound : Specs.P205.Families.bound := by
  intro α _ X k F hk hn hF hi
  classical
  let e := X.equivFin
  let f := fun A : Finset α => (A.subtype (· ∈ X)).map e.toEmbedding
  have restore (A : Finset α) (hA : A ⊆ X) :
      (A.subtype (· ∈ X)).map (Function.Embedding.subtype _) = A :=
    subtype_map_of_mem hA
  have size (A : Finset α) (hA : A ⊆ X) : (f A).card = A.card := by
    have h := congrArg Finset.card (restore A hA)
    simpa only [f, card_map] using h
  have inj : Set.InjOn f F := by
    intro A hA B hB he
    have hs := (map_injective e.toEmbedding) he
    have h := congrArg (Finset.map (Function.Embedding.subtype (· ∈ X))) hs
    simpa only [restore A (mem_powersetCard.mp (hF hA)).1,
      restore B (mem_powersetCard.mp (hF hB)).1] using h
  have hs : (F.image f : Set (Finset (Fin X.card))).Sized k := by
    intro T hT
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hT
    obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp (hF hA)
    exact (size A hAX).trans hAk
  have hi' : (F.image f : Set (Finset (Fin X.card))).Intersecting := by
    intro S hS T hT hd
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hS
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hT
    apply hi hA hB
    have hd' := (disjoint_map e.toEmbedding).mp hd
    rw [← restore A (mem_powersetCard.mp (hF hA)).1,
      ← restore B (mem_powersetCard.mp (hF hB)).1]
    exact (disjoint_map _).mpr hd'
  have hb := Finset.erdos_ko_rado hi' hs (by omega : k ≤ X.card / 2)
  rwa [card_image_of_injOn inj] at hb

/-- Inserting the center is a bijection from the preceding layer off the center. -/
theorem fullStar_attains : Specs.P205.Families.star := by
  intro α _ X k c hk _ hc
  classical
  refine ⟨filter_subset _ _, ?_, ?_⟩
  · intro A hA B hB hd
    exact (disjoint_left.mp hd) (mem_filter.mp hA).2 (mem_filter.mp hB).2
  have heq : fullStar X k c = ((X.erase c).powersetCard (k - 1)).image (insert c) := by
    ext A
    constructor
    · intro hA
      obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp (mem_filter.mp hA).1
      have hcA := (mem_filter.mp hA).2
      refine mem_image.mpr ⟨A.erase c, mem_powersetCard.mpr ⟨?_, ?_⟩, insert_erase hcA⟩
      · exact erase_subset_erase c hAX
      · rw [card_erase_of_mem hcA, hAk]
    · intro hA
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
      obtain ⟨hBX, hBk⟩ := mem_powersetCard.mp hB
      have hcB : c ∉ B := fun h => (notMem_erase c X) (hBX h)
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, mem_insert_self _ _⟩
      · exact insert_subset hc (hBX.trans (erase_subset _ _))
      · rw [card_insert_of_notMem hcB, hBk]
        omega
  rw [heq, card_image_of_injOn, card_powersetCard, card_erase_of_mem hc]
  intro A hA B hB h
  have hcA : c ∉ A := fun h => (notMem_erase c X) ((mem_powersetCard.mp hA).1 h)
  have hcB : c ∉ B := fun h => (notMem_erase c X) ((mem_powersetCard.mp hB).1 h)
  have hh := congrArg (Finset.erase · c) h
  simpa [erase_insert hcA, erase_insert hcB] using hh

/-- At the middle layer, complementation pairs all sets with no fixed point. -/
theorem boundary_equality : Specs.P205.Families.boundaryEquality := by
  intro α _ X k F hk hn hF hi
  classical
  let L := X.powersetCard k
  let C := F.image (X \ ·)
  have comp_layer (A : Finset α) (hA : A ∈ L) : X \ A ∈ L := by
    obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp hA
    apply mem_powersetCard.mpr
    refine ⟨sdiff_subset, ?_⟩
    rw [card_sdiff_of_subset hAX, hAk, hn]
    omega
  have invol (A : Finset α) (hA : A ∈ L) : X \ (X \ A) = A :=
    Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hA).1
  have memC (A : Finset α) (hA : A ∈ L) : A ∈ C ↔ X \ A ∈ F := by
    constructor
    · intro h
      obtain ⟨B, hB, rfl⟩ := mem_image.mp h
      simpa only [invol B (hF hB)] using hB
    · intro h
      exact mem_image.mpr ⟨X \ A, h, invol A hA⟩
  have hC : C ⊆ L := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    exact comp_layer B (hF hB)
  have hCcard : C.card = F.card := by
    apply card_image_of_injOn
    intro A hA B hB he
    have h := congrArg (X \ ·) he
    simpa only [invol A (hF hA), invol B (hF hB)] using h
  have hd : Disjoint F C := by
    apply disjoint_left.mpr
    intro A hA hAC
    have hAc := (memC A (hF hA)).mp hAC
    apply hi hA hAc
    exact disjoint_left.mpr (fun a ha hca => (mem_sdiff.mp hca).2 ha)
  have hsub : F ∪ C ⊆ L := union_subset hF hC
  have hLcard : L.card = (X.card - 1).choose (k - 1) +
      (X.card - 1).choose (k - 1) := by
    change (X.powersetCard k).card = _
    rw [card_powersetCard]
    have hc : (X.card - 1).choose k = (X.card - 1).choose (k - 1) :=
      Nat.choose_symm_of_eq_add (by omega)
    calc
      X.card.choose k = ((X.card - 1) + 1).choose ((k - 1) + 1) := by
        congr 1 <;> omega
      _ = (X.card - 1).choose (k - 1) + (X.card - 1).choose k := by
        rw [Nat.choose_succ_succ']
        congr 2
        omega
      _ = _ := by rw [hc]
  constructor
  · intro heq
    have hu : F ∪ C = L := eq_of_subset_of_card_le hsub (by
      rw [card_union_of_disjoint hd, hCcard, hLcard, heq])
    intro A hA
    constructor
    · intro hAF hAc
      exact disjoint_left.mp hd hAF ((memC A hA).mpr hAc)
    · intro hAc
      have hAU : A ∈ F ∪ C := hu.symm ▸ hA
      rcases mem_union.mp hAU with h | h
      · exact h
      · exact False.elim (hAc ((memC A hA).mp h))
  · intro hpair
    have hu : F ∪ C = L := by
      apply Subset.antisymm hsub
      intro A hA
      by_cases hAF : A ∈ F
      · exact mem_union_left C hAF
      · have hAc : X \ A ∈ F := by
          by_contra h
          exact hAF ((hpair A hA).mpr h)
        exact mem_union_right F ((memC A hA).mpr hAc)
    have hcard := congrArg Finset.card hu
    rw [card_union_of_disjoint hd, hCcard, hLcard] at hcard
    omega

end P205.Families
