import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.ErdosKoRadoUniqueness
import MathGenome.Internal.ExtremalOptimization.P205.Families.ErdosKoRadoBound
import MathGenome.Internal.ExtremalOptimization.P205.Families.Shifting
import MathGenome.Internal.ExtremalOptimization.P205.Families.ShiftedStars
import MathGenome.Internal.ExtremalOptimization.P205.Families.InverseShiftStar

open Finset

namespace P205.Families

/-- Reverse a finite sequence of shifts, retaining the hypotheses needed at
each original family. -/
lemma fullStar_of_shift_steps {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k < n)
    {F G : Shifting.Family n} (hFG : Shifting.Steps F G) :
    (F : Set (Finset (Fin n))).Sized k →
    (F : Set (Finset (Fin n))).Intersecting →
    (∃ c : Fin n, G = fullStar univ k c) →
    ∃ c : Fin n, F = fullStar univ k c := by
  induction hFG using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ _ hs
    exact hs
  | @head F H hstep hHG ih =>
    intro hsize hi hs
    obtain ⟨i, j, hij, _, rfl⟩ := hstep
    obtain ⟨c, hc⟩ := ih (Shifting.shift_rank i j F hsize)
      (Shifting.shift_intersecting i j hij F hi) hs
    exact InverseShiftStar.inverse_shift_star hk hn i j hij F hsize hi c hc

/-- The strict-range classification on an enumerated ground set. -/
theorem fin_extremal_is_fullStar {n k : ℕ} (F : Shifting.Family n)
    (hk : 1 ≤ k) (hn : 2 * k < n)
    (hsize : (F : Set (Finset (Fin n))).Sized k)
    (hi : (F : Set (Finset (Fin n))).Intersecting)
    (hcard : F.card = (n - 1).choose (k - 1)) :
    ∃ c : Fin n, F = fullStar univ k c := by
  obtain ⟨G, hFG, hstable, hGF, hsizeG, hiG⟩ := Shifting.exists_shifted F hsize hi
  have hs := ShiftedStars.shifted_extremal_is_fullStar G hk hn hsizeG hiG hstable
    (hGF.trans hcard)
  exact fullStar_of_shift_steps hk hn hFG hsize hi hs

/-- Enumerate the subtype of the ground set. After classification on `Fin`,
pull its center back and use the star cardinality to obtain the entire star. -/
theorem erdosKoRadoUniqueness : Specs.P205.Families.uniqueness := by
  intro α _ X k F hk hn hF hi
  classical
  constructor
  · intro hcard
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
    have hsize : (F.image f : Set (Finset (Fin X.card))).Sized k := by
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
    obtain ⟨c, hc⟩ := fin_extremal_is_fullStar (F.image f) hk hn hsize hi'
      (by rwa [card_image_of_injOn inj])
    let d := e.symm c
    refine ⟨d.val, d.property, ?_⟩
    apply eq_of_subset_of_card_le
    · intro A hA
      apply mem_filter.mpr
      refine ⟨hF hA, ?_⟩
      have hcA : c ∈ f A := by
        have hAf : f A ∈ F.image f := mem_image.mpr ⟨A, hA, rfl⟩
        rw [hc] at hAf
        exact (mem_filter.mp hAf).2
      have hdA : d ∈ A.subtype (· ∈ X) := by
        obtain ⟨a, ha, hea⟩ := mem_map.mp hcA
        have had : a = d := e.injective (by simpa [d] using hea)
        exact had ▸ ha
      exact mem_subtype.mp hdA
    · rw [(fullStar_attains X k d.val hk (by omega) d.property).2.2, hcard]
  · rintro ⟨c, hc, rfl⟩
    exact (fullStar_attains X k c hk (by omega) hc).2.2

end P205.Families
