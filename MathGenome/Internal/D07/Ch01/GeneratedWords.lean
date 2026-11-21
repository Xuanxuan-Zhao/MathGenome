import MathGenome.Internal.D07.Ch01.SubgroupLattice
import MathGenome.Internal.Specs.D07.Ch01.GeneratedWords
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Words and induction on generation

The finite products in `K07.01.generated_words` are ordered list products.
Concatenation realizes multiplication, and reversing and inverting all letters
realizes inversion. This retains the arbitrary, possibly noncommutative group
and arbitrary, possibly empty generating set of the source.
-/

namespace D07.Ch01.GeneratedWords

universe u

theorem mem_generated_iff_word (G : Type u) [Group G] (S : Set G) (x : G) :
    x ∈ Subgroup.closure S ↔
      ∃ w : List G, (∀ a ∈ w, a ∈ S ∨ ∃ s ∈ S, a = s⁻¹) ∧ w.prod = x := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
        exact ⟨[a], by simpa using Or.inl ha, by simp⟩
    | one =>
        exact ⟨[], by simp, rfl⟩
    | mul a b _ _ ha hb =>
        obtain ⟨v, hv, hvprod⟩ := ha
        obtain ⟨w, hw, hwprod⟩ := hb
        refine ⟨v ++ w, ?_, ?_⟩
        · intro c hc
          rcases List.mem_append.mp hc with hc | hc
          · exact hv c hc
          · exact hw c hc
        · rw [List.prod_append, hvprod, hwprod]
    | inv a _ ha =>
        obtain ⟨w, hw, hwprod⟩ := ha
        refine ⟨(w.map Inv.inv).reverse, ?_, ?_⟩
        · intro c hc
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
          rcases hw b hb with hbS | ⟨s, hs, hbs⟩
          · exact Or.inr ⟨b, hbS, rfl⟩
          · left
            simpa only [hbs, inv_inv] using hs
        · rw [← List.prod_inv_reverse, hwprod]
  · rintro ⟨w, hw, rfl⟩
    induction w with
    | nil => exact (Subgroup.closure S).one_mem
    | cons a w ih =>
        apply (Subgroup.closure S).mul_mem
        · rcases hw a List.mem_cons_self with ha | ⟨s, hs, rfl⟩
          · exact Subgroup.subset_closure ha
          · exact (Subgroup.closure S).inv_mem (Subgroup.subset_closure hs)
        · exact ih (fun b hb => hw b (List.mem_cons_of_mem a hb))

theorem generation_induction (G : Type u) [Group G] (S : Set G) (P : G → Prop)
    (hS : ∀ s ∈ S, P s) (h1 : P 1)
    (hmul : ∀ x y : G, P x → P y → P (x * y))
    (hinv : ∀ x : G, P x → P x⁻¹) :
    ∀ x ∈ Subgroup.closure S, P x := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := (mem_generated_iff_word G S x).mp hx
  clear hx
  induction w with
  | nil => exact h1
  | cons a w ih =>
      apply hmul
      · rcases hw a List.mem_cons_self with ha | ⟨s, hs, rfl⟩
        · exact hS a ha
        · exact hinv s (hS s hs)
      · exact ih (fun b hb => hw b (List.mem_cons_of_mem a hb))

end D07.Ch01.GeneratedWords
