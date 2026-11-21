import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.LYMSpernerEquality
import MathGenome.Internal.ExtremalOptimization.P205.Families.LYMSpernerBounds
import Mathlib.Combinatorics.SetFamily.AhlswedeZhang
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

open Finset
namespace P205.Families
universe u
variable {X : Type u} [Fintype X]

/-- Equality leaves no positive correction term in the AZ identity. -/
lemma truncatedInf_eq_empty_of_lym_eq [DecidableEq X] [Nonempty X]
    {𝒜 : Finset (Finset X)}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X)))
    (h₀ : ∅ ∉ 𝒜)
    (heq : (∑ s ∈ 𝒜, ((Fintype.card X).choose s.card : ℚ)⁻¹) = 1)
    {s : Finset X} (hs : s ∉ 𝒜) : 𝒜.truncatedInf s = ∅ := by
  have hn : 𝒜.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at heq
  let f : Finset X → ℚ := fun t ↦
    (𝒜.truncatedInf t).card / (t.card * (Fintype.card X).choose t.card)
  have hsum : ∑ t ∈ 𝒜, f t = 1 := by
    rw [← heq]
    apply sum_congr rfl
    intro t ht
    dsimp [f]
    rw [truncatedInf_of_isAntichain h𝒜 ht, div_mul_cancel_left₀]
    exact_mod_cast (Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_of_not_mem ht h₀))).ne'
  have hdiff : ∑ t ∈ (univ \ 𝒜), f t = 0 := by
    have hh := sum_sdiff (f := f) (subset_univ 𝒜)
    rw [hsum] at hh
    have hi : ∑ t, f t = 1 := AhlswedeZhang.infSum_eq_one hn h₀
    linarith
  have hz := (sum_eq_zero_iff_of_nonneg
    (fun t (_ : t ∈ univ \ 𝒜) ↦ show 0 ≤ f t by dsimp [f]; positivity)).mp hdiff s
      (mem_sdiff.mpr ⟨mem_univ s, hs⟩)
  by_cases hse : s = ∅
  · subst s
    exact Finset.subset_empty.mp Finset.truncatedInf_le
  have hd : (s.card * (Fintype.card X).choose s.card : ℚ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hse)))
      (by exact_mod_cast (Nat.choose_pos s.card_le_univ).ne')
  exact card_eq_zero.mp (by exact_mod_cast (div_eq_zero_iff.mp hz).resolve_right hd)

/-- The minimum occupied rank is closed under replacing one point. -/
lemma exchange_mem_of_lym_eq [DecidableEq X] [Nonempty X]
    {𝒜 : Finset (Finset X)}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X)))
    (h₀ : ∅ ∉ 𝒜)
    (heq : (∑ t ∈ 𝒜, ((Fintype.card X).choose t.card : ℚ)⁻¹) = 1)
    {s : Finset X} (hs : s ∈ 𝒜)
    (hmin : ∀ t ∈ 𝒜, s.card ≤ t.card)
    {a b : X} (ha : a ∈ s) (hb : b ∉ s) : (insert b s).erase a ∈ 𝒜 := by
  have hu : insert b s ∉ 𝒜 := by
    intro h
    have he := h𝒜.eq hs h (subset_insert b s)
    exact hb (he.symm ▸ mem_insert_self b s)
  have hz := truncatedInf_eq_empty_of_lym_eq h𝒜 h₀ heq hu
  have hc : insert b s ∈ upperClosure (𝒜 : Set (Finset X)) :=
    ⟨s, hs, subset_insert b s⟩
  have hw : ∃ t ∈ 𝒜, t ⊆ insert b s ∧ a ∉ t := by
    by_contra! h
    have hi : a ∈ 𝒜.truncatedInf (insert b s) := by
      rw [truncatedInf_of_mem hc, mem_inf']
      intro t ht
      exact h t (mem_filter.mp ht).1 (mem_filter.mp ht).2
    simp [hz] at hi
  obtain ⟨t, ht, htu, hat⟩ := hw
  have hsub : t ⊆ (insert b s).erase a := by
    intro x hx
    exact mem_erase.mpr ⟨by rintro rfl; exact hat hx, htu hx⟩
  have hcard : ((insert b s).erase a).card = s.card := by
    rw [card_erase_of_mem (mem_insert_of_mem ha), card_insert_of_notMem hb]
    omega
  have het := eq_of_subset_of_card_le hsub (hcard ▸ hmin t ht)
  exact het ▸ ht

omit [Fintype X] in
/-- Connectivity of a fixed layer under exchanges of single points. -/
lemma mem_of_exchange [DecidableEq X] {𝒜 : Finset (Finset X)} {k : ℕ}
    (hex : ∀ s ∈ 𝒜, s.card = k → ∀ a ∈ s, ∀ b ∉ s, (insert b s).erase a ∈ 𝒜)
    {s t : Finset X} (hs : s ∈ 𝒜) (hsk : s.card = k) (htk : t.card = k) : t ∈ 𝒜 := by
  generalize hm : (t \ s).card = m
  induction m using Nat.strong_induction_on generalizing s with
  | h m ih =>
    by_cases hsub : t ⊆ s
    · have he := eq_of_subset_of_card_le hsub (by omega : s.card ≤ t.card)
      exact he.symm ▸ hs
    obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr (mt sdiff_eq_empty_iff_subset.mp hsub)
    obtain ⟨a, ha⟩ : (s \ t).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro hh
      have he := eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp hh)
        (by omega : t.card ≤ s.card)
      exact hsub (he ▸ Subset.rfl)
    have hb' := mem_sdiff.mp hb
    have ha' := mem_sdiff.mp ha
    let s' := (insert b s).erase a
    have hs' : s' ∈ 𝒜 := hex s hs hsk a ha'.1 b hb'.2
    have hsk' : s'.card = k := by
      dsimp [s']
      rw [card_erase_of_mem (mem_insert_of_mem ha'.1), card_insert_of_notMem hb'.2]
      omega
    have he : t \ s' = (t \ s).erase b := by
      ext x
      simp only [s', mem_sdiff, mem_erase, mem_insert]
      constructor
      · rintro ⟨hxt, hx⟩
        have hxa : x ≠ a := by rintro rfl; exact ha'.2 hxt
        tauto
      · rintro ⟨hxb, hxt, hxs⟩
        exact ⟨hxt, by tauto⟩
    have hlt : (t \ s').card < m := by
      rw [he, card_erase_of_mem hb]
      have := card_pos.mpr (show (t \ s).Nonempty from ⟨b, hb⟩)
      omega
    exact ih _ hlt hs' hsk' rfl

/-- Every full layer has Lubell sum one, including the empty-set layer. -/
lemma lym_sum_layer (k : ℕ) (hk : k ≤ Fintype.card X) :
    (∑ s ∈ (univ : Finset X).powersetCard k,
      ((Fintype.card X).choose s.card : ℝ)⁻¹) = 1 := by
  classical
  calc
    _ = ∑ _s ∈ (univ : Finset X).powersetCard k,
        ((Fintype.card X).choose k : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro s hs
      rw [mem_powersetCard_univ.mp hs]
    _ = 1 := by
      simp only [sum_const, card_powersetCard, card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast (Nat.choose_pos hk).ne')

/-- Complete LYM equality classification on an arbitrary finite ground type. -/
theorem lym_equality {X : Type u} [Fintype X] (n : ℕ)
    (hcard : Fintype.card X = n) (𝒜 : Finset (Finset X))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X))) :
    ((∑ A ∈ 𝒜, (Nat.choose n A.card : ℝ)⁻¹) = 1 ↔
      ∃ k : ℕ, k ≤ n ∧ 𝒜 = (univ : Finset X).powersetCard k) := by
  classical
  subst n
  constructor
  · intro heq
    have hn : 𝒜.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at heq
    by_cases h₀ : ∅ ∈ 𝒜
    · refine ⟨0, Nat.zero_le _, ?_⟩
      have he : 𝒜 = {∅} := by
        ext t
        constructor
        · intro ht
          have := h𝒜.eq h₀ ht (empty_subset t)
          simp [this.symm]
        · simpa using fun h : t = ∅ ↦ h.symm ▸ h₀
      simpa using he
    obtain ⟨s, hs, hmin⟩ := 𝒜.exists_min_image Finset.card hn
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr (ne_of_mem_of_not_mem hs h₀)
    have : Nonempty X := ⟨x⟩
    have heqQ : (∑ t ∈ 𝒜, ((Fintype.card X).choose t.card : ℚ)⁻¹) = 1 := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      exact heq
    have hex : ∀ t ∈ 𝒜, t.card = s.card →
        ∀ a ∈ t, ∀ b ∉ t, (insert b t).erase a ∈ 𝒜 := by
      intro t ht htk a ha b hb
      exact exchange_mem_of_lym_eq h𝒜 h₀ heqQ ht
        (by simpa [htk] using hmin) ha hb
    have hall : ∀ t : Finset X, t.card = s.card → t ∈ 𝒜 := by
      intro t htk
      exact mem_of_exchange hex hs rfl htk
    refine ⟨s.card, s.card_le_univ, ?_⟩
    ext t
    rw [mem_powersetCard_univ]
    constructor
    · intro ht
      obtain ⟨r, hrt, hr⟩ := exists_subset_card_eq (hmin t ht)
      have he := h𝒜.eq (hall r hr) ht hrt
      simpa [he] using hr
    · exact hall t
  · rintro ⟨k, hk, rfl⟩
    exact lym_sum_layer k hk

/-- Strict growth on the lower half of the binomial row. -/
lemma choose_lt_succ_below_middle {n r : ℕ} (hr : r < n / 2) :
    n.choose r < n.choose (r + 1) := by
  have hrn : r ≤ n := by omega
  have hp := Nat.choose_pos hrn
  have hratio := Nat.choose_succ_right_eq n r
  have hstrict : r + 1 < n - r := by omega
  by_contra! h
  have hm := Nat.mul_le_mul_right (r + 1) h
  nlinarith

/-- The binomial maximum is attained at precisely the middle rank or ranks. -/
lemma choose_eq_middle_iff {n k : ℕ} (hk : k ≤ n) :
    n.choose k = n.choose (n / 2) ↔ k = n / 2 ∨ k = (n + 1) / 2 := by
  constructor
  · intro he
    by_cases hl : k < n / 2
    · have := (choose_lt_succ_below_middle hl).trans_le (Nat.choose_le_middle (k + 1) n)
      omega
    by_cases hu : (n + 1) / 2 < k
    · have hl' : n - k < n / 2 := by omega
      have hh := (choose_lt_succ_below_middle hl').trans_le
        (Nat.choose_le_middle (n - k + 1) n)
      rw [Nat.choose_symm hk] at hh
      omega
    omega
  · rintro (rfl | rfl)
    · rfl
    · have hm : n - n / 2 = (n + 1) / 2 := by omega
      rw [← hm, Nat.choose_symm (Nat.div_le_self n 2)]

/-- Complete Sperner equality classification, with no nonemptiness assumptions. -/
theorem sperner_equality {X : Type u} [Fintype X] (n : ℕ)
    (hcard : Fintype.card X = n) (𝒜 : Finset (Finset X))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X))) :
    (𝒜.card = Nat.choose n (n / 2) ↔
      𝒜 = (univ : Finset X).powersetCard (n / 2) ∨
      𝒜 = (univ : Finset X).powersetCard ((n + 1) / 2)) := by
  classical
  subst n
  constructor
  · intro he
    have hM : (0 : ℝ) < (Fintype.card X).choose (Fintype.card X / 2) := by
      exact_mod_cast Nat.choose_pos (Nat.div_le_self (Fintype.card X) 2)
    have hlower : 1 ≤ ∑ s ∈ 𝒜, ((Fintype.card X).choose s.card : ℝ)⁻¹ := by
      calc
        1 = ∑ _s ∈ 𝒜, ((Fintype.card X).choose (Fintype.card X / 2) : ℝ)⁻¹ := by
          simp only [sum_const, nsmul_eq_mul, he]
          exact (mul_inv_cancel₀ hM.ne').symm
        _ ≤ _ := by
          apply sum_le_sum
          intro s hs
          apply (inv_le_inv₀ hM (by exact_mod_cast Nat.choose_pos s.card_le_univ)).mpr
          exact_mod_cast Nat.choose_le_middle s.card (Fintype.card X)
    have hlym := le_antisymm (lym_bound _ rfl 𝒜 h𝒜) hlower
    obtain ⟨k, hk, hlayer⟩ := (lym_equality _ rfl 𝒜 h𝒜).mp hlym
    have hchoose : (Fintype.card X).choose k =
        (Fintype.card X).choose (Fintype.card X / 2) := by
      simpa [hlayer, card_powersetCard] using he
    rcases (choose_eq_middle_iff hk).mp hchoose with h | h
    · exact Or.inl (h ▸ hlayer)
    · exact Or.inr (h ▸ hlayer)
  · rintro (rfl | rfl)
    · simp
    · simp only [card_powersetCard, card_univ]
      exact (choose_eq_middle_iff (by omega : (Fintype.card X + 1) / 2 ≤ Fintype.card X)).mpr
        (Or.inr rfl)

/-- The two middle layers coincide exactly when the ground-set size is even. -/
theorem middle_layers_coincide {X : Type u} [Fintype X] (n : ℕ)
    (hcard : Fintype.card X = n) :
    ((univ : Finset X).powersetCard (n / 2) =
      (univ : Finset X).powersetCard ((n + 1) / 2) ↔ n % 2 = 0) := by
  classical
  constructor
  · intro he
    obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr
      (show n / 2 ≤ (univ : Finset X).card by simp [hcard]; omega)
    have hs' := hs
    rw [he] at hs'
    have h₁ := mem_powersetCard_univ.mp hs
    have h₂ := mem_powersetCard_univ.mp hs'
    omega
  · intro he
    have hi : n / 2 = (n + 1) / 2 := by omega
    rw [hi]

end P205.Families
