import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.LocalLYM
import Mathlib.Combinatorics.SetFamily.LYM

namespace P205.Families

universe u

/-- Proposition p205:W06, lower form. -/
theorem lower_local_lym : Specs.P205.Families.LowerLocalLYM.{u} := by
  intro α _ _ k A hk _ hA
  exact Finset.local_lubell_yamamoto_meshalkin_inequality_div (by omega) hA

/-- Proposition p205:W06, upper form, obtained by complementing each member. -/
theorem upper_local_lym : Specs.P205.Families.UpperLocalLYM.{u} := by
  intro α _ _ k A hk hA
  have hSized : (A : Set (Finset α)).Sized k := hA
  have h := Finset.local_lubell_yamamoto_meshalkin_inequality_div
    (𝕜 := ℝ) (by omega : Fintype.card α - k ≠ 0) hSized.compls
  rw [Finset.card_compls, Finset.shadow_compls, Finset.card_compls,
    Nat.choose_symm (Nat.le_of_lt hk)] at h
  have hrank : Fintype.card α - k - 1 = Fintype.card α - (k + 1) := by omega
  rw [hrank, Nat.choose_symm hk] at h
  exact h

/-- The rank-zero shadow convention agrees with one-point deletion. -/
theorem rank_zero_shadow : Specs.P205.Families.RankZeroShadow.{u} := by
  intro α _ A hA
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨s, hs, a, ha, _⟩ := Finset.mem_shadow_iff.mp ht
  have hs0 : s = ∅ := Finset.card_eq_zero.mp (hA s hs)
  simp [hs0] at ha

/-- The canonical upper shadow has the source's next-layer description. -/
theorem upper_shadow_membership : Specs.P205.Families.UpperShadowMembership.{u} := by
  intro α _ _ k A hA t
  rw [Finset.mem_upShadow_iff_exists_mem_card_add_one]
  constructor
  · rintro ⟨s, hs, hst, ht⟩
    exact ⟨by simpa [hA s hs] using ht, s, hs, hst⟩
  · rintro ⟨ht, s, hs, hst⟩
    exact ⟨s, hs, hst, by simpa [hA s hs] using ht⟩

end P205.Families
