import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization.SubsetIdentity

noncomputable section

namespace D05.M15.PolynomialPolarization.SubsetIdentity

open scoped BigOperators
open D05.M15.PolynomialPolarization
open Finset

/-- Pair subsets with and without an index unused by the expanded tuple. -/
theorem missing_index_cancellation :
    Specs.D05.M15.PolynomialPolarization.SubsetIdentity.missing_index_cancellation := by
  intro K _ p f a ha
  classical
  let t : Finset (Fin p) := univ.erase a
  let F : Finset (Fin p) → K := fun S =>
    if ∀ i, f i ∈ S then (-1 : K) ^ (p - S.card) else 0
  have hat : a ∉ t := by simp [t]
  have hfull : insert a t = univ := by simp [t]
  have hpair (S : Finset (Fin p)) (hS : S ∈ t.powerset) : F S + F (insert a S) = 0 := by
    have hsub : S ⊆ t := mem_powerset.mp hS
    have han : a ∉ S := fun h => hat (hsub h)
    have hcard : S.card < p := by
      have h := card_le_card hsub
      have hap : 0 < p := lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
      simp only [t, card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin] at h
      omega
    have hmem : (∀ i, f i ∈ insert a S) ↔ ∀ i, f i ∈ S := by
      simp only [mem_insert]
      constructor
      · intro h i
        exact (h i).resolve_left (ha i)
      · intro h i
        exact Or.inr (h i)
    simp only [F, hmem, card_insert_of_notMem han]
    split_ifs with h
    · have he : p - S.card = (p - (S.card + 1)) + 1 := by omega
      rw [he, pow_succ]
      ring
    · simp
  have hsum : (∑ S ∈ t.powerset, F S) + (∑ S ∈ t.powerset, F (insert a S)) = 0 := by
    rw [← sum_add_distrib]
    exact sum_eq_zero hpair
  rw [← sum_powerset_insert hat, hfull, powerset_univ] at hsum
  exact hsum

/-- A surjective choice of `p` indices in `p` slots uses each exactly once. -/
def surjectionsEquivPerm (p : ℕ) :
    {f : Fin p → Fin p // Function.Surjective f} ≃ Equiv.Perm (Fin p) where
  toFun f := Equiv.ofBijective f.1
    ⟨Finite.injective_iff_surjective.mpr f.2, f.2⟩
  invFun σ := ⟨σ, σ.surjective⟩
  left_inv _ := rfl
  right_inv σ := by ext i; rfl

theorem survivor_count :
    Specs.D05.M15.PolynomialPolarization.SubsetIdentity.survivor_count := by
  classical
  intro p
  constructor
  · intro f
    exact ⟨fun h => ⟨Finite.injective_iff_surjective.mpr h, h⟩, fun h => h.2⟩
  · have h := Fintype.card_congr (surjectionsEquivPerm p)
    simpa [Fintype.card_subtype, Fintype.card_perm] using h

theorem survivor_sum :
    Specs.D05.M15.PolynomialPolarization.SubsetIdentity.survivor_sum := by
  intro K V _ _ _ p B hB v
  classical
  calc
    (∑ f : Fin p → Fin p, if Function.Surjective f then B (v ∘ f) else 0) =
        ∑ f : {f : Fin p → Fin p // Function.Surjective f}, B (v ∘ f.1) := by
          rw [← sum_filter]
          exact Finset.sum_subtype _ (by simp) _
    _ = ∑ σ : Equiv.Perm (Fin p), B (v ∘ σ) := by
      exact Fintype.sum_equiv (surjectionsEquivPerm p) _ _ (fun _ => rfl)
    _ = (p.factorial : K) * B v := by
      simp_rw [show ∀ σ : Equiv.Perm (Fin p), B (v ∘ σ) = B v from fun σ => hB σ v]
      simp [Fintype.card_perm, nsmul_eq_mul]

/-- Expansion of a subset diagonal into choices of one occurrence in each slot. -/
theorem diagonal_expansion {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p : ℕ} (B : MultilinearMap K (fun _ : Fin p => V) K)
    (v : Fin p → V) (S : Finset (Fin p)) :
    rawDiagonal B (∑ i ∈ S, v i) =
      ∑ f : Fin p → Fin p, if ∀ i, f i ∈ S then B (v ∘ f) else 0 := by
  classical
  unfold rawDiagonal
  rw [B.map_sum_finset (fun _ j => v j) (fun _ => S)]
  rw [← sum_filter]
  apply sum_congr
  · ext f
    simp
  · intro f _
    rfl

/-- The total coefficient is one exactly for tuples using all indices. -/
theorem support_coefficient {K : Type*} [Field K] (p : ℕ) (f : Fin p → Fin p) :
    (∑ S : Finset (Fin p), if ∀ i, f i ∈ S then (-1 : K) ^ (p - S.card) else 0) =
      if Function.Surjective f then 1 else 0 := by
  classical
  by_cases hf : Function.Surjective f
  · have hcond (S : Finset (Fin p)) : (∀ i, f i ∈ S) ↔ S = univ := by
      constructor
      · intro h
        apply eq_univ_iff_forall.mpr
        intro a
        obtain ⟨i, rfl⟩ := hf a
        exact h i
      · rintro rfl
        simp
    simp_rw [hcond]
    simp [hf]
  · rw [ite_eq_right hf]
    have hmiss : ∃ a, ∀ i, f i ≠ a := by
      simpa only [Function.Surjective, not_forall, not_exists] using hf
    obtain ⟨a, ha⟩ := hmiss
    exact missing_index_cancellation p f a ha

theorem subset_identity :
    Specs.D05.M15.PolynomialPolarization.SubsetIdentity.subset_identity := by
  intro K V _ _ _ p B hB v
  classical
  rw [← survivor_sum p B hB v]
  symm
  calc
    (∑ S : Finset (Fin p), (-1 : K) ^ (p - S.card) * rawDiagonal B (∑ i ∈ S, v i)) =
        ∑ S : Finset (Fin p), ∑ f : Fin p → Fin p,
          if ∀ i, f i ∈ S then (-1 : K) ^ (p - S.card) * B (v ∘ f) else 0 := by
      apply sum_congr rfl
      intro S _
      rw [diagonal_expansion, mul_sum]
      apply sum_congr rfl
      intro f _
      split_ifs <;> simp
    _ = ∑ f : Fin p → Fin p,
        (∑ S : Finset (Fin p), if ∀ i, f i ∈ S then (-1 : K) ^ (p - S.card) else 0) *
          B (v ∘ f) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro f _
      rw [sum_mul]
      apply sum_congr rfl
      intro S _
      split_ifs <;> simp
    _ = ∑ f : Fin p → Fin p, if Function.Surjective f then B (v ∘ f) else 0 := by
      simp_rw [support_coefficient]
      apply sum_congr rfl
      intro f _
      split_ifs <;> simp

theorem polarization_formula :
    Specs.D05.M15.PolynomialPolarization.SubsetIdentity.polarization_formula := by
  intro K V _ _ _ _ p B hB v
  rw [← subset_identity p B hB v, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)), one_mul]

theorem raw_diagonal_injective :
    Specs.D05.M15.PolynomialPolarization.SubsetIdentity.raw_diagonal_injective := by
  intro K V _ _ _ _ p B C hB hC hdiag
  ext v
  rw [polarization_formula p B hB v, polarization_formula p C hC v, hdiag]

theorem degree_zero :
    Specs.D05.M15.PolynomialPolarization.SubsetIdentity.degree_zero := by
  intro K V _ _ _ B v
  constructor
  · simp
  · simp [rawDiagonal]
    exact congrArg B (Subsingleton.elim _ _)

end D05.M15.PolynomialPolarization.SubsetIdentity
