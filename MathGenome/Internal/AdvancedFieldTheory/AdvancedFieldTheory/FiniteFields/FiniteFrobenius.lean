import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.FiniteFrobenius
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.GlobalFrobenius
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.DivisorLattice

/-!
# Arithmetic Frobenius on finite layers (FT-E04B)

The q-power automorphisms below are restrictions of the same global arithmetic
Frobenius. The relative Galois group is the canonical pointwise stabilizer of
the included smaller layer. Restricting a power to that layer detects exactly
the exponents divisible by its degree.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]

/-- The restriction of global arithmetic Frobenius to the n-th root field. -/
abbrev finiteFrobenius (n : ℕ) : finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n :=
  Specs.AdvancedFieldTheory.layerFrobenius k Ω n

/-- Gal(k_n/k_m), represented as the subgroup fixing the included k_m. -/
abbrev finiteRelativeGaloisGroup {m n : ℕ} (h : m ∣ n) :
    Subgroup (finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) :=
  Specs.AdvancedFieldTheory.relativeLayerGroup k Ω h

@[simp] theorem finiteFrobenius_coe (n : ℕ) (x : finiteRootField k Ω n) :
    (finiteFrobenius k Ω n x : Ω) = globalFrobenius k Ω (x : Ω) := rfl

@[simp] theorem finiteFrobenius_pow_coe (n d : ℕ) (x : finiteRootField k Ω n) :
    ((finiteFrobenius k Ω n ^ d) x : Ω) = (globalFrobenius k Ω ^ d) (x : Ω) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      finiteFrobenius_coe, ih]

theorem finiteRootField_finite (n : ℕ) (hn : 0 < n) : Finite (finiteRootField k Ω n) :=
  (Nat.card_pos_iff.mp (by
    rw [finiteRootField_card k Ω n hn]
    exact pow_pos Fintype.card_pos n)).2

theorem finiteFrobenius_orderOf (n : ℕ) (hn : 0 < n) :
    orderOf (finiteFrobenius k Ω n) = n := by
  let : Finite (finiteRootField k Ω n) := finiteRootField_finite k Ω n hn
  exact (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k
    (finiteRootField k Ω n)).trans (finiteRootField_finrank k Ω n hn)

/-- Every automorphism is a nonnegative power of the specified Frobenius. -/
theorem finiteFrobenius_exists_pow (n : ℕ) (hn : 0 < n)
    (σ : finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) :
    ∃ d : ℕ, finiteFrobenius k Ω n ^ d = σ := by
  let : Finite (finiteRootField k Ω n) := finiteRootField_finite k Ω n hn
  obtain ⟨d, hd⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (finiteRootField k Ω n)).surjective σ
  exact ⟨d.val, hd⟩

theorem finiteFrobenius_generates (n : ℕ) (hn : 0 < n) :
    Subgroup.zpowers (finiteFrobenius k Ω n) = ⊤ := by
  apply (Subgroup.zpowers _).eq_top_iff'.mpr
  intro σ
  obtain ⟨d, rfl⟩ := finiteFrobenius_exists_pow k Ω n hn σ
  exact Subgroup.npow_mem_zpowers _ _

theorem finiteGaloisGroup_card (n : ℕ) (hn : 0 < n) :
    Nat.card (finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) = n := by
  rw [← orderOf_eq_card_of_zpowers_eq_top (finiteFrobenius_generates k Ω n hn)]
  exact finiteFrobenius_orderOf k Ω n hn

omit [IsAlgClosure k Ω] in
@[simp] theorem mem_finiteRelativeGaloisGroup {m n : ℕ} (h : m ∣ n)
    (σ : finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) :
    σ ∈ finiteRelativeGaloisGroup k Ω h ↔
      ∀ x : finiteRootField k Ω m,
        σ (finiteRootFieldInclusion k Ω h x) = finiteRootFieldInclusion k Ω h x := by
  change σ ∈ (finiteRootFieldInclusion k Ω h).fieldRange.fixingSubgroup ↔ _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ x
    exact hσ _ ⟨x, rfl⟩
  · intro hσ y hy
    obtain ⟨x, rfl⟩ := hy
    exact hσ x

theorem finiteFrobenius_pow_orderOf (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : m ∣ n) : orderOf (finiteFrobenius k Ω n ^ m) = n / m := by
  rw [orderOf_pow_of_dvd hm.ne' (by rwa [finiteFrobenius_orderOf k Ω n hn])]
  rw [finiteFrobenius_orderOf k Ω n hn]

/-- Powers on two layers commute with the literal inclusion. -/
theorem finiteFrobenius_pow_inclusion {m n : ℕ} (h : m ∣ n) (d : ℕ)
    (x : finiteRootField k Ω m) :
    (finiteFrobenius k Ω n ^ d) (finiteRootFieldInclusion k Ω h x) =
      finiteRootFieldInclusion k Ω h ((finiteFrobenius k Ω m ^ d) x) := by
  apply Subtype.ext
  simp only [finiteFrobenius_pow_coe, finiteRootFieldInclusion_coe]

theorem finiteRelativeGaloisGroup_eq_zpowers (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : m ∣ n) :
    finiteRelativeGaloisGroup k Ω h = Subgroup.zpowers (finiteFrobenius k Ω n ^ m) := by
  apply le_antisymm
  · intro σ hσ
    obtain ⟨d, rfl⟩ := finiteFrobenius_exists_pow k Ω n hn σ
    have hfix : finiteFrobenius k Ω m ^ d = 1 := by
      apply DFunLike.ext
      intro x
      apply (finiteRootFieldInclusion k Ω h).injective
      change finiteRootFieldInclusion k Ω h ((finiteFrobenius k Ω m ^ d) x) =
        finiteRootFieldInclusion k Ω h x
      rw [← finiteFrobenius_pow_inclusion]
      exact (mem_finiteRelativeGaloisGroup k Ω h _).mp hσ x
    have hd : m ∣ d := by
      rw [← finiteFrobenius_orderOf k Ω m hm]
      exact orderOf_dvd_of_pow_eq_one hfix
    obtain ⟨r, rfl⟩ := hd
    rw [pow_mul]
    exact Subgroup.npow_mem_zpowers _ _
  · apply Subgroup.zpowers_le.mpr
    rw [mem_finiteRelativeGaloisGroup]
    intro x
    rw [finiteFrobenius_pow_inclusion]
    have hpow : finiteFrobenius k Ω m ^ m = 1 := by
      simpa only [finiteFrobenius_orderOf k Ω m hm] using
        pow_orderOf_eq_one (finiteFrobenius k Ω m)
    rw [hpow]
    rfl

theorem finiteRelativeGaloisGroup_card (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : m ∣ n) : Nat.card (finiteRelativeGaloisGroup k Ω h) = n / m := by
  rw [finiteRelativeGaloisGroup_eq_zpowers k Ω m n hm hn h, Nat.card_zpowers]
  exact finiteFrobenius_pow_orderOf k Ω m n hm hn h

end AdvancedFieldTheory
