import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.RootFields
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteIngredients.SeparableSplittingField

/-!
# Root fields in the chosen algebraic closure (FT-E01)

The fixed field of the n-fold q-power map is exactly the root set of
`X^(q^n)-X`. Separability and splitting count its elements. Adjoining this
root set changes nothing, giving the splitting-field and finite Galois claims.
Counting vectors gives the degree. Any competing subfield of the same size
satisfies the same power identity, so inclusion and counting give equality.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

/-- The root fields, all inside the specified ambient field. -/
abbrev finiteRootField (k : Type u) (Ω : Type v) [Field k] [Fintype k]
    [Field Ω] [Algebra k Ω] (n : ℕ) : IntermediateField k Ω :=
  Specs.AdvancedFieldTheory.rootField k Ω n

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]

@[simp] theorem mem_finiteRootField (n : ℕ) (x : Ω) :
    x ∈ finiteRootField k Ω n ↔ x ^ (Fintype.card k ^ n) = x := by
  change ((FiniteField.frobeniusAlgHom k Ω) ^ n) x = x ↔ _
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

theorem finiteRootField_contains_base (n : ℕ) (a : k) :
    algebraMap k Ω a ∈ finiteRootField k Ω n :=
  (finiteRootField k Ω n).algebraMap_mem a

theorem finiteRootField_operations (n : ℕ) :
    (0 : Ω) ∈ finiteRootField k Ω n ∧ (1 : Ω) ∈ finiteRootField k Ω n ∧
    (∀ x y : Ω, x ∈ finiteRootField k Ω n → y ∈ finiteRootField k Ω n →
      x + y ∈ finiteRootField k Ω n) ∧
    (∀ x y : Ω, x ∈ finiteRootField k Ω n → y ∈ finiteRootField k Ω n →
      x - y ∈ finiteRootField k Ω n) ∧
    (∀ x y : Ω, x ∈ finiteRootField k Ω n → y ∈ finiteRootField k Ω n →
      x * y ∈ finiteRootField k Ω n) ∧
    (∀ x : Ω, x ∈ finiteRootField k Ω n → x⁻¹ ∈ finiteRootField k Ω n) := by
  let F := finiteRootField k Ω n
  exact ⟨F.zero_mem, F.one_mem, fun _ _ hx hy => F.add_mem hx hy,
    fun _ _ hx hy => F.sub_mem hx hy, fun _ _ hx hy => F.mul_mem hx hy,
    fun _ hx => F.inv_mem hx⟩

open Polynomial in
theorem finiteRootField_rootSet (n : ℕ) (hn : 0 < n) :
    (X ^ (Fintype.card k ^ n) - X : Polynomial k).rootSet Ω =
      (finiteRootField k Ω n : Set Ω) := by
  ext x
  rw [mem_rootSet_of_ne (FiniteField.X_pow_card_pow_sub_X_ne_zero k hn.ne'
    Fintype.one_lt_card)]
  change _ ↔ x ∈ finiteRootField k Ω n
  rw [mem_finiteRootField]
  simp only [map_sub, aeval_X_pow, aeval_X, sub_eq_zero]

open Polynomial in
private theorem rootPolynomial_separable (n : ℕ) (hn : 0 < n) :
    (X ^ (Fintype.card k ^ n) - X : Polynomial k).Separable := by
  obtain ⟨p, hc, f, hp, hcard⟩ := FiniteField.card' k
  let : CharP k p := hc
  apply galois_poly_separable p
  rw [hcard, ← pow_mul]
  exact dvd_pow_self p (Nat.mul_pos f.pos hn).ne'

variable [IsAlgClosure k Ω]

open Polynomial in
theorem finiteRootField_card (n : ℕ) (hn : 0 < n) :
    Nat.card (finiteRootField k Ω n) = Fintype.card k ^ n := by
  have h := card_rootSet_eq_natDegree (K := Ω) (rootPolynomial_separable k n hn)
    ((IsAlgClosure.isAlgClosed k).splits _)
  rw [← Nat.card_eq_fintype_card, finiteRootField_rootSet k Ω n hn] at h
  exact h.trans (FiniteField.X_pow_card_pow_sub_X_natDegree_eq k hn.ne'
    Fintype.one_lt_card)

open Polynomial in
theorem finiteRootField_isSplittingField (n : ℕ) (hn : 0 < n) :
    IsSplittingField k (finiteRootField k Ω n)
      (X ^ (Fintype.card k ^ n) - X : Polynomial k) := by
  have heq : IntermediateField.adjoin k
      ((X ^ (Fintype.card k ^ n) - X : Polynomial k).rootSet Ω) =
      finiteRootField k Ω n := by
    rw [finiteRootField_rootSet k Ω n hn]
    exact IntermediateField.adjoin_self _ _
  rw [← heq]
  exact IntermediateField.adjoin_rootSet_isSplittingField ((IsAlgClosure.isAlgClosed k).splits _)

theorem finiteRootField_finite_galois (n : ℕ) (hn : 0 < n) :
    FiniteDimensional k (finiteRootField k Ω n) ∧ IsGalois k (finiteRootField k Ω n) := by
  let := finiteRootField_isSplittingField k Ω n hn
  exact ⟨Polynomial.IsSplittingField.finiteDimensional _
    (Polynomial.X ^ (Fintype.card k ^ n) - Polynomial.X : Polynomial k),
    IsGalois.of_separable_splitting_field (rootPolynomial_separable k n hn)⟩

theorem finiteRootField_finrank (n : ℕ) (hn : 0 < n) :
    Module.finrank k (finiteRootField k Ω n) = n := by
  let := (finiteRootField_finite_galois k Ω n hn).1
  let : Finite (finiteRootField k Ω n) :=
    (Nat.card_pos_iff.mp (by rw [finiteRootField_card k Ω n hn]; exact pow_pos Fintype.card_pos n)).2
  apply Nat.pow_right_injective (a := Fintype.card k) Fintype.one_lt_card
  change Fintype.card k ^ Module.finrank k (finiteRootField k Ω n) = _
  rw [← Nat.card_eq_fintype_card (α := k), ← Module.natCard_eq_pow_finrank,
    Nat.card_eq_fintype_card (α := k)]
  exact finiteRootField_card k Ω n hn

theorem finiteRootField_unique (n : ℕ) (hn : 0 < n) (S : Subfield Ω)
    (hS : Nat.card S = Fintype.card k ^ n) : S = (finiteRootField k Ω n).toSubfield := by
  have hpos : 0 < Fintype.card k ^ n := pow_pos Fintype.card_pos n
  let : Finite S := (Nat.card_pos_iff.mp (hS ▸ hpos)).2
  let : Finite (finiteRootField k Ω n) :=
    (Nat.card_pos_iff.mp ((finiteRootField_card k Ω n hn) ▸ hpos)).2
  let : Fintype S := Fintype.ofFinite S
  let : Fintype (finiteRootField k Ω n) := Fintype.ofFinite _
  have hle : (S : Set Ω) ⊆ (finiteRootField k Ω n : Set Ω) := by
    intro x hx
    change x ∈ finiteRootField k Ω n
    rw [mem_finiteRootField]
    have h := congrArg (fun z : S => (z : Ω)) (FiniteField.pow_card (⟨x, hx⟩ : S))
    rw [← hS, Nat.card_eq_fintype_card]
    simpa only [SubmonoidClass.coe_pow] using h
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_card_le hle
  change Fintype.card (finiteRootField k Ω n) ≤ Fintype.card S
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    finiteRootField_card k Ω n hn, hS]

theorem finiteRootField_one : finiteRootField k Ω 1 = ⊥ := by
  let := (finiteRootField_finite_galois k Ω 1 Nat.zero_lt_one).1
  symm
  apply IntermediateField.eq_of_le_of_finrank_eq bot_le
  rw [IntermediateField.finrank_bot, finiteRootField_finrank k Ω 1 Nat.zero_lt_one]

end AdvancedFieldTheory
