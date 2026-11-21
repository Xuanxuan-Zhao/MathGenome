import MathGenome.Internal.Specs.D07.Ch13.Uniqueness
import MathGenome.Internal.D07.Ch13.Existence
import MathGenome.Internal.D07.Ch13.PowerIdentity
import MathGenome.Internal.D07.Ch12.SplittingExistenceUniqueness
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Set.Card

/-!
Uniqueness of finite fields with the specified base fixed. A finite field F
is the splitting field of X^|F| - X over any specified subfield. Hence equal
cardinalities give base-preserving isomorphisms by splitting-field uniqueness.
For embedded fields, the power identity gives containment in the canonical
root field; equal finite cardinalities then give equality of the actual sets.
-/

universe u v w

namespace D07.Ch13.Uniqueness

open Polynomial Specs.D07.Ch13.Uniqueness

/-- The finite field itself consists of all the roots, so they generate it. -/
theorem finite_field_splitting (K : Type u) (F : Type v)
    [Field K] [Field F] [Algebra K F] [Finite F] :
    Specs.D07.Ch12.SplittingDefinition.splittingFieldValue K F
      (X ^ Nat.card F - X) := by
  let := Fintype.ofFinite F
  have hf : (X ^ Nat.card F - X : Polynomial K) ≠ 0 := by
    apply FiniteField.X_pow_card_sub_X_ne_zero K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  apply (D07.Ch12.SplittingDefinition.library_characterization K F _ hf).mpr
  simpa only [Nat.card_eq_fintype_card] using FiniteField.isSplittingField_sub F K

/-- The base may be any subfield; the proof preserves its specified embedding. -/
theorem equal_cardinality_over_base (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Finite E] [Finite L] (h : Nat.card E = Nat.card L) :
    Nonempty (E ≃ₐ[K] L) := by
  have hE := finite_field_splitting K E
  have hL := finite_field_splitting K L
  rw [← h] at hL
  exact D07.Ch12.SplittingExistenceUniqueness.uniqueness K E L _ hE hL

theorem prime_power_uniqueness : PrimePowerUniqueness.{u, v} := by
  intro p n _hp _hn E L _ _ _ _ hE hL
  let := Fintype.ofFinite E
  let := Fintype.ofFinite L
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hE, hL])⟩

theorem base_uniqueness : BaseUniqueness.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ n hE hL
  obtain ⟨hfiniteE, _, hcardE⟩ :=
    D07.Ch13.PrimePowerCardinality.extension_cardinality K E
  obtain ⟨hfiniteL, _, hcardL⟩ :=
    D07.Ch13.PrimePowerCardinality.extension_cardinality K L
  let := hfiniteE
  let := hfiniteL
  apply equal_cardinality_over_base K E L
  rw [hcardE, hcardL, hE, hL]

/-- Uniqueness as an actual subfield of the ambient field, not merely up to
isomorphism. Algebraic closedness is needed for existence, not this comparison. -/
theorem embedded_field_eq_root_field (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] [Finite K]
    (q n : ℕ) (hq : Nat.card K = q)
    (E : IntermediateField K Ω) [Finite E]
    (hE : Nat.card E = q ^ n)
    (hF : Finite (Existence.rootField K Ω q n))
    (hcardF : Nat.card (Existence.rootField K Ω q n) = q ^ n) :
    E = Existence.rootField K Ω q n := by
  let F := Existence.rootField K Ω q n
  let := hF
  let := Fintype.ofFinite E
  have hle : E ≤ F := by
    intro x hx
    apply (Existence.root_field_membership K Ω q n hq x).mpr
    have hpow := PowerIdentity.power_identity E (q ^ n)
      (by rw [← Nat.card_eq_fintype_card]; exact hE) ⟨x, hx⟩
    exact congrArg (fun y : E => (y : Ω)) hpow
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite (F : Set Ω))
  change Nat.card F ≤ Nat.card E
  exact (hcardF.trans hE.symm).le

theorem embedded_uniqueness : EmbeddedUniqueness.{u, v} := by
  intro K Ω _ _ _ _ _ _ q n hq hn
  have h := Existence.embedded_existence K Ω q n hq hn
  refine ⟨h.1, h.2.1, ?_⟩
  intro E hfinite hcard
  let := hfinite
  exact embedded_field_eq_root_field K Ω q n hq E hcard h.1 h.2.1

end D07.Ch13.Uniqueness
