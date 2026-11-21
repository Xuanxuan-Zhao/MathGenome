import MathGenome.Internal.Specs.D07.Ch13.Existence
import MathGenome.Internal.D07.Ch13.Frobenius
import MathGenome.Internal.D07.Ch13.PrimePowerCardinality
import MathGenome.Internal.D07.Ch12.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic

/-! The root-field construction for K07.13.existence. -/

universe u v

namespace D07.Ch13.Existence

open Polynomial Specs.D07.Ch13.Existence

noncomputable abbrev rootField : RootFieldType.{u, v} := rootFieldValue

/-- Iterating the relative Frobenius gives the q^n-power map, over the
specified base K. Surjectivity or finite order of Frobenius is not used. -/
theorem iterated_frobenius (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] [Finite K]
    (q n : ℕ) (hq : Nat.card K = q) :
    ∃ φ : Ω →ₐ[K] Ω, ∀ x, φ x = x ^ (q ^ n) := by
  obtain ⟨φ, hφ⟩ := Frobenius.relative_endomorphism K Ω q hq
  refine ⟨φ ^ n, ?_⟩
  intro x
  rw [AlgHom.coe_pow, show ⇑φ = (fun x : Ω => x ^ q) from funext hφ, pow_iterate]

/-- The fixed elements of any algebra endomorphism form an intermediate field. -/
def fixedElements (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] (φ : Ω →ₐ[K] Ω) :
    IntermediateField K Ω :=
  (φ.toRingHom.eqLocusField (RingHom.id Ω)).toIntermediateField
    (fun c => φ.commutes c)

theorem root_field_membership : RootFieldMembership.{u, v} := by
  intro K Ω _ _ _ _ q n hq x
  obtain ⟨φ, hφ⟩ := iterated_frobenius K Ω q n hq
  have hfixed : ∀ x : Ω, x ∈ fixedElements K Ω φ ↔ x ^ (q ^ n) = x := by
    intro x
    change φ x = x ↔ _
    rw [hφ]
  constructor
  · intro hx
    apply (hfixed x).mp
    apply (IntermediateField.adjoin_le_iff.mpr (fun a ha => (hfixed a).mpr ha)) hx
  · intro hx
    exact IntermediateField.subset_adjoin K {x : Ω | x ^ (q ^ n) = x} hx

/-- The roots of the defining polynomial, viewed as an actual subset of Ω. -/
theorem polynomial_root_set (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] [Finite K]
    (q n : ℕ) (hq : Nat.card K = q) (hn : 1 ≤ n) :
    (X ^ (q ^ n) - X : Polynomial K).rootSet Ω =
      {x : Ω | x ^ (q ^ n) = x} := by
  let := Fintype.ofFinite K
  have hq1 : 1 < q := hq ▸ Finite.one_lt_card
  have hf := FiniteField.X_pow_card_pow_sub_X_ne_zero K (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)) hq1
  ext x
  simp [mem_rootSet_of_ne hf, sub_eq_zero]

/-- Separability follows from the constant derivative -1. -/
theorem defining_polynomial_separable (K : Type u) [Field K] [Finite K]
    (q n : ℕ) (hq : Nat.card K = q) (hn : 1 ≤ n) :
    (X ^ (q ^ n) - X : Polynomial K).Separable := by
  let := Fintype.ofFinite K
  have hqzero : (q : K) = 0 := by
    rw [← hq, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero K
  have hqnzero : ((q ^ n : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, hqzero, zero_pow (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))]
  have hd : (X ^ (q ^ n) - X : Polynomial K).derivative = -1 := by
    simp [derivative_sub, derivative_X_pow, hqnzero]
  rw [Polynomial.separable_def, hd]
  exact isCoprime_one_right.neg_right

/-- The construction works even in a closed overfield larger than an algebraic
closure: only closedness is needed to count the roots. -/
theorem root_field_properties (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] [Finite K] [IsAlgClosed Ω]
    (q n : ℕ) (hq : Nat.card K = q) (hn : 1 ≤ n) :
    let E := rootField K Ω q n
    Finite E ∧ Nat.card E = q ^ n ∧
      FiniteDimensional K E ∧ Module.finrank K E = n ∧
      (X ^ (q ^ n) - X : Polynomial K) ≠ 0 ∧
      (X ^ (q ^ n) - X : Polynomial K).Separable ∧
      Polynomial.IsSplittingField K E (X ^ (q ^ n) - X) := by
  let := Fintype.ofFinite K
  let f : Polynomial K := X ^ (q ^ n) - X
  let E := rootField K Ω q n
  have hq1 : 1 < q := hq ▸ Finite.one_lt_card
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hf : f ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero K hn0 hq1
  have hdegree : f.natDegree = q ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hn0 hq1
  have hsep : f.Separable := defining_polynomial_separable K q n hq hn
  have hs : (f.map (algebraMap K Ω)).Splits := IsAlgClosed.splits _
  have hroots : f.rootSet Ω = {x : Ω | x ^ (q ^ n) = x} :=
    polynomial_root_set K Ω q n hq hn
  have hE : E = IntermediateField.adjoin K (f.rootSet Ω) := by
    change IntermediateField.adjoin K _ = _
    rw [hroots]
  let : Polynomial.IsSplittingField K E f := by
    rw [hE]
    exact IntermediateField.adjoin_rootSet_isSplittingField hs
  let : FiniteDimensional K E := Polynomial.IsSplittingField.finiteDimensional E f
  obtain ⟨hfinite, _, hcount⟩ := PrimePowerCardinality.extension_cardinality K E
  have hset : (E : Set Ω) = f.rootSet Ω := by
    ext x
    rw [hroots]
    exact root_field_membership K Ω q n hq x
  have hcard : Nat.card E = q ^ n := by
    calc
      Nat.card E = Nat.card (f.rootSet Ω) := congrArg (fun s : Set Ω => Nat.card s) hset
      _ = q ^ n := by
        rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep hs, hdegree]
  have hfinrank : Module.finrank K E = n := by
    apply Nat.pow_right_injective hq1
    change q ^ Module.finrank K E = q ^ n
    calc
      q ^ Module.finrank K E = Nat.card E := by rw [← hq, ← hcount]
      _ = q ^ n := hcard
  exact ⟨hfinite, hcard, inferInstance, hfinrank, hf, hsep, inferInstance⟩

theorem embedded_existence : EmbeddedExistence.{u, v} := by
  intro K Ω _ _ _ _ _ _ q n hq hn
  exact root_field_properties K Ω q n hq hn

theorem prime_power_existence : PrimePowerExistence := by
  intro p n hp hn
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Ω, hΩ, aΩ, _, halg, hclosed⟩ :=
    D07.Ch12.AlgebraicClosure.existence (ZMod p)
  let := hΩ
  let := aΩ
  let := halg
  let := hclosed
  have h := embedded_existence (ZMod p) Ω p n (Nat.card_zmod p) hn
  exact ⟨rootField (ZMod p) Ω p n, inferInstance, h.1, h.2.1⟩

end D07.Ch13.Existence
