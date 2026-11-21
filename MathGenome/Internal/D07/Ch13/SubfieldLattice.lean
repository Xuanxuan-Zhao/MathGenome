import MathGenome.Internal.Specs.D07.Ch13.SubfieldLattice
import MathGenome.Internal.D07.Ch13.Existence
import MathGenome.Internal.D07.Ch13.Uniqueness
import MathGenome.Internal.D07.Ch12.TowerLaw
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! The divisor classification of actual embedded finite fields. -/

universe u v

namespace D07.Ch13.SubfieldLattice

open Specs.D07.Ch13.SubfieldLattice

/-- Iterating a power map that fixes x still fixes x. -/
theorem pow_pow_eq_self {F : Type*} [Monoid F] {x : F} {a : ℕ}
    (h : x ^ a = x) (k : ℕ) : x ^ (a ^ k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, h]

/-- This containment uses only the root-set characterization, not Galois
correspondence or a classification of embeddings. -/
theorem root_field_le_of_dvd (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] [Finite K]
    (q d n : ℕ) (hq : Nat.card K = q) (h : d ∣ n) :
    Existence.rootField K Ω q d ≤ Existence.rootField K Ω q n := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  apply (Existence.root_field_membership K Ω q (d * k) hq x).mpr
  rw [pow_mul]
  exact pow_pow_eq_self ((Existence.root_field_membership K Ω q d hq x).mp hx) k

theorem divisor_field : DivisorField.{u, v} := by
  intro K Ω _ _ _ _ _ _ q n d hq _hn hd hdn
  have h := Existence.embedded_existence K Ω q d hq hd
  refine ⟨root_field_le_of_dvd K Ω q d n hq hdn, h.1, h.2.1,
    h.2.2.1, h.2.2.2.1, Existence.root_field_membership K Ω q d hq, ?_⟩
  intro M hfinite hcard
  let := hfinite
  exact Uniqueness.embedded_field_eq_root_field K Ω q d hq M hcard h.1 h.2.1

/-- Tower divisibility and the coordinate count determine an intermediate
field's degree and size; embedded uniqueness then identifies its actual set. -/
theorem embedded_classification : EmbeddedClassification.{u, v} := by
  intro K Ω _ _ _ _ _ _ q n hq hn E
  have hF := Existence.embedded_existence K Ω q n hq hn
  let F := Existence.rootField K Ω q n
  let : Finite F := hF.1
  let : FiniteDimensional K F := hF.2.2.1
  constructor
  · intro hEF
    let : Finite E := Finite.of_injective (IntermediateField.inclusion hEF)
      (IntermediateField.inclusion hEF).injective
    let : FiniteDimensional K E := Module.Finite.of_finite
    let d := Module.finrank K E
    have hd : 1 ≤ d := Module.finrank_pos
    have hdn : d ∣ n := by
      rw [← hF.2.2.2.1]
      exact IntermediateField.finrank_dvd_of_le_right hEF
    have hD := Existence.embedded_existence K Ω q d hq hd
    have hcard : Nat.card E = q ^ d := by
      rw [Module.natCard_eq_pow_finrank (K := K), hq]
    have hE : E = Existence.rootField K Ω q d :=
      Uniqueness.embedded_field_eq_root_field K Ω q d hq E hcard hD.1 hD.2.1
    refine ⟨d, ⟨hd, hdn, hE⟩, ?_⟩
    intro e he
    have hDeg := (Existence.embedded_existence K Ω q e hq he.1).2.2.2.1
    change e = Module.finrank K E
    rw [he.2.2]
    exact hDeg.symm
  · rintro ⟨d, ⟨_hd, hdn, rfl⟩, _⟩
    exact root_field_le_of_dvd K Ω q d n hq hdn

/-- Unital subfields contain every element of the embedded prime field. -/
theorem prime_field_mem (p : ℕ) [Fact p.Prime] (Ω : Type v)
    [Field Ω] [Algebra (ZMod p) Ω] (S : Subfield Ω) (a : ZMod p) :
    algebraMap (ZMod p) Ω a ∈ S := by
  rw [← ZMod.natCast_zmod_val a, map_natCast]
  exact natCast_mem S a.val

theorem prime_subfield_classification : PrimeSubfieldClassification.{v} := by
  intro p _ Ω _ _ _ _ n hn S
  let E : IntermediateField (ZMod p) Ω :=
    S.toIntermediateField (prime_field_mem p Ω S)
  have h := embedded_classification (ZMod p) Ω p n (Nat.card_zmod p) hn E
  change E ≤ Existence.rootField (ZMod p) Ω p n ↔ _
  rw [h]
  constructor
  · rintro ⟨d, ⟨hd, hdn, hE⟩, huniq⟩
    refine ⟨d, ⟨hd, hdn, congrArg IntermediateField.toSubfield hE⟩, ?_⟩
    intro e he
    apply huniq e
    refine ⟨he.1, he.2.1, ?_⟩
    apply IntermediateField.toSubfield_injective
    exact he.2.2
  · rintro ⟨d, ⟨hd, hdn, hS⟩, huniq⟩
    refine ⟨d, ⟨hd, hdn, IntermediateField.toSubfield_injective hS⟩, ?_⟩
    intro e he
    exact huniq e ⟨he.1, he.2.1, congrArg IntermediateField.toSubfield he.2.2⟩

end D07.Ch13.SubfieldLattice
