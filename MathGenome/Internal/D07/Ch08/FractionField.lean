import MathGenome.Internal.Specs.D07.Ch08.FractionField
import MathGenome.Internal.D07.Ch08.ZeroDivisorCancellation

/-! The fraction-field construction of K07.08.fraction_field.
The canonical quotient and its field structure come from Mathlib. The theorems
identify its classes, equality, and operations with the paper's construction.
-/

universe u v

namespace D07.Ch08.FractionField

open Specs.D07.Ch08.FractionField

theorem fieldConstruction : FieldConstruction.{u} := by
  intro R _ _
  refine ⟨Field.toIsField _, IsFractionRing.injective R (FractionRing R), ?_⟩
  intro x
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective R x
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, hx.symm⟩

theorem existsFractionField : ExistsFractionField.{u} := by
  intro R _ _
  obtain ⟨_, hinj, hrep⟩ := fieldConstruction R
  exact ⟨FractionRing R, inferInstance, algebraMap R (FractionRing R), hinj, hrep⟩

theorem quotientClass : QuotientClass.{u} := by
  intro R _ _ a b hb
  exact FractionRing.mk_eq_div R

theorem fractionEquality : FractionEquality.{u} := by
  intro R _ _ a b c d hb hd
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb
  have hd' : algebraMap R (FractionRing R) d ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hd
  rw [div_eq_div_iff hb' hd']
  simpa only [← map_mul] using (hinj.eq_iff (a := a * d) (b := c * b)).trans
    (by rw [mul_comm c b])

theorem pairRelationEquivalence : PairRelationEquivalence.{u} := by
  intro R _ _
  let f : R × {b : R // b ≠ 0} → FractionRing R := fun p =>
    algebraMap R (FractionRing R) p.1 / algebraMap R (FractionRing R) p.2.1
  have heq (p q : R × {b : R // b ≠ 0}) :
      f p = f q ↔ p.1 * q.2.1 = p.2.1 * q.1 :=
    fractionEquality R p.1 p.2.1 q.1 q.2.1 p.2.2 q.2.2
  refine ⟨fun p => (heq p p).mp rfl, ?_, ?_⟩
  · intro p q hpq
    exact (heq q p).mp ((heq p q).mpr hpq).symm
  · intro p q r hpq hqr
    exact (heq p r).mp (((heq p q).mpr hpq).trans ((heq q r).mpr hqr))

theorem fractionOperations : FractionOperations.{u} := by
  intro R _ _ a b c d hb hd
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb
  have hd' : algebraMap R (FractionRing R) d ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hd
  refine ⟨mul_ne_zero hb hd, ?_, ?_⟩
  · simpa only [map_add, map_mul, mul_comm (algebraMap R (FractionRing R) b)] using
      (div_add_div (algebraMap R (FractionRing R) a)
        (algebraMap R (FractionRing R) c) hb' hd')
  · simp only [map_mul, div_mul_div_comm]

theorem constantsAndNegation : ConstantsAndNegation.{u} := by
  intro R _ _
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro a
    simp
  · intro a b _
    rw [map_neg, neg_div]

theorem fractionZero : FractionZero.{u} := by
  intro R _ _ a b hb
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb
  rw [div_eq_zero_iff, or_iff_left hb']
  exact IsFractionRing.to_map_eq_zero_iff

theorem fractionInverse : FractionInverse.{u} := by
  intro R _ _ a b ha hb
  have hinj := IsFractionRing.injective R (FractionRing R)
  have ha' : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ha
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb
  have hi := inv_div (algebraMap R (FractionRing R) a)
    (algebraMap R (FractionRing R) b)
  refine ⟨hi, ?_, ?_⟩
  · rw [← hi]
    exact mul_inv_cancel₀ (div_ne_zero ha' hb')
  · rw [← hi]
    exact inv_mul_cancel₀ (div_ne_zero ha' hb')

theorem annihilatorKilled : AnnihilatorKilled.{u,v} := by
  intro R _ S _ f b d hbd hb
  apply (ZeroDivisorCancellation.unitZeroProducts S (f b) hb).1 (f d)
  rw [← map_mul, hbd, map_zero]

theorem zeroDivisorObstruction : ZeroDivisorObstruction.{u,v} := by
  intro R _ S _ f b d hd hbd hinj hb
  exact hd (hinj ((annihilatorKilled R S f b d hbd hb).trans (map_zero f).symm))

end D07.Ch08.FractionField
