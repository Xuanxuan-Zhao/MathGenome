import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FieldFormalSmoothness
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FlatSquareZeroFormalSmoothness
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TensorProduct.Quotient

namespace CommutativeAlgebraNotes.CoefficientRings

open Ideal

private theorem formallySmooth_quotient_step {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] {I J : Ideal R} (hIJ : I ≤ J) (hJI : J ^ 2 ≤ I)
    (hSmooth : Algebra.FormallySmooth (R ⧸ J) (S ⧸ J.map (algebraMap R S))) :
    Algebra.FormallySmooth (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  let A := R ⧸ I
  let B := S ⧸ I.map (algebraMap R S)
  let K : Ideal A := J.map (Ideal.Quotient.mk I)
  have : Module.Flat A B :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  have hK : K ^ 2 = ⊥ := by
    change (J.map (Ideal.Quotient.mk I)) ^ 2 = ⊥
    rw [← Ideal.map_pow]
    exact le_antisymm ((Ideal.map_mono hJI).trans (Ideal.map_quotient_self I).le) bot_le
  apply formallySmooth_of_flat_of_squareZero_quotient K hK
  have hmap : K.map (algebraMap A B) =
      (J.map (algebraMap R S)).map (Ideal.Quotient.mk (I.map (algebraMap R S))) := by
    dsimp only [K, A, B]
    rw [Ideal.map_map, Ideal.map_map]
    rfl
  let eA := DoubleQuot.quotQuotEquivQuotOfLE hIJ
  let eB := (Ideal.quotEquivOfEq hmap).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hIJ))
  apply RingHom.formallySmooth_algebraMap.mp
  have hcomm : eB.toRingHom.comp (algebraMap (A ⧸ K) (B ⧸ K.map (algebraMap A B))) =
      (algebraMap (R ⧸ J) (S ⧸ J.map (algebraMap R S))).comp eA.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  have h : (eB.toRingHom.comp
      (algebraMap (A ⧸ K) (B ⧸ K.map (algebraMap A B)))).FormallySmooth := by
    rw [hcomm]
    exact (RingHom.FormallySmooth.of_bijective (f := eA.toRingHom) eA.bijective).comp
      (RingHom.formallySmooth_algebraMap.mpr hSmooth)
  have hcancel : eB.symm.toRingHom.comp eB.toRingHom = RingHom.id _ := eB.symm_comp
  simpa only [← RingHom.comp_assoc, hcancel, RingHom.id_comp] using
    h.comp (RingHom.FormallySmooth.of_bijective (f := eB.symm.toRingHom) eB.symm.bijective)

private theorem cohenRingCharZero (Λ : Type*) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] (p : ℕ) [Fact p.Prime]
    (hgen : Ideal.span {(p : Λ)} = IsLocalRing.maximalIdeal Λ) : CharZero Λ := by
  have hpne : (p : Λ) ≠ 0 := by
    intro hp
    apply IsDiscreteValuationRing.not_a_field Λ
    rw [← hgen, hp, Ideal.span_singleton_zero]
  have hpnu : ¬ IsUnit (p : Λ) := by
    change (p : Λ) ∈ nonunits Λ
    rw [← IsLocalRing.mem_maximalIdeal, ← hgen]
    exact Ideal.subset_span (Set.mem_singleton _)
  apply (CharP.ringChar_zero_iff_CharZero (R := Λ)).mp
  rcases CharP.char_is_prime_or_zero Λ (ringChar Λ) with hprime | hzero
  · have hd : p ∣ ringChar Λ := by
      by_contra h
      exact hpnu ((isUnit_iff_not_dvd_char_of_ringChar_ne_zero Λ p hprime.ne_zero).mpr h)
    have hEq : p = ringChar Λ :=
      ((Nat.dvd_prime hprime).mp hd).resolve_left (Fact.out : p.Prime).ne_one
    exact (hpne (hEq.symm ▸ CharP.cast_eq_zero Λ (ringChar Λ))).elim
  · exact hzero

private theorem cohenRingIntQuotientSmoothness (Λ : Type*) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [CharZero Λ] (p : ℕ) [Fact p.Prime]
    (hgen : Ideal.span {(p : Λ)} = IsLocalRing.maximalIdeal Λ) (m : ℕ) :
    let J : Ideal ℤ := Ideal.span {(p : ℤ)}
    Algebra.FormallySmooth (ℤ ⧸ J ^ (m + 1))
      (Λ ⧸ (J ^ (m + 1)).map (algebraMap ℤ Λ)) := by
  let J : Ideal ℤ := Ideal.span {(p : ℤ)}
  change Algebra.FormallySmooth (ℤ ⧸ J ^ (m + 1))
    (Λ ⧸ (J ^ (m + 1)).map (algebraMap ℤ Λ))
  induction m with
  | zero =>
    change Algebra.FormallySmooth (ℤ ⧸ J ^ 1) (Λ ⧸ (J ^ 1).map (algebraMap ℤ Λ))
    rw [pow_one]
    have hmap : J.map (algebraMap ℤ Λ) = IsLocalRing.maximalIdeal Λ := by
      simpa [J, Ideal.map_span] using hgen
    let L := Λ ⧸ J.map (algebraMap ℤ Λ)
    have : (J.map (algebraMap ℤ Λ)).IsMaximal := by
      rw [hmap]
      infer_instance
    let : Field L := Ideal.Quotient.field _
    have hpzero : (p : L) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (J.map (algebraMap ℤ Λ)))]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [hmap, ← hgen]
      exact Ideal.subset_span (Set.mem_singleton _)
    let : CharP L p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpzero
    let : Algebra (ZMod p) L := ZMod.algebra L p
    let e : (ℤ ⧸ J) ≃+* ↥(⊥ : Subfield L) :=
      (Int.quotientSpanNatEquivZMod p).trans (Subfield.botEquivZMod L p).symm
    have hcomp : (algebraMap (↥(⊥ : Subfield L)) L).comp e.toRingHom =
        algebraMap (ℤ ⧸ J) L := by
      apply Ideal.Quotient.ringHom_ext
      exact Subsingleton.elim _ _
    apply RingHom.formallySmooth_algebraMap.mp
    rw [← hcomp]
    exact (RingHom.FormallySmooth.of_bijective (f := e.toRingHom) e.bijective).comp
      (RingHom.formallySmooth_algebraMap.mpr (primeSubfieldFormallySmooth L))
  | succ m ih =>
    have hIJ : J ^ (m + 1 + 1) ≤ J ^ (m + 1) :=
      Ideal.pow_le_pow_right (Nat.le_succ _)
    have hJI : (J ^ (m + 1)) ^ 2 ≤ J ^ (m + 1 + 1) := by
      rw [← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    exact formallySmooth_quotient_step hIJ hJI ih

/-- Every positive truncation of a complete DVR with uniformizer `p` is
formally smooth over the integers modulo the same power of `p`. -/
theorem cohenRingTruncationSmoothness (Λ : Type*) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    (p : ℕ) [Fact p.Prime] (hgen : Ideal.span {(p : Λ)} = IsLocalRing.maximalIdeal Λ)
    (n : ℕ) (hn : 1 ≤ n) :
    let I : Ideal Λ := Ideal.span {(p : Λ) ^ n}
    let f : ZMod (p ^ n) →+* Λ ⧸ I :=
      ZMod.castHom (ringChar.dvd (R := Λ ⧸ I) (by
        rw [Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk I), ← map_pow]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))) _
    f.FormallySmooth := by
  let : CharZero Λ := cohenRingCharZero Λ p hgen
  let J : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hs : Algebra.FormallySmooth (ℤ ⧸ J ^ n) (Λ ⧸ (J ^ n).map (algebraMap ℤ Λ)) := by
    cases n with
    | zero => omega
    | succ m => exact cohenRingIntQuotientSmoothness Λ p hgen m
  have hint : Ideal.span {((p ^ n : ℕ) : ℤ)} = J ^ n := by
    simp [J, Ideal.span_singleton_pow]
  have hΛ : (J ^ n).map (algebraMap ℤ Λ) = Ideal.span {(p : Λ) ^ n} := by
    simp [J, Ideal.map_span, Ideal.span_singleton_pow]
  let e := (Int.quotientSpanNatEquivZMod (p ^ n)).symm.trans (Ideal.quotEquivOfEq hint)
  let eΛ := Ideal.quotEquivOfEq hΛ
  dsimp only
  convert ((RingHom.FormallySmooth.of_bijective (f := e.toRingHom) e.bijective).comp
    (RingHom.formallySmooth_algebraMap.mpr hs)).comp
    (RingHom.FormallySmooth.of_bijective (f := eΛ.toRingHom) eΛ.bijective) using 1
  exact Subsingleton.elim _ _

end CommutativeAlgebraNotes.CoefficientRings
