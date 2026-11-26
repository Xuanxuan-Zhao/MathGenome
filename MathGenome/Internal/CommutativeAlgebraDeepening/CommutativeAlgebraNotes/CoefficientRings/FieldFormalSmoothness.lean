import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.PrimeField
import Mathlib.RingTheory.Smooth.Field

namespace CommutativeAlgebraNotes.CoefficientRings

open Algebra MvPolynomial

private theorem self_mem_ker_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial L K) :
    p ∈ (Generators.self K L).ker ↔ aeval (R := K) id p = 0 := by
  rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
  rfl

private theorem self_cotangent_coord {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : (Generators.self K L).toExtension.ker) (j : L) :
    (Generators.self K L).cotangentSpaceBasis.repr
        ((Generators.self K L).toExtension.cotangentComplex (Extension.Cotangent.mk p)) j =
      aeval (R := K) id (pderiv j p.val) := by
  erw [Extension.cotangentComplex_mk]
  exact (Generators.self K L).cotangentSpaceBasis_repr_one_tmul p.val j

private theorem mem_ker_sq_of_cotangent_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.FormallySmooth K L]
    (p : (Generators.self K L).toExtension.ker)
    (hp : (Generators.self K L).toExtension.cotangentComplex (Extension.Cotangent.mk p) = 0) :
    (p.val : MvPolynomial L K) ∈ (Generators.self K L).ker ^ 2 := by
  let P := Generators.self K L
  have : Algebra.FormallySmooth K P.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth K (MvPolynomial L K))
  have hinj : Function.Injective P.toExtension.cotangentComplex :=
    P.toExtension.cotangentComplex_injective_iff.mpr
      (Algebra.FormallySmooth.subsingleton_h1Cotangent (R := K) (A := L))
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot'] at hinj
  exact (Extension.Cotangent.mk_eq_zero_iff p).mp (hinj _ hp)

/-- A field extension of a perfect field is formally smooth. -/
theorem fieldFormallySmoothOfPerfect (K L : Type*) [Field K] [PerfectField K]
    [Field L] [Algebra K L] : Algebra.FormallySmooth K L := by
  classical
  let P := Generators.self K L
  have : Algebra.FormallySmooth K P.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth K (MvPolynomial L K))
  refine ⟨inferInstance, P.toExtension.cotangentComplex_injective_iff.mp ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨p, rfl⟩ := Extension.Cotangent.mk_surjective x
  -- A polynomial relation uses only finitely many elements of the field.
  let s : Finset L := (p.val : MvPolynomial L K).vars
  let E := IntermediateField.adjoin K (s : Set L)
  have : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr ⟨s, rfl⟩
  have : Algebra.FormallySmooth K E := Algebra.FormallySmooth.of_perfectField
  let Q := Generators.self K E
  let i : E → L := Subtype.val
  have hi : Function.Injective i := Subtype.val_injective
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range p.val i hi (by
    intro a ha
    exact ⟨⟨a, IntermediateField.subset_adjoin K (s : Set L) ha⟩, rfl⟩)
  have eval_rename (r : MvPolynomial E K) :
      aeval (R := K) id (rename i r) = E.val (aeval (R := K) id r) := by
    rw [aeval_rename, comp_aeval_apply]
    rfl
  have hp := (self_mem_ker_iff (p.val : MvPolynomial L K)).mp p.property
  have hqker : q ∈ Q.ker := by
    apply (self_mem_ker_iff q).mpr
    apply hi
    change E.val (aeval (R := K) id q) = E.val 0
    rw [← eval_rename, hq, hp, map_zero]
  -- The partial derivatives evaluated in E vanish because they vanish in L.
  have hqdiff : Q.toExtension.cotangentComplex (Extension.Cotangent.mk ⟨q, hqker⟩) = 0 := by
    apply Q.cotangentSpaceBasis.repr.injective
    apply Finsupp.ext
    intro j
    rw [map_zero, Finsupp.zero_apply]
    have hj := congrArg (fun y ↦ P.cotangentSpaceBasis.repr y (i j)) hx
    have hj' : aeval (R := K) id (pderiv (i j) p.val) = 0 := by
      calc
        _ = P.cotangentSpaceBasis.repr (P.toExtension.cotangentComplex
            (Extension.Cotangent.mk p)) (i j) := (self_cotangent_coord p (i j)).symm
        _ = 0 := by simpa only [map_zero, Finsupp.zero_apply] using hj
    rw [← hq, pderiv_rename hi, eval_rename] at hj'
    exact (self_cotangent_coord ⟨q, hqker⟩ j).trans
      (hi (hj'.trans (map_zero E.val).symm))
  have hq₂ : q ∈ Q.ker ^ 2 :=
    mem_ker_sq_of_cotangent_zero (K := K) (L := E) ⟨q, hqker⟩ hqdiff
  have hker : Q.ker.map (rename (R := K) i).toRingHom ≤ P.ker := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change rename i r ∈ P.ker
    apply (self_mem_ker_iff (rename i r)).mpr
    rw [eval_rename, (self_mem_ker_iff r).mp hr, map_zero]
  apply (Extension.Cotangent.mk_eq_zero_iff p).mpr
  have hm := Ideal.mem_map_of_mem (rename (R := K) i).toRingHom hq₂
  rw [Ideal.map_pow] at hm
  rw [← hq]
  exact Ideal.pow_right_mono hker 2 hm

/-- Every field is formally smooth over its prime subfield. -/
theorem primeSubfieldFormallySmooth (L : Type*) [Field L] :
    Algebra.FormallySmooth (↥(⊥ : Subfield L)) L := by
  have : PerfectField (↥(⊥ : Subfield L)) := by
    rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | hzero
    · let : Fact (ringChar L).Prime := ⟨hp⟩
      let : Algebra (ZMod (ringChar L)) L := ZMod.algebra L _
      exact PerfectField.of_ringEquiv (Subfield.botEquivZMod L (ringChar L)).symm
    · have : CharZero L := (CharP.ringChar_zero_iff_CharZero (R := L)).mp hzero
      exact PerfectField.of_ringEquiv (Subfield.botEquivRat L).symm
  exact fieldFormallySmoothOfPerfect _ L

/-- A map from a field to a square-zero quotient lifts over the prime subfield. -/
theorem primeSubfieldSquareZeroLift (L : Type*) [Field L] (T : Type*) [CommRing T]
    [Algebra (↥(⊥ : Subfield L)) T] (N : Ideal T) (hN : N ^ 2 = ⊥)
    (f : L →ₐ[↥(⊥ : Subfield L)] T ⧸ N) :
    ∃ g : L →ₐ[↥(⊥ : Subfield L)] T, (Ideal.Quotient.mkₐ (↥(⊥ : Subfield L)) N).comp g = f := by
  have := primeSubfieldFormallySmooth L
  exact Algebra.FormallySmooth.comp_surjective _ L N hN f

end CommutativeAlgebraNotes.CoefficientRings
