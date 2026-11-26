import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FieldFormalSmoothness
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Smooth.AdicCompletion

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing

private theorem lift_residueField (K R : Type*) [Field K] [PerfectField K]
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra K R] :
    ∃ σ : ResidueField R →+* R, (residue R).comp σ = RingHom.id (ResidueField R) := by
  have := fieldFormallySmoothOfPerfect K (ResidueField R)
  obtain ⟨σ, hσ⟩ :=
    Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
      (I := maximalIdeal R) (AlgHom.id K (ResidueField R))
  exact ⟨σ.toRingHom, congrArg AlgHom.toRingHom hσ⟩

/-- The residue map of an equal-characteristic complete Noetherian local ring
admits an injective ring-homomorphic section. -/
theorem exists_coefficientField (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (hchar : ringChar (ResidueField R) = ringChar R) :
    ∃ σ : ResidueField R →+* R,
      (residue R).comp σ = RingHom.id (ResidueField R) ∧ Function.Injective σ := by
  suffices ∃ σ : ResidueField R →+* R, (residue R).comp σ = RingHom.id (ResidueField R) by
    obtain ⟨σ, hσ⟩ := this
    have hleft : Function.LeftInverse (residue R) σ := fun x ↦ RingHom.congr_fun hσ x
    exact ⟨σ, hσ, hleft.injective⟩
  rcases CharP.char_is_prime_or_zero (ResidueField R) (ringChar (ResidueField R)) with hp | hzero
  · have : Fact (ringChar (ResidueField R)).Prime := ⟨hp⟩
    have : CharP R (ringChar (ResidueField R)) := hchar.symm ▸ ringChar.charP R
    let := ZMod.algebra R (ringChar (ResidueField R))
    exact lift_residueField (ZMod (ringChar (ResidueField R))) R
  · have : CharZero (ResidueField R) :=
      (CharP.ringChar_zero_iff_CharZero (R := ResidueField R)).mp hzero
    have hunit (n : nonZeroDivisors ℤ) : IsUnit (Int.castRingHom R n) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      change residue R (n.val : R) ≠ 0
      rw [map_intCast]
      exact Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp n.prop)
    let : Algebra ℚ R := (IsLocalization.lift (S := ℚ) hunit).toAlgebra
    exact lift_residueField ℚ R

end CommutativeAlgebraNotes.CoefficientRings
