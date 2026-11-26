import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PurelyInseparableValuationExtension
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ValuationDomination

namespace CommutativeAlgebraNotes.PurelyInseparableValuationExtension

open Specs.CommutativeAlgebraNotes.PurelyInseparableValuationExtension

/-- The power test for membership in an extension of valuation subrings. -/
theorem mem_iff_pow_mem : MemIffPowMem := by
  intro K L _ _ _ V W hW p _ n x y hy
  have hmem : y ∈ V ↔ algebraMap K L y ∈ W := by
    rw [← ValuationSubring.mem_comap, hW]
  rw [hmem, hy, ← W.valuation_le_one_iff x,
    ← W.valuation_le_one_iff (x ^ (p ^ n)), map_pow]
  exact (pow_le_one_iff_of_nonneg zero_le (expChar_pow_pos K p n).ne').symm

/-- Every valuation subring extending the base valuation is its integral closure. -/
theorem extension_eq_integralClosure : ExtensionEqIntegralClosure := by
  intro K L _ _ _ _ V W hW
  have : IsIntegrallyClosedIn W.toSubring L :=
    inferInstanceAs (IsIntegrallyClosedIn W L)
  apply le_antisymm
  · intro x hx
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) x
    have hyV : y ∈ V := (mem_iff_pow_mem V W hW (ringExpChar K) n x y hy).mp hx
    let a : V := ⟨y, hyV⟩
    change IsIntegral V x
    refine ⟨Polynomial.X ^ (ringExpChar K ^ n) - Polynomial.C a,
      Polynomial.monic_X_pow_sub_C a (expChar_pow_pos K (ringExpChar K) n).ne', ?_⟩
    have ha : algebraMap V L a = x ^ (ringExpChar K ^ n) := hy
    simp [ha]
  · apply Subring.integralClosure_le_iff.mpr
    intro a
    change (a : K) ∈ W.comap (algebraMap K L)
    rw [hW]
    exact a.property

/-- The purely inseparable assertion of Theorem 5.22. -/
theorem existsUnique_extension : ExistsUniqueExtension := by
  intro K L _ _ _ _ V
  obtain ⟨W, h, hLocal⟩ :=
    IsLocalRing.exists_factor_valuationRing ((algebraMap K L).comp V.subtype)
  have hW : W.comap (algebraMap K L) = V :=
    ValuationDomination.comap_eq_of_domination K L (algebraMap K L) V W h
      (IsLocalRing.maximalIdeal_comap _)
  refine ⟨W, hW, fun W' hW' => ValuationSubring.toSubring_injective ?_⟩
  exact (extension_eq_integralClosure V W' hW').trans (extension_eq_integralClosure V W hW).symm

end CommutativeAlgebraNotes.PurelyInseparableValuationExtension
