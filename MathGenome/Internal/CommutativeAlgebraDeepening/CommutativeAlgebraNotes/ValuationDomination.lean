import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ValuationDomination
import Mathlib.RingTheory.Valuation.LocalSubring

namespace CommutativeAlgebraNotes.ValuationDomination

theorem exists_dominating_valuation_subring : Specs.exists_dominating_valuation_subring := by
  intro L _ A
  obtain ⟨V, h, hLocal⟩ := A.exists_le_valuationSubring
  let : IsLocalHom (Subring.inclusion h) := hLocal
  exact ⟨V, inferInstance, h, IsLocalRing.maximalIdeal_comap (Subring.inclusion h)⟩

theorem comap_eq_of_domination : Specs.comap_eq_of_domination := by
  intro K L _ _ f A V h hMax
  refine le_antisymm ?_ (fun x hx => h ⟨x, hx⟩)
  intro x hxV
  by_contra hxA
  have hInv : x⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hxA)
  obtain ⟨hInvA, hInvMax⟩ := A.mem_nonunits_iff_exists_mem_maximalIdeal.mp hInv
  have hInvMaxV : (⟨x⁻¹, hInvA⟩ : A) ∈
      (IsLocalRing.maximalIdeal V).comap ((f.comp A.subtype).codRestrict V.toSubring h) :=
    hMax.symm ▸ hInvMax
  have hInvV : f x⁻¹ ∈ V.nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr (Ideal.mem_comap.mp hInvMaxV)
  rw [map_inv₀] at hInvV
  rcases V.inv_mem_nonunits_iff.mp hInvV with hZero | hOutside
  · exact hxA ((f.injective (hZero.trans f.map_zero.symm)) ▸ A.zero_mem)
  · exact hOutside hxV

end CommutativeAlgebraNotes.ValuationDomination
