import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.RegularAndCohenMacaulayNormality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.SerreCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import Batteries.Tactic.OpenPrivate

/-! SN-10: normality of regular rings and the codimension-one criterion
for Cohen–Macaulay rings. All conditions are tested at the primes of the
ambient Noetherian ring, so the statements also include the zero ring. -/
universe u
namespace AdvCommAlg.Normality

open private ringSerreCondition_iff_local_depth from MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.SerreCriterion

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

private theorem ringSerreCondition_of_cohenMacaulay
    (hCM : CohenMacaulay.CohenMacaulayRing A) (k : ℕ) :
    CohenMacaulay.RingSerreCondition A k := by
  apply (ringSerreCondition_iff_local_depth A k).mpr
  intro p
  have he := (CohenMacaulay.cohenMacaulayAt_iff_depth_eq A p).mp (hCM p)
  exact (min_le_right _ _).trans he.symm.le

/-- For a Cohen–Macaulay Noetherian ring, normality is equivalent to
regularity at every prime of height at most one. -/
theorem cohenMacaulay_isNormal_iff_regularInCodimension_one
    (hCM : CohenMacaulay.CohenMacaulayRing A) :
    IsNormal A ↔ RegularInCodimension A 1 := by
  constructor
  · intro h
    exact ((serreCriterion A).mp h).1
  · intro h
    exact (serreCriterion A).mpr ⟨h, ringSerreCondition_of_cohenMacaulay A hCM 2⟩

/-- A Noetherian ring whose localization at every prime is regular local
is normal. -/
theorem isNormal_of_regular_at_every_prime
    (hreg : ∀ p : PrimeSpectrum A,
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)) : IsNormal A := by
  have hCM : CohenMacaulay.CohenMacaulayRing A := by
    intro p
    let := hreg p
    exact CohenMacaulay.regularLocal_cohenMacaulay (Localization.AtPrime p.asIdeal)
  apply (cohenMacaulay_isNormal_iff_regularInCodimension_one A hCM).mpr
  intro p _
  exact hreg p

end AdvCommAlg.Normality
