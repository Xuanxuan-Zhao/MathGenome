import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions

/-! Krull dimension conventions (paper.tex:1037).
The localization equality is proved by the order correspondence between primes
of Rₚ and primes of R contained in p. The support comparison uses the quotient
prime correspondence and the finite-generation support formula, which requires
no Noetherian hypothesis. -/
namespace P103.Ch06.DimensionConventions

universe u v
open P103.Specs.Ch05.AssociatedPrimesInterface
open P103.Specs.Ch06.DimensionConventions

noncomputable def ringDimension : RingDimensionType.{u} := ringDimensionValue
noncomputable def primeHeight : PrimeHeightType.{u} := primeHeightValue
noncomputable def moduleDimension : ModuleDimensionType.{u,v} := moduleDimensionValue
noncomputable def supportDimension : ModuleDimensionType.{u,v} := supportDimensionValue

theorem ringDimension_chains : ringDimension_chainsType.{u} := by
  intro R _
  rfl

theorem ringDimension_empty : ringDimension_emptyType.{u} := by
  intro R _ _
  exact Order.krullDim_eq_bot

theorem ringDimension_zeroRing : ringDimension_zeroRingType.{u} := by
  intro R _ _
  exact ringKrullDim_eq_bot_of_subsingleton

theorem primeHeight_chains : primeHeight_chainsType.{u} := by
  intro R _ p
  change p.asIdeal.height = _
  rw [p.height_eq_orderHeight]
  exact Order.height_eq_iSup_last_eq p

theorem primeHeight_localization : primeHeight_localizationType.{u} := by
  intro R _ p
  change (p.asIdeal.height : WithBot ℕ∞) =
    Order.krullDim (PrimeSpectrum (Localization.AtPrime p.asIdeal))
  rw [p.height_eq_orderHeight, Order.height_eq_krullDim_Iic]
  exact (Order.krullDim_eq_of_orderIso
    (IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.asIdeal) p.asIdeal)).symm

theorem finite_support_eq_zeroLocus : finite_support_eq_zeroLocusType.{u,v} := by
  intro R _ M _ _ _
  exact Module.support_eq_zeroLocus

theorem moduleDimension_eq_supportDimension :
    moduleDimension_eq_supportDimensionType.{u,v} := by
  intro R _ M _ _ _
  change Order.krullDim (PrimeSpectrum (R ⧸ Module.annihilator R M)) =
    Order.krullDim (supportValue R M)
  rw [finite_support_eq_zeroLocus R M]
  exact Order.krullDim_eq_of_orderIso
    (Module.annihilator R M).primeSpectrumQuotientOrderIsoZeroLocus

theorem moduleDimension_zero : moduleDimension_zeroType.{u,v} := by
  intro R _ M _ _ _
  change ringKrullDim (R ⧸ Module.annihilator R M) = ⊥
  rw [Module.annihilator_eq_top_iff.mpr (inferInstance : Subsingleton M)]
  exact ringKrullDim_eq_bot_of_subsingleton

end P103.Ch06.DimensionConventions
