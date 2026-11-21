import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Localization

/-! FL-10: localization and the square-zero lifting properties.
We transport the general localization theorem through FL-01. Target
localization is composition with an étale map. For source localization,
the unit hypothesis supplies the localized-base algebra structure; the
localization is étale, so restriction of scalars preserves and reflects
each property. No nontriviality or finiteness assumptions are used.
-/
namespace AdvCommAlg.FormalLifting

universe u v w

open Specs.AdvCommAlg.FormalLifting.Localization

/-- Localizations are formally étale even when zero is inverted. -/
theorem localization_etale : localizationEtale.{u,v} := by
  intro B L _ _ _ S _
  apply (formallyEtale_iff B L).mpr
  exact Algebra.FormallyEtale.of_isLocalization S

/-- Localizing the target preserves formal smoothness. -/
theorem smooth_target_localization : smoothTargetLocalization.{u,v,w} := by
  intro A B L _ _ _ _ _ _ _ S _ h
  let : Algebra.FormallySmooth A B := (formallySmooth_iff A B).mp h
  let : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isLocalization S
  apply (formallySmooth_iff A L).mpr
  exact Algebra.FormallySmooth.comp A B L

/-- Localizing the target preserves formal unramifiedness. -/
theorem unramified_target_localization : unramifiedTargetLocalization.{u,v,w} := by
  intro A B L _ _ _ _ _ _ _ S _ h
  let : Algebra.FormallyUnramified A B := (formallyUnramified_iff A B).mp h
  let : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isLocalization S
  apply (formallyUnramified_iff A L).mpr
  exact Algebra.FormallyUnramified.comp A B L

/-- Localizing the target preserves formal étaleness. -/
theorem etale_target_localization : etaleTargetLocalization.{u,v,w} := by
  intro A B L _ _ _ _ _ _ _ S _ h
  let : Algebra.FormallyEtale A B := (formallyEtale_iff A B).mp h
  let : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isLocalization S
  apply (formallyEtale_iff A L).mpr
  exact Algebra.FormallyEtale.comp A B L

/-- Localizing the base at elements already mapping to units preserves and
reflects formal smoothness, with its induced localized-base action. -/
theorem smooth_source_localization_iff : smoothSourceLocalizationIff.{u,v,w} := by
  intro A B L _ _ _ _ _ U _ hU
  let : Algebra L B := (IsLocalization.lift (S := L) hU).toAlgebra
  let : IsScalarTower A L B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hU).symm
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization U
  constructor
  · intro h
    let : Algebra.FormallySmooth A B := (formallySmooth_iff A B).mp h
    apply (formallySmooth_iff L B).mpr
    exact Algebra.FormallySmooth.of_restrictScalars A L B
  · intro h
    let : Algebra.FormallySmooth L B := (formallySmooth_iff L B).mp h
    apply (formallySmooth_iff A B).mpr
    exact Algebra.FormallySmooth.comp A L B

/-- Localizing the base at elements already mapping to units preserves and
reflects formal unramifiedness, with its induced localized-base action. -/
theorem unramified_source_localization_iff : unramifiedSourceLocalizationIff.{u,v,w} := by
  intro A B L _ _ _ _ _ U _ hU
  let : Algebra L B := (IsLocalization.lift (S := L) hU).toAlgebra
  let : IsScalarTower A L B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hU).symm
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization U
  constructor
  · intro h
    let : Algebra.FormallyUnramified A B := (formallyUnramified_iff A B).mp h
    apply (formallyUnramified_iff L B).mpr
    exact Algebra.FormallyUnramified.of_restrictScalars A L B
  · intro h
    let : Algebra.FormallyUnramified L B := (formallyUnramified_iff L B).mp h
    apply (formallyUnramified_iff A B).mpr
    exact Algebra.FormallyUnramified.comp A L B

/-- Localizing the base at elements already mapping to units preserves and
reflects formal étaleness, with its induced localized-base action. -/
theorem etale_source_localization_iff : etaleSourceLocalizationIff.{u,v,w} := by
  intro A B L _ _ _ _ _ U _ hU
  let : Algebra L B := (IsLocalization.lift (S := L) hU).toAlgebra
  let : IsScalarTower A L B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hU).symm
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization U
  constructor
  · intro h
    let : Algebra.FormallyEtale A B := (formallyEtale_iff A B).mp h
    apply (formallyEtale_iff L B).mpr
    exact Algebra.FormallyEtale.of_restrictScalars (R := A)
  · intro h
    let : Algebra.FormallyEtale L B := (formallyEtale_iff L B).mp h
    apply (formallyEtale_iff A B).mpr
    exact Algebra.FormallyEtale.comp A L B

end AdvCommAlg.FormalLifting
