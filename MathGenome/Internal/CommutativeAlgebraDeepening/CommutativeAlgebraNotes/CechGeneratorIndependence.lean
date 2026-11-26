import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsionProperties
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechGeneratorIndependence

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped ZeroObject

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.CechGeneratorIndependence

universe u v w

/-- The natural identification of torsion functors for equal radicals derives
to a natural identification on bounded-below complexes. -/
theorem derivedIdealTorsionIsoOfRadicalEq : DerivedRadicalInvariance.{u, w} := by
  intro R _ _ _ I J h
  obtain ⟨e, _⟩ := idealTorsionFunctor_inclusion_iso_of_radical_eq.{u, u} h
  refine ⟨⟨e.hom.rightDerivedFunctorPlus, e.inv.rightDerivedFunctorPlus, ?_, ?_⟩⟩
  · rw [← NatTrans.rightDerivedFunctorPlus_comp, e.hom_inv_id, NatTrans.rightDerivedFunctorPlus_id]
  · rw [← NatTrans.rightDerivedFunctorPlus_comp, e.inv_hom_id, NatTrans.rightDerivedFunctorPlus_id]

/-- Both Čech tensor functors descend to the same functor identified with derived torsion. -/
theorem derivedCechIndependence : DerivedCechIndependence.{u, w} := by
  intro R _ _ _ I rs ts hrs hts
  obtain ⟨e₁⟩ := derivedIdealTorsionIsoOfRadicalEq hrs
  obtain ⟨e₂⟩ := derivedIdealTorsionIsoOfRadicalEq hts
  obtain ⟨T, ⟨hT⟩, ⟨eT⟩⟩ := derivedCechComparison _ rs rfl
  obtain ⟨U, ⟨hU⟩, ⟨eU⟩⟩ := derivedCechComparison _ ts rfl
  let e : T ≅ U := eT.symm ≪≫ e₁.symm ≪≫ e₂ ≪≫ eU
  exact ⟨T, ⟨e₁ ≪≫ eT⟩, ⟨hT⟩,
    ⟨Functor.isoWhiskerRight (Functor.isoWhiskerLeft DerivedCategory.Plus.Q e)
      DerivedCategory.Plus.ι ≪≫ hU⟩⟩

/-- Local cohomology depends naturally on the radical of the support ideal. -/
theorem localCohomologyIsoOfRadicalEq : RadicalInvariance.{u, v} := by
  intro R _ _ _ I J h q
  cases q with
  | negSucc _ => exact ⟨Iso.refl _⟩
  | ofNat n =>
    obtain ⟨e, _⟩ := idealTorsionFunctor_inclusion_iso_of_radical_eq.{v, u} h
    change Nonempty ((idealTorsionFunctor I).rightDerived n ≅ (idealTorsionFunctor J).rightDerived n)
    refine ⟨⟨e.hom.rightDerived n, e.inv.rightDerived n, ?_, ?_⟩⟩
    · rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
    · rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

theorem localCohomologyCechComparisonOfRadicalEq : CechComparisonOfRadicalEq.{u} := by
  intro R _ _ I rs h q
  obtain ⟨e⟩ := localCohomologyIsoOfRadicalEq h q
  obtain ⟨c⟩ := localCohomologyCechComparison _ rs rfl q
  exact ⟨e ≪≫ c⟩

theorem cechCohomologyIsoOfRadicalEq : CechIndependence.{u} := by
  intro R _ _ rs ts h q
  obtain ⟨e⟩ := localCohomologyCechComparison _ rs rfl q
  obtain ⟨c⟩ := localCohomologyCechComparisonOfRadicalEq _ ts h q
  exact ⟨e.symm ≪≫ c⟩

theorem localCohomologyIsZeroOfLengthLt : VanishingAboveLength.{u} := by
  intro R _ _ I rs h q hq
  obtain ⟨e⟩ := localCohomologyCechComparisonOfRadicalEq I rs h q
  refine IsZero.of_iso (Functor.isZero (cechCohomology rs q) fun M => ?_) e
  change IsZero ((cechCoefficients rs M).homology q)
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change IsZero ((cechCoefficients rs M).X q)
  exact IsZero.of_iso
    (Functor.map_isZero ((curriedTensor (ModuleCat R)).flip.obj M)
      (Cech.isZero_X rs q (Or.inr hq)))
    (Cech.tensorSingleTerm (CechComplex rs) M q).symm

theorem localCohomologyBotIso : BotDegreeZero.{u, v} := by
  intro R _ _ _
  let := idealTorsionInclusion_bot_isIso.{v, u} (R := R)
  exact ⟨(idealTorsionFunctor (⊥ : Ideal R)).rightDerivedZeroIsoSelf ≪≫
    asIso (idealTorsionInclusion (⊥ : Ideal R))⟩

theorem localCohomologyBotIsZero : BotVanishing.{u} := by
  intro R _ _ q hq
  change IsZero (localCohomology (⊥ : Ideal R) q)
  rcases lt_or_gt_of_ne hq with hn | hp
  · rw [localCohomology_of_neg _ _ hn]
    exact isZero_zero _
  · exact localCohomologyIsZeroOfLengthLt (⊥ : Ideal R) []
      (by simp) q (by simpa using hp)

theorem localCohomologyTopIsZero : TopVanishing.{u, v} := by
  intro R _ _ _ q
  cases q with
  | negSucc _ => exact isZero_zero _
  | ofNat n =>
    let F := idealTorsionFunctor.{v} (⊤ : Ideal R)
    change IsZero (F.rightDerived n)
    refine Functor.isZero _ fun M => ?_
    let P := injectiveResolution M
    refine IsZero.of_iso ?_ (P.isoRightDerivedObj F n)
    apply ShortComplex.isZero_homology_of_isZero_X₂
    change IsZero (F.obj (P.cocomplex.X n))
    exact (idealTorsionFunctor_top_isZero (R := R)).obj _

end CommutativeAlgebraNotes
