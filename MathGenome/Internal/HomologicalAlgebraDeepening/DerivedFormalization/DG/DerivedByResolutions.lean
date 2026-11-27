import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedByResolutions
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.DerivedByResolutions
open Specs.DerivedFormalization.DG.DerivedCoproducts
open Specs.DerivedFormalization.DG.DerivedTriangles
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)
open Specs.DerivedFormalization.DG.IndexedSemiFree (StrictSum)

open private transitionMaps_of_inclusions from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts

noncomputable section

universe u v w j t s

private theorem ambientResolutions : AmbientResolutions.{u,v,w,t} := by
  intro k _ A M
  let B := AmbientDerived.category.{u,v,w,t} A
  obtain ⟨P, p, hP, hs, hp⟩ := unboundedSemiFreeResolutionInUniverse.{u,max v t,w} k B M
  exact ⟨P, p, hP, IsSemiFree.isKProjective hP, hs, hp⟩

private theorem ambientHomGroups : AmbientHomGroups.{u,v,w,t} := by
  intro k _ A h
  dsimp only
  intro AD
  obtain ⟨AD₀, hAdd⟩ := ambientDerivedHomComparison_additive.{u,v,w,t} A h
  have hAD : AD = AD₀ := by
    -- The triangulation supplies binary biproducts, which determine the group laws.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, SD, AD₁, ZD, LD, _, TD, _⟩ :=
      ambientDerivedTriangulation.{u,v,w,t} A h
    let _ := derivedCategoryInstance (AmbientDerived.category.{u,v,w,t} A) h
    let _ := SD
    let _ := AD₁
    let _ := ZD
    let _ := LD
    let _ := TD
    exact Subsingleton.elim AD AD₀
  subst AD
  intro P M N p hp hP
  exact hAdd (N := N) p hp hP

private theorem coproductsAtAdequateIndex : CoproductsAtAdequateIndex.{u,v,w,j} := by
  intro k _ A h I X
  let _ := Derived.homotopyCategory A h
  let _ := derivedCategoryInstance A h
  let e := Localization.Construction.objEquiv (Derived.quasiIsomorphisms A)
  let F := fun i => e.symm (X i)
  have hF : IndexedSums.TermsSmall F := fun _ _ => small_self _
  obtain ⟨S, ⟨b⟩⟩ := DG.IndexedSums.realization.{u,max v w j,w,j} F hF
  obtain ⟨hres, ⟨hb⟩⟩ := nativeDerivedCoproduct.{u,v,w,j} h b
  refine ⟨S, b, hres, ⟨hb⟩, ?_⟩
  have he : (fun i => (Derived.quotient A h).obj (F i)) = X :=
    funext fun i => e.apply_symm_apply (X i)
  rw [← he]
  exact HasColimit.mk ⟨derivedCofan h b, hb⟩

private theorem coproductTransitionCompatibility :
    CoproductTransitionCompatibility.{u,v,w,j,t,s} := by
  intro k _ A h h'
  obtain ⟨d, hff, hlin, hrep⟩ := DG.DerivedCoefficientLift.derivedCoefficientTransition.{u,v,w,t,s} A h h'
  refine ⟨d, hff, hlin, hrep, ?_⟩
  intro I F S b
  obtain ⟨_, c, _, hi, hc, hlower, hupper, _⟩ := ambientCoproductTransition.{u,v,w,j,t,s} A h h' b
  exact ⟨c, hi, hc, hlower, hupper, transitionMaps_of_inclusions d b c hi⟩

set_option maxHeartbeats 800000 in
/-- Compute the derived category through K-projective resolutions, with the
signed cone triangulation and coproducts given by the strict pointwise sums. -/
theorem derivedByResolutions : ComputingDerivedByResolutions.{u,v,w,j,t,s} :=
  ⟨DG.AmbientDerived.isLocalization.{u,v,w,t},
    ambientResolutions.{u,v,w,t},
    ambientKProjectiveLocalization_isEquivalence.{u,v,w,t},
    ambientDerivedHomComparison.{u,v,w,t},
    ambientHomGroups.{u,v,w,t},
    ambientKProjectiveReplacementComparison.{u,v,w,t},
    ambientDerivedHomComparison_sourceNaturality.{u,v,w,t},
    ambientDerivedTriangulation.{u,v,w,t},
    liftedConeTriangleComparison.{u,v,w,t},
    DG.AmbientDerived.inputCoefficients.{u,v,w,t},
    DG.AmbientDerived.inputLocalization.{u,v,w,t},
    originalInputDerivedHomComparison.{u,v,w,t},
    DG.AmbientDerived.nativeStrictComparison.{u,v,w,t},
    DG.AmbientDerived.nativeLocalizationComparison.{u,v,w,t},
    adequateNativeDerivedHomComparison.{u,v,w,t},
    nativeDerivedTriangulation.{u,v,w},
    coproductsAtAdequateIndex.{u,v,w,j},
    originalDerivedCoproduct.{u,v,w,j,t},
    originalExistingDerivedCoproduct.{u,v,w,j,t},
    nativeExistingDerivedCoproduct.{u,v,w,j},
    g02SumComparison.{u,v,w},
    coproductTransitionCompatibility.{u,v,w,j,t,s},
    DG.DerivedCoefficientLift.derivedCoefficientTransitionOnInputs.{u,v,w,t,s},
    DG.DerivedCoefficientLift.kProjectiveCoefficientTransition.{u,v,w,t,s}⟩

end

end DerivedFormalization.RightDGModule
