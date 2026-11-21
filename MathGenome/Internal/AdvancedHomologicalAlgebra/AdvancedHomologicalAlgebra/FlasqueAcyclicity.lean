import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FlasqueAcyclicity
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

noncomputable section
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u w w'
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.FlasqueAcyclicity

namespace AdvancedHomologicalAlgebra.FlasqueAcyclicity

theorem sectionsSurjective : sectionsSurjectiveType.{u} := by
  intro X R S hS hF U
  let T := S.map (SheafOfModules.toSheaf R)
  have hT : T.ShortExact := hS.map_of_exact (SheafOfModules.toSheaf R)
  letI : TopCat.Sheaf.IsFlasque T.X₁ :=
    (SheafInjectivesAndRestriction.flasque_iff R S.X₁).mpr hF
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hT)

theorem quotientFlasque : quotientFlasqueType.{u} := by
  intro X R S hS hF hG
  let T := S.map (SheafOfModules.toSheaf R)
  have hT : T.ShortExact := hS.map_of_exact (SheafOfModules.toSheaf R)
  letI : TopCat.Sheaf.IsFlasque T.X₁ :=
    (SheafInjectivesAndRestriction.flasque_iff R S.X₁).mpr hF
  letI : TopCat.Sheaf.IsFlasque T.X₂ :=
    (SheafInjectivesAndRestriction.flasque_iff R S.X₂).mpr hG
  exact (SheafInjectivesAndRestriction.flasque_iff R S.X₃).mp
    (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hT)

/-- The cokernel in an injective presentation stays flasque. Repeating this
construction gives the successive flasque cokernels of an injective resolution. -/
lemma injectiveCokernelFlasque {X : TopCat.{u}} (R : RingSheaf X)
    [EnoughInjectives (Modules R)] (M : Modules R) (hM : IsFlasque R M) :
    IsFlasque R (cokernel (Injective.ι M)) := by
  exact quotientFlasque R (UniversalDeltaFunctors.injectiveSequence M)
    (UniversalDeltaFunctors.injectiveSequence_shortExact M) hM
    (SheafInjectivesAndRestriction.Expected.injectives_flasque R _ inferInstance)

/-- Dimension shifting along the successive injective presentations. In degree
one the boundary vanishes because sections of the injective surject onto the
cokernel; at each later degree its source vanishes by induction. -/
theorem flasqueAcyclic : flasqueAcyclicType.{u, w, w'} := by
  intro X R _ _ U _ M hM n
  let F := SheafOfModules.evaluation R (op U)
  let T := rightSystem F
  have hT : IsCohomological T :=
    UniversalDeltaFunctors.rightDelta (Modules R) (ModuleCat (sectionRing R U)) F
  have vanish (I : Modules R) [Injective I] (k : ℕ) :
      IsZero ((T.value (k + 1)).obj I) :=
    ClassicalDerivedValues.rightInjectiveVanishing _ _ F I k
  suffices h : ∀ (N : Modules R), IsFlasque R N →
      IsZero ((T.value (n + 1)).obj N) from h M hM
  induction n with
  | zero =>
    intro N hN
    let S := UniversalDeltaFunctors.injectiveSequence N
    have hS : S.ShortExact := UniversalDeltaFunctors.injectiveSequence_shortExact N
    letI : Epi (T.δ hS 0) :=
      UniversalDeltaFunctors.dimensionShift_epi T hT vanish N 0
    letI : Epi (F.map S.g) :=
      (ModuleCat.epi_iff_surjective _).mpr (sectionsSurjective R S hS hN U)
    letI := ClassicalDerivedValues.rightZero (Modules R)
      (ModuleCat (sectionRing R U)) F
    letI : Epi ((T.value 0).map S.g) := by
      change Epi ((rightValue F 0).map S.g)
      exact epi_of_epi_fac ((rightDegreeZeroUnit F).naturality S.g).symm
    exact IsZero.of_epi_eq_zero (T.δ hS 0)
      (zero_of_epi_comp ((T.value 0).map S.g) (hT.exact₃ hS 0).zero)
  | succ n ih =>
    intro N hN
    let S := UniversalDeltaFunctors.injectiveSequence N
    have hS : S.ShortExact := UniversalDeltaFunctors.injectiveSequence_shortExact N
    letI : Epi (T.δ hS (n + 1)) :=
      UniversalDeltaFunctors.dimensionShift_epi T hT vanish N (n + 1)
    exact IsZero.of_epi (T.δ hS (n + 1))
      (ih (cokernel (Injective.ι N)) (injectiveCokernelFlasque R N hN))

end AdvancedHomologicalAlgebra.FlasqueAcyclicity
