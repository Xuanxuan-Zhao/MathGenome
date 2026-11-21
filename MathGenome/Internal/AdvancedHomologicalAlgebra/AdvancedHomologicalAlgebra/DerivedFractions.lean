import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedFractions
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicThickSubcategory

/-!
HA-D02. The cone class of the acyclic triangulated subcategory has both fraction
calculi. HA-D01 identifies that class with the ordinary quasi-isomorphisms.
The library fraction localization proves the roof representation and equality
criterion for every localization model. Two-out-of-three upgrades the maps in
a common refinement to quasi-isomorphisms. The canonical path localization
supplies an actual category and the unique factorization of every inverting
functor, so no equivalence or composition law is left as an assumption.
-/

set_option linter.checkUnivs false
universe v u
open CategoryTheory
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.DerivedFractions

namespace AdvancedHomologicalAlgebra.DerivedFractions

instance rightCalculus (A : Type u) [Category.{v} A] [Abelian A] :
    (W A).HasRightCalculusOfFractions := by
  change (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).HasRightCalculusOfFractions
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

instance leftCalculus (A : Type u) [Category.{v} A] [Abelian A] :
    (W A).HasLeftCalculusOfFractions := by
  change (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).HasLeftCalculusOfFractions
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

theorem localization :
    Specs.AdvancedHomologicalAlgebra.DerivedFractions.localizationType := by
  intro A _ _
  infer_instance

theorem universal : Specs.AdvancedHomologicalAlgebra.DerivedFractions.universalType := by
  intro A _ _ E _ F hF
  refine ⟨Localization.Construction.lift F hF, Localization.Construction.fac F hF, ?_⟩
  intro G hG
  exact Localization.Construction.uniq G _ (hG.trans (Localization.Construction.fac F hF).symm)

theorem rightRoof : Specs.AdvancedHomologicalAlgebra.DerivedFractions.rightRoofType := by
  intro A _ _ E _ J _ X Y f
  exact Localization.exists_rightFraction J (W A) f

theorem leftRoof : Specs.AdvancedHomologicalAlgebra.DerivedFractions.leftRoofType := by
  intro A _ _ E _ J _ X Y f
  exact Localization.exists_leftFraction J (W A) f

theorem rightRoof_eq_iff :
    Specs.AdvancedHomologicalAlgebra.DerivedFractions.rightRoof_eq_iffType := by
  intro A _ _ E _ J _ X Y r q
  let := AcyclicThickSubcategory.two_out_of_three A
  rw [MorphismProperty.RightFraction.map_eq_iff J (W A)]
  constructor
  · rintro ⟨T, a, b, hs, hf, h⟩
    exact ⟨T, a, b, (W A).of_postcomp a r.s r.hs h,
      (W A).of_postcomp b q.s q.hs (hs ▸ h), hs, hf⟩
  · rintro ⟨T, a, b, ha, _, hs, hf⟩
    exact ⟨T, a, b, hs, hf, (W A).comp_mem a r.s ha r.hs⟩

theorem leftRoof_eq_iff :
    Specs.AdvancedHomologicalAlgebra.DerivedFractions.leftRoof_eq_iffType := by
  intro A _ _ E _ J _ X Y r q
  let := AcyclicThickSubcategory.two_out_of_three A
  rw [MorphismProperty.LeftFraction.map_eq_iff J (W A)]
  constructor
  · rintro ⟨T, a, b, hs, hf, h⟩
    exact ⟨T, a, b, (W A).of_precomp r.s a r.hs h,
      (W A).of_precomp q.s b q.hs (hs ▸ h), hs, hf⟩
  · rintro ⟨T, a, b, ha, _, hs, hf⟩
    exact ⟨T, a, b, hs, hf, (W A).comp_mem r.s a r.hs ha⟩

end AdvancedHomologicalAlgebra.DerivedFractions
