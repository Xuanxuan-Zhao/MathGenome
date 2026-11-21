import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedCategory

/-!
HA-D04. The cone comparison q is a quasi-isomorphism without splitting
assumptions. Transporting the cone row gives the derived triangle and its
naturality. To identify boundaries, first cancel the homotopy-category
cohomology comparisons in the library's cone calculation, then cancel H(Qq)
in the derived category. The last calculation is the ordinary snake-lemma
lift-and-differential formula, valid for test objects in every abelian category.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex
open Specs.AdvancedHomologicalAlgebra.MappingCones
open Specs.AdvancedHomologicalAlgebra.DerivedCategory
open Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle

namespace AdvancedHomologicalAlgebra.ShortExactDerivedTriangle

noncomputable def coneToThird :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.coneToThirdType :=
  fun _ _ _ S => mappingCone.descShortComplex S

theorem coneToThird_coordinates :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.coneToThird_coordinatesType := by
  intro A _ _ S n
  ext <;> simp [degreeBiproductIso, Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.coneToThird,
    targetInclusion, shiftInclusion]

theorem coneToThird_quasiIso :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.coneToThird_quasiIsoType := by
  intro A _ _ S hS
  exact mappingCone.quasiIso_descShortComplex hS

noncomputable def connecting :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.connectingType :=
  fun _ _ _ _ _ hS => _root_.DerivedCategory.triangleOfSESδ hS

theorem connecting_formula :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.connecting_formulaType := by
  intro A _ _ _ S hS
  simp only [Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.connecting,
    _root_.DerivedCategory.triangleOfSESδ, projectionToShift, neg_neg]

noncomputable def triangle :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.triangleType :=
  fun _ _ _ _ _ hS => _root_.DerivedCategory.triangleOfSES hS

theorem triangle_arrows :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.triangle_arrowsType := by
  intro A _ _ _ S hS
  rfl

theorem distinguished :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.distinguishedType := by
  intro A _ _ _ S hS
  exact _root_.DerivedCategory.triangleOfSES_distinguished hS

noncomputable def triangleMap :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.triangleMapType :=
  fun _ _ _ _ _ _ hS hS' f => _root_.DerivedCategory.triangleOfSES.map hS hS' f

theorem naturality :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.naturalityType := by
  intro A _ _ _ S S' hS hS' f
  exact _root_.DerivedCategory.triangleOfSESδ_naturality hS hS' f

/-- The cochain cone row has the ordinary short-exact-sequence boundary after
composition with the canonical quasi-isomorphism q. -/
lemma cone_boundary {A : Type u} [Category.{v} A] [Abelian A]
    {S : ShortComplex (CochainComplex A ℤ)} (hS : S.ShortExact)
    (n m : ℤ) (h : n + 1 = m) :
    (HomologicalComplex.homologyFunctor A (.up ℤ) 0).shiftMap
      (mappingCone.triangle S.f).mor₃ n m (by omega) =
    HomologicalComplex.homologyMap (mappingCone.descShortComplex S) n ≫ hS.δ n m h := by
  have e := mappingCone.homologySequenceδ_triangleh hS n m h
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at e
  apply (cancel_epi ((HomotopyCategory.homologyFunctorFactors A (.up ℤ) n).hom.app
    (mappingCone S.f))).mp
  apply (cancel_mono ((HomotopyCategory.homologyFunctorFactors A (.up ℤ) m).inv.app S.X₁)).mp
  convert e using 1 <;> first | rfl | simp only [Category.assoc,
    mappingCone.triangle_obj₁, mappingCone.triangle_obj₃]

theorem cohomology_boundary :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.cohomology_boundaryType := by
  intro A _ _ _ S hS n m h
  have := mappingCone.quasiIso_descShortComplex hS
  apply (cancel_epi ((_root_.DerivedCategory.homologyFunctor A n).map
    (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S)))).mp
  dsimp only [row, _root_.DerivedCategory.HomologySequence.δ]
  rw [← Category.assoc]
  erw [← (_root_.DerivedCategory.homologyFunctor A 0).shiftMap_comp'
    (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S))
    (_root_.DerivedCategory.triangleOfSESδ hS) n m (by omega)]
  change (_root_.DerivedCategory.homologyFunctor A 0).shiftMap
      (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S) ≫
        _root_.DerivedCategory.triangleOfSESδ hS) n m _ ≫ _ = _
  rw [_root_.DerivedCategory.descShortComplex_triangleOfSESδ]
  rw [show _root_.DerivedCategory.Q.map (mappingCone.triangle S.f).mor₃ ≫
      (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ =
      ShiftedHom.map (mappingCone.triangle S.f).mor₃ _root_.DerivedCategory.Q from rfl]
  rw [_root_.DerivedCategory.shiftMap_homologyFunctor_map_Q
    (mappingCone.triangle S.f).mor₃ n m (by omega), cone_boundary hS n m h]
  simp only [mappingCone.triangle_obj₁, mappingCone.triangle_obj₃,
    Category.assoc, Iso.inv_hom_id_app]
  rw [_root_.DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  exact congrArg (fun k =>
    (_root_.DerivedCategory.homologyFunctorFactors A n).hom.app (mappingCone S.f) ≫
      HomologicalComplex.homologyMap (mappingCone.descShortComplex S) n ≫ k)
        (Category.comp_id (hS.δ n m h))

theorem lift_differential :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.lift_differentialType := by
  intro A _ _ S hS n m h P c hc b hb a ha
  exact hS.δ_eq n m h c hc b hb a ha (m + 1) (by simp)

theorem cohomologyExact :
    Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.cohomologyExactType := by
  intro A _ _ _ S hS
  exact AdvancedHomologicalAlgebra.DerivedCategory.cohomologyExact A (row hS)
    (_root_.DerivedCategory.triangleOfSES_distinguished hS)

end AdvancedHomologicalAlgebra.ShortExactDerivedTriangle
