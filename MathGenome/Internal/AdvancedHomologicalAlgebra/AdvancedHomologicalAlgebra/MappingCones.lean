import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MappingCones

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.MappingCones
namespace AdvancedHomologicalAlgebra.MappingCones

noncomputable def cone : Specs.AdvancedHomologicalAlgebra.MappingCones.coneType :=
  fun _ _ _ _ _ _ f => coneComplex f

noncomputable def degreeIso : Specs.AdvancedHomologicalAlgebra.MappingCones.degreeIsoType :=
  fun _ _ _ _ _ _ f n => degreeBiproductIso f n

noncomputable def inclusion : Specs.AdvancedHomologicalAlgebra.MappingCones.inclusionType :=
  fun _ _ _ _ _ _ f => targetInclusion f

noncomputable def projection : Specs.AdvancedHomologicalAlgebra.MappingCones.projectionType :=
  fun _ _ _ _ _ _ f => projectionToShift f

theorem degree_coordinates : Specs.AdvancedHomologicalAlgebra.MappingCones.degree_coordinatesType := by
  intro A _ _ _ X Y f n
  constructor <;> simp [degreeBiproductIso]

theorem differential : Specs.AdvancedHomologicalAlgebra.MappingCones.differentialType := by
  intro A _ _ _ X Y f n
  constructor
  · simpa only [add_comm] using mappingCone.d_snd_v f n (n+1) rfl
  · simpa only [Preadditive.neg_comp] using mappingCone.d_fst_v f n (n+1) (n+1+1) rfl rfl

theorem inclusion_components : Specs.AdvancedHomologicalAlgebra.MappingCones.inclusion_componentsType := by
  intro A _ _ _ X Y f n
  constructor <;> simp [targetInclusion, targetProjection, shiftProjection]

theorem projection_components : Specs.AdvancedHomologicalAlgebra.MappingCones.projection_componentsType := by
  intro A _ _ _ X Y f n
  apply mappingCone.ext_from f (n+1) n rfl
  · simp [projectionToShift, shiftProjection, Preadditive.comp_neg, CochainComplex.shiftFunctorObjXIso]
  · simp [projectionToShift, shiftProjection, Preadditive.comp_neg]

noncomputable def coneMap : Specs.AdvancedHomologicalAlgebra.MappingCones.coneMapType :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => chosenConeMap h

theorem coneMap_formula : Specs.AdvancedHomologicalAlgebra.MappingCones.coneMap_formulaType := by
  intro A _ _ _ X Y X' Y' f f' a b h n
  dsimp only [chosenConeMap]
  rw [mappingCone.mapOfHomotopy, mappingCone.desc_f _ _ _ _ n (n+1) rfl]
  simp [targetProjection, shiftProjection, targetInclusion, shiftInclusion, Cochain.equivHomotopy, Cochain.ofHomotopy,
    Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Preadditive.comp_add]
  abel

theorem coneMap_inclusion : Specs.AdvancedHomologicalAlgebra.MappingCones.coneMap_inclusionType := by
  intro A _ _ _ X Y X' Y' f f' a b h
  exact mappingCone.triangleMapOfHomotopy_comm₂ h

theorem coneMap_projection : Specs.AdvancedHomologicalAlgebra.MappingCones.coneMap_projectionType := by
  intro A _ _ _ X Y X' Y' f f' a b h
  change mappingCone.mapOfHomotopy h ≫ (-(mappingCone.triangle f').mor₃) =
    (-(mappingCone.triangle f).mor₃) ≫ a⟦(1 : ℤ)⟧'
  rw [Preadditive.comp_neg, Preadditive.neg_comp,
    mappingCone.triangleMapOfHomotopy_comm₃ h]

noncomputable def strictMap : Specs.AdvancedHomologicalAlgebra.MappingCones.strictMapType :=
  fun _ _ _ _ _ _ _ _ f f' a b w => strictConeMap f f' a b w

theorem strictMap_zeroHomotopy : Specs.AdvancedHomologicalAlgebra.MappingCones.strictMap_zeroHomotopyType := by
  intro A _ _ _ X Y X' Y' f f' a b w
  exact mappingCone.map_eq_mapOfHomotopy f f' a b w

theorem strictMap_id : Specs.AdvancedHomologicalAlgebra.MappingCones.strictMap_idType := by
  intro A _ _ _ X Y f
  exact mappingCone.map_id f

theorem strictMap_comp : Specs.AdvancedHomologicalAlgebra.MappingCones.strictMap_compType := by
  intro A _ _ _ X Y X' Y' X'' Y'' f f' f'' a b a' b' w w'
  exact mappingCone.map_comp f f' f'' a b w a' b' w'

theorem inclusion_matrix : Specs.AdvancedHomologicalAlgebra.MappingCones.inclusion_matrixType := by
  intro A _ _ _ X Y f n
  ext <;> simp [degreeBiproductIso, targetInclusion, targetProjection, shiftProjection]

theorem projection_matrix : Specs.AdvancedHomologicalAlgebra.MappingCones.projection_matrixType := by
  intro A _ _ _ X Y f n
  rw [projection_components A X Y f n]
  ext <;> simp [degreeBiproductIso, targetProjection, shiftProjection, targetInclusion, shiftInclusion]

theorem differential_matrix : Specs.AdvancedHomologicalAlgebra.MappingCones.differential_matrixType := by
  intro A _ _ _ X Y f n
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst]
    rw [(degree_coordinates A X Y f (n+1)).1, (differential A X Y f n).1]
    ext <;> simp [degreeBiproductIso, targetProjection, shiftProjection, targetInclusion, shiftInclusion, Preadditive.comp_add]
  · simp only [Category.assoc, biprod.lift_snd]
    rw [(degree_coordinates A X Y f (n+1)).2, (differential A X Y f n).2]
    ext <;> simp [degreeBiproductIso, targetProjection, shiftProjection, targetInclusion, shiftInclusion, Preadditive.comp_neg]

theorem coneMap_matrix : Specs.AdvancedHomologicalAlgebra.MappingCones.coneMap_matrixType := by
  intro A _ _ _ X Y X' Y' f f' a b h n
  rw [coneMap_formula A X Y X' Y' f f' a b h n]
  ext <;> simp [degreeBiproductIso, targetProjection, shiftProjection, targetInclusion, shiftInclusion, Preadditive.comp_add, Preadditive.add_comp,
    Category.assoc]

end AdvancedHomologicalAlgebra.MappingCones
