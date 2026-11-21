import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.StandardHeart

/-! HA-D07. The canonical library t-structure uses strict models. Its
cohomological characterization identifies it with the source's two aisles.
Strict models with both bounds zero are stalks, proving essential surjectivity
onto the heart. Full faithfulness and H^0 of a stalk then give the equivalence
with precisely H^0 as inverse. Orthogonality gives the negative Hom vanishing. -/

set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open Specs.AdvancedHomologicalAlgebra.DerivedCategory
open Specs.AdvancedHomologicalAlgebra.StandardHeart

namespace AdvancedHomologicalAlgebra.StandardHeart

noncomputable def tStructure : tStructureType := tStructureValue

noncomputable def stalkEmbedding : stalkType := stalkValue

theorem cohomologicalAisles : cohomologicalAislesType := by
  intro A _ _ _ n X
  exact ⟨((standardT A).le_iff_isLE X n).trans (_root_.DerivedCategory.isLE_iff X n),
    ((standardT A).ge_iff_isGE X n).trans (_root_.DerivedCategory.isGE_iff X n)⟩

theorem heartDescription : heartDescriptionType := by
  intro A _ _ _ X
  exact ((standardT A).mem_heart_iff X).trans
    (and_congr (_root_.DerivedCategory.isLE_iff X 0)
      (_root_.DerivedCategory.isGE_iff X 0))

theorem fullyFaithful : fullyFaithfulType := by
  intro A _ _ _
  exact ⟨.ofFullyFaithful _⟩

section Equivalence
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

instance toHeartFull : (toHeart A).Full := by
  dsimp [toHeart]
  infer_instance

instance toHeartFaithful : (toHeart A).Faithful := by
  dsimp [toHeart]
  infer_instance

instance toHeartEssSurj : (toHeart A).EssSurj where
  mem_essImage X := by
    have hX := ((standardT A).mem_heart_iff X.obj).mp X.property
    have := hX.1
    have := hX.2
    obtain ⟨Y, ⟨e⟩⟩ :=
      _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X.obj 0
    exact ⟨Y, ⟨ObjectProperty.isoMk (heart A) e.symm⟩⟩

instance toHeartIsEquivalence : (toHeart A).IsEquivalence where

/-- Computing H^0 on stalks gives the identity naturally. -/
noncomputable def stalkH0Iso : toHeart A ⋙ heartH0 A ≅ 𝟭 A :=
  _root_.DerivedCategory.singleFunctorCompHomologyFunctorIso A 0

/-- Adjust the inverse of the equivalence to be ordinary H^0 exactly. -/
noncomputable def equivalence : A ≌ Heart A :=
  let e := (toHeart A).asEquivalence
  e.changeInverse
    ((Functor.rightUnitor e.inverse).symm ≪≫
      (stalkH0Iso A).symm.inverseCompIso (G := e))

end Equivalence

theorem heartEquivalence : heartEquivalenceType := by
  intro A _ _ _
  exact ⟨equivalence A, rfl, rfl⟩

theorem negativeHoms : negativeHomsType := by
  intro A _ _ _ X Y m hm f
  have := (standardT A).isGE_shift ((stalk A).obj Y) 0 m (-m) (by omega)
  exact (standardT A).zero f 0 (-m) (by omega)

end AdvancedHomologicalAlgebra.StandardHeart
