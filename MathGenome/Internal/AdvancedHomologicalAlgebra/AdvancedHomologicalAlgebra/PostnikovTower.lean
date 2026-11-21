import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PostnikovTower

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.DerivedCategory
open Specs.AdvancedHomologicalAlgebra.StandardHeart
open Specs.AdvancedHomologicalAlgebra.PostnikovTower

namespace AdvancedHomologicalAlgebra.PostnikovTower

section Concentrated
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] (n : ℤ)

/-- Objects supported cohomologically at the single degree n. -/
def concentrated : ObjectProperty (D A) :=
  fun X => (standardT A).IsLE X n ∧ (standardT A).IsGE X n

noncomputable def singleToConcentrated : A ⥤ (concentrated A n).FullSubcategory :=
  (concentrated A n).lift (_root_.DerivedCategory.singleFunctor A n)
    (fun _ => ⟨inferInstance, inferInstance⟩)

instance : (singleToConcentrated A n).Full := by
  dsimp [singleToConcentrated]; infer_instance
instance : (singleToConcentrated A n).Faithful := by
  dsimp [singleToConcentrated]; infer_instance
instance : (singleToConcentrated A n).EssSurj where
  mem_essImage X := by
    have := X.property.1
    have := X.property.2
    obtain ⟨Y, ⟨e⟩⟩ :=
      _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X.obj n
    exact ⟨Y, ⟨ObjectProperty.isoMk _ e.symm⟩⟩
instance : (singleToConcentrated A n).IsEquivalence where

noncomputable abbrev concentratedHomology : (concentrated A n).FullSubcategory ⥤ A :=
  (concentrated A n).ι ⋙ HD A n

noncomputable def singleCompHomologyIso :
    singleToConcentrated A n ⋙ concentratedHomology A n ≅ 𝟭 A :=
  _root_.DerivedCategory.singleFunctorCompHomologyFunctorIso A n

noncomputable def concentratedEquivalence :
    A ≌ (concentrated A n).FullSubcategory :=
  let e := (singleToConcentrated A n).asEquivalence
  e.changeInverse
    ((Functor.rightUnitor e.inverse).symm ≪≫
      (singleCompHomologyIso A n).symm.inverseCompIso
        (G := e))

/-- The counit identifies any naturally concentrated family with its ordinary
cohomology stalk, naturally in the parameter. -/
noncomputable def concentratedIso (F : D A ⥤ D A)
    (h : ∀ X, concentrated A n (F.obj X)) :
    F ≅ F ⋙ HD A n ⋙ _root_.DerivedCategory.singleFunctor A n :=
  let G := (concentrated A n).lift F h
  NatIso.ofComponents (fun X =>
    ((concentrated A n).ι.mapIso ((concentratedEquivalence A n).counitIso.app
      (G.obj X))).symm) (by
        intro X Y f
        exact congrArg (fun k => k.hom)
          ((concentratedEquivalence A n).counitIso.inv.naturality (G.map f)))

end Concentrated

section Layers
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Upper truncation preserves the top retained cohomology. -/
lemma homology_inclusion_isIso (n : ℤ) (K : D A) :
    IsIso ((HD A n).map (((standardT A).truncLTι (n + 1)).app K)) := by
  let T := ((standardT A).triangleLTGE (n + 1)).obj K
  have hT := (standardT A).triangleLTGE_distinguished (n + 1) K
  have h₀ : IsZero ((HD A (n - 1)).obj T.obj₃) :=
    _root_.DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) (n - 1) (by omega)
  have h₁ : IsZero ((HD A n).obj T.obj₃) :=
    _root_.DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) n (by omega)
  have : Mono ((HD A n).map T.mor₁) :=
    (_root_.DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (n - 1) n
      (by omega)).mpr (h₀.eq_of_src _ _)
  have : Epi ((HD A n).map T.mor₁) :=
    (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT n).mpr
      (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((HD A n).map T.mor₁)

/-- Lower truncation preserves the bottom retained cohomology. -/
lemma homology_projection_isIso (n : ℤ) (K : D A) :
    IsIso ((HD A n).map (((standardT A).truncGEπ n).app K)) := by
  let T := ((standardT A).triangleLTGE n).obj K
  have hT := (standardT A).triangleLTGE_distinguished n K
  have h₀ : IsZero ((HD A n).obj T.obj₁) :=
    _root_.DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) n (by omega)
  have h₁ : IsZero ((HD A (n + 1)).obj T.obj₁) :=
    _root_.DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)
  have : Mono ((HD A n).map T.mor₂) :=
    (_root_.DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT n).mpr
      (h₀.eq_of_src _ _)
  have : Epi ((HD A n).map T.mor₂) :=
    (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1)
      rfl).mpr (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((HD A n).map T.mor₂)

/-- The single cohomological layer between adjacent truncations. -/
noncomputable abbrev piece (n : ℤ) : D A ⥤ D A :=
  (standardT A).truncGELT n (n + 1)

/-- Both truncation maps induce natural isomorphisms on H^n. -/
noncomputable def pieceHomologyIso (n : ℤ) : piece A n ⋙ HD A n ≅ HD A n := by
  let p : stage A n ⋙ HD A n ⟶ piece A n ⋙ HD A n :=
    Functor.whiskerRight
      (Functor.whiskerLeft (stage A n) ((standardT A).truncGEπ n)) (HD A n)
  let j : stage A n ⋙ HD A n ⟶ HD A n :=
    Functor.whiskerRight ((standardT A).truncLTι (n + 1)) (HD A n)
  have : IsIso p := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact homology_projection_isIso A n ((stage A n).obj K)
  have : IsIso j := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact homology_inclusion_isIso A n K
  exact (asIso p).symm ≪≫ asIso j

/-- The third term is the actual ordinary cohomology stalk H^n(K)[-n]. -/
noncomputable def pieceIso (n : ℤ) : piece A n ≅ layer A n :=
  concentratedIso A n (piece A n) (fun K => by
    constructor
    · exact (standardT A).isLE_of_le ((piece A n).obj K) ((n + 1) - 1) n (by omega)
    · exact inferInstanceAs ((standardT A).IsGE ((piece A n).obj K) n)) ≪≫
  Functor.isoWhiskerRight (pieceHomologyIso A n) (_root_.DerivedCategory.singleFunctor A n) ≪≫
  Functor.isoWhiskerLeft (HD A n)
    ((_root_.DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).symm

/-- Transport the functorial truncation triangles along the natural stalk identification. -/
noncomputable def tower : NaturalTower A where
  projection n :=
    Functor.whiskerLeft (stage A n) ((standardT A).truncGEπ n) ≫ (pieceIso A n).hom
  attachment n := (pieceIso A n).inv ≫ (standardT A).truncGELTδLT n (n + 1)
  distinguished n K := by
    let T := ((standardT A).triangleLTLTGELT n (n + 1) (by omega)).obj K
    let T' := Triangle.mk ((step A n).app K)
      ((Functor.whiskerLeft (stage A n) ((standardT A).truncGEπ n) ≫
        (pieceIso A n).hom).app K)
      (((pieceIso A n).inv ≫ (standardT A).truncGELTδLT n (n + 1)).app K)
    have e : T ≅ T' := Triangle.isoMk T T' (Iso.refl _) (Iso.refl _)
      ((pieceIso A n).app K) (by simp [T, T', step]) (by simp [T, T'])
      (by simp [T, T'])
    exact isomorphic_distinguished _
      ((standardT A).triangleLTLTGELT_distinguished n (n + 1) (by omega) K) _ e.symm

end Layers

/-- All successive triangles, with arrows natural in K. -/
theorem naturalTower : naturalTowerType := by
  intro A _ _ _
  exact ⟨tower A⟩

/-- The finite interval of successive triangles has the prescribed endpoints. -/
theorem finiteTower : finiteTowerType := by
  intro A _ _ _ K a b hab ha hb
  have : (standardT A).IsGE K a := (_root_.DerivedCategory.isGE_iff K a).mpr ha
  have hLE : (standardT A).IsLE K b := (_root_.DerivedCategory.isLE_iff K b).mpr hb
  exact ⟨{
    naturalTower := tower A
    ordered := hab
    initial := (standardT A).isZero_truncLT_obj_of_isGE a K
    terminal := ((standardT A).isLE_iff_isIso_truncLTι_app b (b + 1) rfl K).mp hLE
    rows := fun i _ => (tower A).distinguished i K }⟩

/-- Bounded cohomology gives suitable finite endpoints without any other assumptions. -/
theorem boundedTower : boundedTowerType := by
  intro A _ _ _ K ⟨a, b, ha, hb⟩
  exact ⟨a, max a b, finiteTower A K a (max a b) (le_max_left _ _) ha
    (fun i hi => hb i (lt_of_le_of_lt (le_max_right _ _) hi))⟩

end AdvancedHomologicalAlgebra.PostnikovTower
