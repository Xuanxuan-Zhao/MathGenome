import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafUniverseTransport
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory
open AdvancedHomologicalAlgebra.OriginalDerivedSectionsTheory
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
universe a b m u v r s

namespace AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients

open private exactDerivedPlus exactDerivedPlusFactors exactDerivedPlusCompιIso unit_isIso_of_injective
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology

open private exactHomologyIso exactHomologyIso_app postExactUnit postExactUnit_isDerived
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

section ComplexComposition

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

private lemma complexComposition_hom (K : CochainComplex.Plus A) :
    (complexComposition F G).hom.app K = 𝟙 _ := by
  apply (CochainComplex.Plus.ι C).map_injective
  rfl

end ComplexComposition

section CompositionUnit
open Specs.AdvancedHomologicalAlgebra.RightDerivedComposition

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

private lemma homotopyComposition_inv (K : CochainComplex.Plus A) :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app
      ((HomotopyCategory.Plus.quotient A).obj K) = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  change ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
    ((HomotopyCategory.quotient A (.up ℤ)).obj K.obj)) = _
  change (HomotopyCategory.quotient C (.up ℤ)).map
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K.obj) = _
  rw [show ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K.obj) =
    𝟙 _ by ext n; rfl]
  exact CategoryTheory.Functor.map_id _ _

omit [EnoughInjectives B] in
private lemma derivedUnit_eq_homotopy (K : CochainComplex.Plus A) :
    F.rightDerivedFunctorPlusUnit.app K =
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K) := by
  rw [Functor.rightDerivedFunctorPlusUnit_app]
  let L := (HomotopyCategory.Plus.quotient A).obj K
  change 𝟙 (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≫
    DerivedCategory.Plus.Qh.map (𝟙 (F.mapHomotopyCategoryPlus.obj L)) ≫
    F.rightDerivedFunctorPlusUnith.app L ≫
    F.rightDerivedFunctorPlus.map (𝟙 (DerivedCategory.Plus.Qh.obj L)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact (Category.id_comp (𝟙 _ ≫ F.rightDerivedFunctorPlusUnith.app L ≫ 𝟙 _)).trans
    ((Category.id_comp _).trans (Category.comp_id _))

private lemma composition_unit (K : CochainComplex.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
      (comparisonValue F G).app (DerivedCategory.Plus.Q.obj K) =
    (iteratedUnit F G).app K := by
  have h := congrArg (fun τ => τ.app ((HomotopyCategory.Plus.quotient A).obj K))
    (RightDerivedComposition.comparisonUniversal A B C F G).1
  simp only [iteratedUnit, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_id, complexComposition_hom] at ⊢
  rw [derivedUnit_eq_homotopy (F ⋙ G) K,
    derivedUnit_eq_homotopy G (F.mapCochainComplexPlus.obj K),
    derivedUnit_eq_homotopy F K]
  simp only [inputComparisonValue, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, associator_inv_app, Category.id_comp,
    Category.comp_id, homotopyComposition_inv] at h
  rw [CategoryTheory.Functor.map_id] at h
  exact h

end CompositionUnit

section Exact

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

private def exactDescent : ExactDescent T where
  functor := exactDerivedPlus T
  termwise := exactDerivedPlusCompιIso T
  factors := exactDerivedPlusFactors T
  factors_on_complex K := by
    change T.mapDerivedCategoryFactors.inv.app K.obj ≫ 𝟙 _ = _
    exact Category.comp_id _
  cohomology n := (exactHomologyIso T n).symm
  cohomology_on_complex n K := by
    let i := (DerivedCategory.Plus.homologyFunctor B n).mapIso ((exactDerivedPlusFactors T).app K) ≪≫
      (DerivedCategory.homologyFunctorFactors B n).app ((T.mapHomologicalComplex (.up ℤ)).obj K.obj) ≪≫
      (K.obj.sc n).mapHomologyIso T ≪≫
      T.mapIso ((DerivedCategory.homologyFunctorFactors A n).app K.obj).symm
    have hi : (exactHomologyIso T n).app (DerivedCategory.Plus.Q.obj K) = i.symm := by
      apply Iso.ext
      simpa only [i, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
        CategoryTheory.Functor.mapIso_inv, Category.assoc]
        using exactHomologyIso_app T K n
    exact congrArg Iso.inv hi

open private exactDerivedIdentification_on_complex from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsComposition

private theorem exactDescent_unit [EnoughInjectives A] :
    ExactDescent.UnitCompatibility T (exactDescent T) := by
  let e : T.rightDerivedFunctorPlus ≅ (exactDescent T).functor :=
    DerivedSectionsComposition.exactDerivedIdentification T
  refine ⟨e, fun K => ?_⟩
  apply DerivedCategory.Plus.ι.map_injective
  rw [CategoryTheory.Functor.map_comp]
  have h := exactDerivedIdentification_on_complex T K
  change DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlusUnit.app K) ≫
    DerivedCategory.Plus.ι.map (e.hom.app (DerivedCategory.Plus.Q.obj K)) ≫ 𝟙 _ =
      T.mapDerivedCategoryFactors.inv.app K.obj at h
  change DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlusUnit.app K) ≫
    DerivedCategory.Plus.ι.map (e.hom.app (DerivedCategory.Plus.Q.obj K)) =
      T.mapDerivedCategoryFactors.inv.app K.obj
  exact (congrArg (DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlusUnit.app K) ≫ ·)
    (Category.comp_id _).symm).trans h


end Exact

section ExactPostcomposition

attribute [local instance] HasDerivedCategory.standard

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [EnoughInjectives A]
  (F : A ⥤ B) (T : B ⥤ C) [F.Additive] [T.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

private def postcompositionIso :
    (F ⋙ T).rightDerivedFunctorPlus ≅ F.rightDerivedFunctorPlus ⋙ exactDerivedPlus T := by
  letI := postExactUnit_isDerived F T
  exact rightDerivedNatIso _ _ (F ⋙ T).rightDerivedFunctorPlusUnit (postExactUnit F T)
    (CochainComplex.Plus.quasiIso A) (isoWhiskerRight (complexComposition F T) _)

private lemma postcompositionIso_unit (K : CochainComplex.Plus A) :
    (F ⋙ T).rightDerivedFunctorPlusUnit.app K ≫
      (postcompositionIso F T).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((complexComposition F T).hom.app K) ≫
        (exactDerivedPlusFactors T).inv.app (F.mapCochainComplexPlus.obj K) ≫
        (exactDerivedPlus T).map (F.rightDerivedFunctorPlusUnit.app K) := by
  letI := postExactUnit_isDerived F T
  simp [postcompositionIso, rightDerivedNatIso, postExactUnit]

end ExactPostcomposition

section Transport

attribute [local instance] HasDerivedCategory.standard

open private exactComparisonComplexIso exactDerivedComparison exactDerivedComparison_unit preExactUnit
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open private restrictionDerivedUnit mapPlusCompIso
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [EnoughInjectives A] [EnoughInjectives A']
  (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
  [F.Additive] [G.Additive] [J.Additive] [H.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (c : F ⋙ H ≅ J ⋙ G)

private lemma complexSquare_eq :
    complexSquare F G J H c = exactComparisonComplexIso F G J H c := by
  apply Iso.ext
  ext I : 2
  apply (CochainComplex.Plus.ι B').map_injective
  apply HomologicalComplex.hom_ext
  intro n
  simp [complexSquare, exactComparisonComplexIso, mapPlusCompIso]

private def derivedUnitTransport
    (hJ : ∀ M, Injective M →
      Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue G (J.obj M)) :
    UnitTransport F G J H c (exactDescent J) (exactDescent H)
      F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit := by
  refine ⟨exactDerivedComparison F G J H c hJ, ?_⟩
  intro I
  have h := exactDerivedComparison_unit F G J H c hJ I
  simp only [postExactUnit, preExactUnit, restrictionDerivedUnit, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at h
  dsimp only [RespectsModelUnits]
  rw [complexSquare_eq]
  apply (cancel_epi ((exactDerivedPlusFactors H).inv.app
    (F.mapCochainComplexPlus.obj I))).mp
  dsimp only [exactDescent]
  rw [Iso.inv_hom_id_app_assoc]
  exact h

private def derivedModelTransport (hJ : ∀ M, Injective M → Injective (J.obj M)) :
    ModelTransport F G J H c (exactDescent J) (exactDescent H)
      F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit :=
  let d := derivedUnitTransport F G J H c fun M hM ↦ by
    letI := hJ M hM
    exact AcyclicTermComparison.rightAcyclic_of_injective G (J.obj M)
  ⟨d.iso, fun I _ ↦ d.on_complex I⟩

private def exactUnitTransport [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (p : ExactDescent F) (q : ExactDescent G)
    (hp : ExactDescent.UnitCompatibility F p) (hq : ExactDescent.UnitCompatibility G q) :
    UnitTransport F G J H c (exactDescent J) (exactDescent H) p.factors.inv q.factors.inv := by
  let e := derivedUnitTransport F G J H c fun M _ ↦
    DerivedSectionsComposition.exactUnitIso G _
  let l := hp.choose
  let k := hq.choose
  refine ⟨isoWhiskerRight l.symm _ ≪≫ e.iso ≪≫ isoWhiskerLeft _ k, ?_⟩
  intro I
  have hl := hp.choose_spec I
  have hk := hq.choose_spec (J.mapCochainComplexPlus.obj I)
  change F.rightDerivedFunctorPlusUnit.app I ≫ l.hom.app (DerivedCategory.Plus.Q.obj I) =
    p.factors.inv.app I at hl
  change G.rightDerivedFunctorPlusUnit.app (J.mapCochainComplexPlus.obj I) ≫
    k.hom.app (DerivedCategory.Plus.Q.obj (J.mapCochainComplexPlus.obj I)) = _ at hk
  have he := e.on_complex I
  dsimp only [RespectsModelUnits] at he ⊢
  rw [← hl, ← hk]
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, NatTrans.comp_app, Iso.symm_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← (exactDescent H).functor.map_comp_assoc (l.hom.app (DerivedCategory.Plus.Q.obj I)),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% he, k.hom.naturality ((exactDescent J).factors.inv.app I)]
  rfl

variable {F G J H c}

/-- Identify two functors with their normalized injective models before
transporting them. The resulting maps are determined by the actual units. -/
private def transportOfComparisons
    {j : ExactDescent J} {h : ExactDescent H}
    (d : ModelTransport F G J H c j h F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit)
    {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {L' : DerivedCategory.Plus A' ⥤ DerivedCategory.Plus B'}
    (l : F.rightDerivedFunctorPlus ≅ L) (l' : G.rightDerivedFunctorPlus ≅ L')
    (η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L)
    (η' : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L')
    (hl : ∀ I : CochainComplex.Plus A, (∀ n, Injective (I.obj.X n)) →
      F.rightDerivedFunctorPlusUnit.app I ≫ l.hom.app (DerivedCategory.Plus.Q.obj I) = η.app I)
    (hl' : ∀ I : CochainComplex.Plus A', (∀ n, Injective (I.obj.X n)) →
      G.rightDerivedFunctorPlusUnit.app I ≫ l'.hom.app (DerivedCategory.Plus.Q.obj I) = η'.app I)
    (hJ : ∀ M, Injective M → Injective (J.obj M)) :
    ModelTransport F G J H c j h η η' where
  iso := isoWhiskerRight l.symm h.functor ≪≫ d.iso ≪≫ isoWhiskerLeft j.functor l'
  on_injective I hI := by
    rw [← hl I hI, ← hl' (J.mapCochainComplexPlus.obj I) (fun n => hJ _ (hI n))]
    simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
      whiskerRight_app, NatTrans.comp_app, Iso.symm_hom, CategoryTheory.Functor.map_comp,
      Category.assoc]
    rw [← h.functor.map_comp_assoc (l.hom.app (DerivedCategory.Plus.Q.obj I)),
      Iso.hom_inv_id_app, h.functor.map_id, Category.id_comp]
    erw [reassoc_of% (d.on_injective I hI)]
    erw [l'.hom.naturality (j.factors.inv.app I)]
    rfl

end Transport

section Pasting

attribute [local instance] HasDerivedCategory.standard

variable {A A' B B' C C' : Type*}
  [Category* A] [Category* A'] [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  {F : A ⥤ B} {F' : A' ⥤ B'} {G : B ⥤ C} {G' : B' ⥤ C'}
  {J : A ⥤ A'} {H : B ⥤ B'} {T : C ⥤ C'}
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [J.Additive] [H.Additive] [T.Additive]

private lemma complexSquare_compose_app (c : F ⋙ H ≅ J ⋙ F') (d : G ⋙ T ≅ H ⋙ G')
    (I : CochainComplex.Plus A) :
    (complexSquare (F ⋙ G) (F' ⋙ G') J T (composeFunctorSquares c d)).hom.app I =
      (complexSquare G G' H T d).hom.app (F.mapCochainComplexPlus.obj I) ≫
        G'.mapCochainComplexPlus.map ((complexSquare F F' J H c).hom.app I) := by
  apply (CochainComplex.Plus.ι C').map_injective
  apply HomologicalComplex.hom_ext
  intro n
  change (composeFunctorSquares c d).hom.app (I.obj.X n) =
    d.hom.app (F.obj (I.obj.X n)) ≫ G'.map (c.hom.app (I.obj.X n))
  simp [composeFunctorSquares]

private lemma compositeUnit_app
    {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {M : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C}
    (η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L)
    (θ : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ M)
    (I : CochainComplex.Plus A) :
    (compositeUnit F G η θ).app I =
      θ.app (F.mapCochainComplexPlus.obj I) ≫ M.map (η.app I) := by
  simp only [compositeUnit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, associator_inv_app, complexComposition_hom,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact Category.id_comp _

variable [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

private def composeUnitTransport {c : F ⋙ H ≅ J ⋙ F'} {d : G ⋙ T ≅ H ⋙ G'}
    {j : ExactDescent J} {h : ExactDescent H} {t : ExactDescent T}
    {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {L' : DerivedCategory.Plus A' ⥤ DerivedCategory.Plus B'}
    {M : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C}
    {M' : DerivedCategory.Plus B' ⥤ DerivedCategory.Plus C'}
    {η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L}
    {η' : F'.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L'}
    {θ : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ M}
    {θ' : G'.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ M'}
    (e : UnitTransport F F' J H c j h η η') (g : UnitTransport G G' H T d h t θ θ') :
    UnitTransport (F ⋙ G) (F' ⋙ G') J T (composeFunctorSquares c d) j t
      (compositeUnit F G η θ) (compositeUnit F' G' η' θ') where
  iso := composeFunctorSquares e.iso g.iso
  on_complex I := by
    have hF := e.on_complex I
    have hG := g.on_complex (F.mapCochainComplexPlus.obj I)
    dsimp only [RespectsModelUnits] at hF hG ⊢
    rw [compositeUnit_app, compositeUnit_app, complexSquare_compose_app]
    simp only [composeFunctorSquares, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, CategoryTheory.Functor.comp_map,
      CategoryTheory.Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
    have hn := g.iso.hom.naturality (η.app I)
    simp only [CategoryTheory.Functor.comp_map] at hn
    rw [reassoc_of% hn, reassoc_of% hG]
    rw [← M'.map_comp (h.functor.map (η.app I)), hF,
      ← M'.map_comp ((h.factors).inv.app (F.mapCochainComplexPlus.obj I)),
      Iso.inv_hom_id_app_assoc]
    simp only [CategoryTheory.Functor.map_comp]
    have ht := θ'.naturality ((complexSquare F F' J H c).hom.app I)
    simp only [CategoryTheory.Functor.comp_map] at ht
    rw [← reassoc_of% ht]
    rfl

end Pasting

section Coherence

attribute [local instance] HasDerivedCategory.standard

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B'] [EnoughInjectives A]
  {F : A ⥤ B} {G : A' ⥤ B'} {J : A ⥤ A'} {H : B ⥤ B'}
  [F.Additive] [G.Additive] [J.Additive] [H.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {c : F ⋙ H ≅ J ⋙ G} {j : ExactDescent J} {h : ExactDescent H}

private lemma natTrans_ext_on_injective
    {E E' : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B'}
    {α β : E ⟶ E'}
    (eq : ∀ I : CochainComplex.Plus A, (∀ n, Injective (I.obj.X n)) →
      α.app (DerivedCategory.Plus.Q.obj I) = β.app (DerivedCategory.Plus.Q.obj I)) : α = β := by
  apply NatTrans.ext
  funext K
  obtain ⟨n, hn⟩ := K.property
  letI : K.IsGE n := (K.isGE_ι_obj_iff n).mp hn
  obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  apply (cancel_epi (E.map e.hom)).mp
  rw [α.naturality, β.naturality, eq _ (fun i ↦ (I.obj.X i).property)]

variable {L M : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
  {L' M' : DerivedCategory.Plus A' ⥤ DerivedCategory.Plus B'}
  {η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L}
  {η' : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L'}
  {θ : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ M}
  {θ' : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ M'}

private lemma transport_commutes
    (d : UnitTransport F G J H c j h η η') (e : UnitTransport F G J H c j h θ θ')
    (p : L ≅ M) (q : L' ≅ M')
    (hp : ∀ I, η.app I ≫ p.hom.app (DerivedCategory.Plus.Q.obj I) = θ.app I)
    (hq : ∀ I, η'.app I ≫ q.hom.app (DerivedCategory.Plus.Q.obj I) = θ'.app I)
    (hη : ∀ I : CochainComplex.Plus A, (∀ n, Injective (I.obj.X n)) → IsIso (η.app I))
    (K : DerivedCategory.Plus A) :
    h.functor.map (p.hom.app K) ≫ e.iso.hom.app K =
      d.iso.hom.app K ≫ q.hom.app (j.functor.obj K) := by
  have hc : whiskerRight p.hom h.functor ≫ e.iso.hom =
      d.iso.hom ≫ whiskerLeft j.functor q.hom := by
    apply natTrans_ext_on_injective
    intro I hI
    haveI := hη I hI
    have h₁ := d.on_complex I
    have h₂ := e.on_complex I
    dsimp only [RespectsModelUnits] at h₁ h₂
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    apply (cancel_epi (h.functor.map (η.app I))).mp
    simp only [← h.functor.map_comp_assoc, hp, h₂, reassoc_of% h₁]
    have hn := q.hom.naturality (j.factors.inv.app I)
    simp only [CategoryTheory.Functor.comp_obj] at hn
    rw [hn, reassoc_of% (hq (J.mapCochainComplexPlus.obj I))]
  exact NatTrans.congr_app hc K

private lemma lifted_unit_isIso
    (d : UnitTransport F G J H c j h η η') (I : CochainComplex.Plus A)
    [IsIso (η.app I)] : IsIso (η'.app (J.mapCochainComplexPlus.obj I)) := by
  have eq := d.on_complex I
  dsimp only [RespectsModelUnits] at eq
  haveI : IsIso (h.factors.hom.app (F.mapCochainComplexPlus.obj I) ≫
      DerivedCategory.Plus.Q.map ((complexSquare F G J H c).hom.app I) ≫
      η'.app (J.mapCochainComplexPlus.obj I) ≫ L'.map (j.factors.inv.app I)) := by
    rw [← eq]
    infer_instance
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using this

end Coherence

section
variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

variable [HasSheafify (Opens.grothendieckTopology X)
    AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{max a u v r s}]
variable [HasSheafify (Opens.grothendieckTopology Y)
    AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max a u v r s}]
attribute [local instance] HasDerivedCategory.standard

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "D" => ambientDirectImage.{a} f
set_option hygiene false in
local notation "ΓX" => globalSections.{max a v s} R
set_option hygiene false in
local notation "ΓY" => globalSections.{max a u r} S
set_option hygiene false in
local notation "Res" => scalarRestriction.{a} f
set_option hygiene false in
local notation "SY" => SectionModules.{max a u r} S (⊤ : Opens Y)

variable [EnoughInjectives A] [EnoughInjectives B]

private lemma sectionsTermwiseUnit_eq (t : ExactDescent Res) :
    sectionsTermwiseUnit.{a} f t =
      compositeUnit ΓX Res (ΓX).rightDerivedFunctorPlusUnit t.factors.inv := by
  have h : (sectionsIdentity.{a} f).hom = 𝟙 _ := rfl
  apply NatTrans.ext
  funext I
  simp only [sectionsTermwiseUnit, NatTrans.comp_app, whiskerRight_app]
  rw [h, NatTrans.mapCochainComplexPlus_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  exact Category.id_comp _

private lemma sectionsTermwiseUnit_isIso (c : SectionsData.{a} f) (I : CochainComplex.Plus A)
    (hI : ∀ n, Injective (I.obj.X n)) :
    IsIso ((sectionsTermwiseUnit.{a} f c.restriction).app I) := by
  haveI := unit_isIso_of_injective ΓX I hI
  rw [sectionsTermwiseUnit_eq.{a}, compositeUnit_app]
  infer_instance

private lemma sectionsData_unit (I : CochainComplex.Plus A) :
    (D ⋙ ΓY).rightDerivedFunctorPlusUnit.app I ≫
      (postcompositionIso ΓX Res).hom.app (DerivedCategory.Plus.Q.obj I) =
    (sectionsTermwiseUnit.{a} f (exactDescent Res)).app I := by
  rw [sectionsTermwiseUnit_eq.{a}]
  simp only [compositeUnit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id]
  exact postcompositionIso_unit ΓX Res I

private def sectionsData : SectionsData.{a} f where
  restriction := exactDescent Res
  restriction_unit := exactDescent_unit Res
  comparison := postcompositionIso ΓX Res
  on_injective I _ := sectionsData_unit.{a} f I
  composition_isIso := by
    letI := HigherDirectImagesIndependentCoefficients.leftExact.{max a u v r s,u,v,r,s} f
    letI := original_sections_left_exact.{max a u r,v,s} Y S (⊤ : Opens Y)
    have h (I : A) (hI : Injective I) :
        Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue ΓY ((D).obj I) := by
      apply (AcyclicTermComparison.rightVanishing B SY ΓY _).mpr
      intro n
      exact (HigherDirectImagesIndependentCoefficients.injectiveImageAcyclic.{a,u,v,r,s} f I hI).2 ⊤ n
    letI := (RightDerivedComposition.comparisonIsoIff A B SY D ΓY).mpr h
    exact NatIso.isIso_of_isIso_app _

end

theorem derivedSections : derivedSectionsType.{a,u,v,r,s} := by
  intro X Y R S f
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{a,u,v,r,s} f).1
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{a,u,v,r,s} f).2
  exact ⟨inferInstance, inferInstance, ⟨sectionsData.{a} f⟩⟩

theorem underivedCoherence : underivedCoherenceType.{a,u,v,r,s} := by
  intro X Y R S f
  apply Iso.ext
  ext M x
  rfl

theorem coefficientCoherence : coefficientCoherenceType.{a,m,u,v,r,s} := by
  intro X Y R S f
  apply Iso.ext
  ext M x
  rfl

theorem coefficientExact : coefficientExactType.{a,m,u,v,r,s} := by
  intro X Y R S f
  exact coefficient_lift_original_sheaf_short_exact.{max a v s,u,r,m} X R


section SiteTransport

open Specs.AdvancedHomologicalAlgebra.RightDerivedComposition

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
attribute [local instance] HasDerivedCategory.standard

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "D" => ambientDirectImage.{a} f
set_option hygiene false in
local notation "ΓY" => globalSections.{max a u r} S
set_option hygiene false in
local notation "J" => transport.{max a v s} R
set_option hygiene false in
local notation "H" => targetScalars.{a} f
set_option hygiene false in
local notation "DX" => transportedDirectImage.{a} f
set_option hygiene false in
local notation "LX" => AdvancedHomologicalAlgebra.DerivedSectionsTheory.globalSections (liftedRing.{max a v s} R)
set_option hygiene false in
local notation "LY" => AdvancedHomologicalAlgebra.DerivedSectionsTheory.globalSections (liftedRing.{max a u r} S)
set_option hygiene false in
local notation "LT" => liftedRestriction.{a} f
set_option hygiene false in
local notation "AX" => AdvancedHomologicalAlgebra.SheafTheory.Modules (liftedRing.{max a v s} R)

variable [EnoughInjectives A] [EnoughInjectives B]
variable [(J).IsEquivalence]

private def liftedCoordinates (c : liftedSectionsData.{a} f) :
    LiftedRestrictionCoordinates.{a} f c := by
  let t := exactDescent LT
  let ff := ((DerivedCategory.TStructure.t
    (C := ModuleCat.{max a u v r s} ((liftedRing.{max a u r} S).obj.obj (op ⊤)))).plus.fullyFaithfulι).whiskeringRight
      (DerivedCategory.Plus
        (ModuleCat.{max a u v r s} ((liftedRing.{max a v s} R).obj.obj (op ⊤))))
  let e := ff.preimageIso (c.restriction.termwise ≪≫ t.termwise.symm)
  refine ⟨t, e, ?_, ?_⟩
  · have he : isoWhiskerRight e DerivedCategory.Plus.ι =
        c.restriction.termwise ≪≫ t.termwise.symm := by
      apply Iso.ext
      exact ff.map_preimage _
    rw [he]
    cat_disch
  · intro n
    apply Iso.ext
    let Q := DerivedCategory.Plus.Q
      (C := ModuleCat.{max a u v r s} ((liftedRing.{max a v s} R).obj.obj (op ⊤)))
    apply (Localization.fullyFaithfulWhiskeringLeft Q (CochainComplex.Plus.quasiIso _) _).map_injective
    apply NatTrans.ext
    funext K
    let b := isoWhiskerRight t.termwise (DerivedCategory.homologyFunctor _ n) ≪≫
      associator .. ≪≫ isoWhiskerLeft DerivedCategory.Plus.ι (c.restriction.homology n) ≪≫
      (associator ..).symm
    change (t.cohomology n).hom.app (Q.obj K) = b.hom.app (Q.obj K)
    rw [t.cohomology_on_complex]
    simp only [b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerLeft_app, whiskerRight_app, associator_hom_app,
      associator_inv_app, Category.id_comp, Category.comp_id]
    rw [show (t.termwise.hom.app (Q.obj K)) = 𝟙 _ from rfl]
    rw [CategoryTheory.Functor.map_id]
    exact (c.restriction.homology_on_complex n K.obj).symm.trans (Category.id_comp _).symm

private lemma liftedCoordinates_unit (c : liftedSectionsData.{a} f)
    (I : CochainComplex.Plus AX) (hI : ∀ n, Injective (I.obj.X n)) :
    (DX ⋙ LY).rightDerivedFunctorPlusUnit.app I ≫
      (LiftedRestrictionCoordinates.comparison f (liftedCoordinates f c)).hom.app
        (DerivedCategory.Plus.Q.obj I) =
      (liftedTermwiseUnit.{a} f (liftedCoordinates f c).descent).app I := by
  let t := (liftedCoordinates f c).descent
  let A₀ := DerivedCategory.Plus.Q.obj I
  let V := (LX).rightDerivedFunctorPlus.obj A₀
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono (t.termwise.hom.app V)).mp
  have he := congrArg (fun e => e.hom.app V) (liftedCoordinates f c).termwise
  have hc := c.on_injective I hI
  have hη := t.termwise.hom.naturality ((LX).rightDerivedFunctorPlusUnit.app I)
  have hid : (liftedSectionsIdentity.{a} f).hom = 𝟙 _ := rfl
  have hcomp :
      ((mapHomologicalComplexCompIso (liftedSectionsIdentity.{a} f).symm (.up ℤ)).inv.app I.obj) =
        𝟙 _ := by
    ext n
    rfl
  simp only [LiftedRestrictionCoordinates.comparison, Iso.trans_hom, isoWhiskerLeft_hom,
    whiskerLeft_app, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
    Category.assoc] at ⊢
  change DerivedCategory.Plus.ι.map ((liftedCoordinates f c).identify.hom.app V) ≫
    t.termwise.hom.app V = c.restriction.termwise.hom.app V at he
  erw [he, hc]
  simp only [liftedTermwiseUnit, termwiseUnit, hid, NatTrans.mapCochainComplexPlus_id,
    NatTrans.id_app, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, CategoryTheory.Functor.map_comp,
    complexComposition_hom, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.assoc, hcomp]
  let K := (LX).mapCochainComplexPlus.obj I
  simp only [CategoryTheory.Functor.comp_map] at hη
  have h := congrArg (fun k => DerivedCategory.Plus.ι.map (t.factors.inv.app K) ≫ k) hη
  simp only [← Category.assoc] at h
  erw [t.factors_on_complex K] at h
  simp only [Category.assoc] at h
  let LYMod := ModuleCat.{max a u v r s} ((liftedRing.{max a u r} S).obj.obj (op ⊤))
  let W := DerivedCategory.Plus.Q.obj ((DX ⋙ LY).mapCochainComplexPlus.obj I)
  have hi := (DerivedCategory.Plus.ι (C := LYMod)).map_id W
  erw [hi]
  exact h.symm.trans ((Category.id_comp _).symm.trans (Category.id_comp _).symm)

private def siteTransportData (c : SectionsData.{a} f) (c' : liftedSectionsData.{a} f) :
    SiteTransportData.{a} f c c' := by
  let e := liftedCoordinates f c'
  letI : (H).Additive := by
    constructor
    intro M N g k
    ext x
    rfl
  letI : (H).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max a u v r s,s,max a u v r s}
      (sectionRingEquiv.{max a u r} S (⊤ : Opens (liftedSpace.{max a u v r s} Y))).symm).isEquivalence_functor
  have hJ (M : A) (hM : Injective M) : Injective ((J).obj M) :=
    ((ambient_mono_injective.{max a v s,u,r} X R M M (𝟙 M)).2).mpr hM
  let d := derivedModelTransport (D ⋙ ΓY) (DX ⋙ LY) J H (compositeSquare.{a} f) hJ
  letI := c.composition_isIso
  letI := c'.composition_isIso
  let l := asIso (comparisonValue D ΓY)
  let l' := asIso (comparisonValue DX LY)
  let L := transportOfComparisons d c.comparison (e.comparison f)
    (sectionsTermwiseUnit.{a} f c.restriction) (liftedTermwiseUnit.{a} f e.descent)
    (fun I hI => c.on_injective I hI) (liftedCoordinates_unit f c') hJ
  let K := transportOfComparisons d l l' (iteratedUnit D ΓY) (iteratedUnit DX LY)
    (fun I _ => composition_unit D ΓY I) (fun I _ => composition_unit DX LY I) hJ
  refine ⟨e, exactDescent J, exactDescent H, L, K, ?_⟩
  intro P
  dsimp only [L, K, transportOfComparisons, SectionsData.iteratedIso,
    LiftedRestrictionCoordinates.iterated, LiftedRestrictionCoordinates.comparison,
    AdvancedHomologicalAlgebra.DerivedSectionsTheory.SectionsDerivedData.iteratedIso]
  simp only [Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_inv, isoWhiskerLeft_hom, whiskerRight_app,
    whiskerLeft_app, NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  change (exactDescent H).functor.map (c.comparison.inv.app P) ≫
    (exactDescent H).functor.map (l.hom.app P) ≫
    (exactDescent H).functor.map (l.inv.app P) ≫ _ = _
  rw [← (exactDescent H).functor.map_comp_assoc (l.hom.app P) (l.inv.app P),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.hom_inv_id_app_assoc]
  rfl

private theorem modelEquation (c : SectionsData.{a} f) (I : CochainComplex.Plus A)
    (h : (D ⋙ ΓY).rightDerivedFunctorPlusUnit.app I ≫
        c.comparison.hom.app (DerivedCategory.Plus.Q.obj I) =
      (sectionsTermwiseUnit.{a} f c.restriction).app I) : c.ModelEquation f I := by
  let P := DerivedCategory.Plus.Q.obj I
  letI := c.composition_isIso
  change (D ⋙ ΓY).rightDerivedFunctorPlusUnit.app I ≫ c.comparison.hom.app P =
    (sectionsTermwiseUnit.{a} f c.restriction).app I at h
  have he :
      (sectionsTermwiseUnit.{a} f c.restriction).app I ≫ c.iteratedIso.hom.app P =
        (iteratedUnit D ΓY).app I := by
    rw [← h]
    simp only [SectionsData.iteratedIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, asIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
    exact composition_unit D ΓY I
  refine ⟨he, ?_⟩
  intro n
  have hc := congrArg (DerivedCategory.Plus.homologyFunctor _ n).map he
  simp only [CategoryTheory.Functor.map_comp] at hc
  simp only [SectionsData.cohomologyIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, Category.id_comp, Iso.hom_inv_id_app_assoc]
  exact hc

private theorem modelComparison (c : SectionsData.{a} f) : c.IsModelComparison f :=
  fun I hI ↦ modelEquation f c I (c.on_injective I hI)

private theorem sectionsData_modelEquation (I : CochainComplex.Plus A) :
    (sectionsData.{a} f).ModelEquation f I :=
  modelEquation.{a} f (sectionsData.{a} f) I (sectionsData_unit.{a} f I)

private theorem cohomologyCoherence (c : SectionsData.{a} f) (c' : liftedSectionsData.{a} f)
    (d : SiteTransportData.{a} f c c') : d.CohomologyCoherence f := by
  intro K n
  let F := DerivedCategory.Plus.homologyFunctor
    (ModuleCat.{max a u v r s} ((liftedRing.{max a u r} S).obj.obj (op ⊤))) n
  have h := congrArg F.map (d.commutes K)
  have hn := (d.scalars.cohomology n).inv.naturality (c.iteratedIso.hom.app K)
  simp only [CategoryTheory.Functor.map_comp] at h
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map] at hn
  simp only [SectionsData.cohomologyIso, ModelTransport.cohomology,
    SiteTransportData.restrictedCohomology, LiftedRestrictionCoordinates.cohomologyIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    CategoryTheory.Functor.map_comp, Category.assoc,
    Category.comp_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% hn]
  exact congrArg (fun k ↦ (H).map ((c.restriction.cohomology n).inv.app
    ((globalSections.{max a v s} R).rightDerivedFunctorPlus.obj K)) ≫
      (d.scalars.cohomology n).inv.app _ ≫ k) h


end SiteTransport

theorem transportComparison : transportType.{a,u,v,r,s} := by
  intro X Y R S f
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{a,u,v,r,s} f).1
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{a,u,v,r,s} f).2
  letI := ambient_equivalence.{max a v s,u,r} X R
  exact ⟨inferInstance, inferInstance, inferInstance, sectionsData.{a} f,
    modelComparison f (sectionsData.{a} f),
    fun c' => ⟨siteTransportData.{a} f (sectionsData.{a} f) c',
      cohomologyCoherence.{a} f _ _ _⟩⟩



section CoefficientTransport

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

attribute [local instance] HasDerivedCategory.standard

set_option hygiene false in
local notation "A₀" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "A₁" => AmbientSheaves.{max a b v s} R
set_option hygiene false in
local notation "B₀" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "B₁" => AmbientSheaves.{max a b u r} S
set_option hygiene false in
local notation "D₀" => ambientDirectImage.{a} f
set_option hygiene false in
local notation "D₁" => ambientDirectImage.{max a b} f
set_option hygiene false in
local notation "ΓX₀" => globalSections.{max a v s} R
set_option hygiene false in
local notation "ΓX₁" => globalSections.{max a b v s} R
set_option hygiene false in
local notation "ΓY₀" => globalSections.{max a u r} S
set_option hygiene false in
local notation "ΓY₁" => globalSections.{max a b u r} S
set_option hygiene false in
local notation "Res₀" => scalarRestriction.{a} f
set_option hygiene false in
local notation "Res₁" => scalarRestriction.{max a b} f
set_option hygiene false in
local notation "JX" => liftSheafCoefficients.{max b u v r s,u,r,max a u v r s} R
set_option hygiene false in
local notation "JY" => liftSheafCoefficients.{max b u v r s,v,s,max a u v r s} S
set_option hygiene false in
local notation "HX" => ModuleCat.uliftFunctor.{max b u v r s,max a u v r s} (R.obj.obj (op ⊤))
set_option hygiene false in
local notation "HY" => ModuleCat.uliftFunctor.{max b u v r s,max a u v r s} (S.obj.obj (op ⊤))

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a u v r s}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a u v r s}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a b u v r s}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a b u v r s}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a b u v r s}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a b u v r s}]
  [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives B₀] [EnoughInjectives B₁]
  [PreservesFiniteLimits JX] [PreservesFiniteColimits JX]
  [PreservesFiniteLimits JY] [PreservesFiniteColimits JY]

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport (coefficientEvaluationComparisonValue)
open Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
  (coefficientLiftComparisonValue)

private lemma coefficientLift_injective_flasque {Z : TopCat.{u}} (T : Z.Sheaf RingCat.{r})
    (M : AmbientSheaves.{a} T) (hM : Injective M) :
    IsFlasque T ((liftSheafCoefficients.{b,u,r,max a u r} T).obj M) :=
  (coefficient_lift_flasque.{b,u,r,max a u r} Z T M).mpr
    (original_injectives_flasque.{a,u,r} Z T M hM)

private def coefficientTransportData (c₀ : SectionsData.{a} f) (c₁ : SectionsData.{max a b} f) :
    CoefficientTransportData.{a,b} f c₀ c₁ where
  source := exactDescent JX
  target := exactDescent JY
  sourceModules := exactDescent HX
  targetModules := exactDescent HY
  sourceSections := derivedUnitTransport ΓX₀ ΓX₁ JX HX _ fun M hM ↦ by
    letI := original_sections_left_exact.{max a b v s,u,r} X R ⊤
    apply (AcyclicTermComparison.rightVanishing _ _ (ΓX₁) _).mpr
    exact SheafCohomologyOriginalCoefficients.flasque.{max a b v s,u,r} R ⊤ _
      (coefficientLift_injective_flasque.{max a v s,max b u v r s,u,r} R M hM)
  targetSections := derivedUnitTransport ΓY₀ ΓY₁ JY HY _ fun M hM ↦ by
    letI := original_sections_left_exact.{max a b u r,v,s} Y S ⊤
    apply (AcyclicTermComparison.rightVanishing _ _ (ΓY₁) _).mpr
    exact SheafCohomologyOriginalCoefficients.flasque.{max a b u r,v,s} S ⊤ _
      (coefficientLift_injective_flasque.{max a u r,max b u v r s,v,s} S M hM)
  pushforward := derivedUnitTransport D₀ D₁ JX JY _ fun M hM ↦ by
    letI := HigherDirectImagesIndependentCoefficients.leftExact.{max a b u v r s,u,v,r,s} f
    apply (AcyclicTermComparison.rightVanishing _ _ (D₁) _).mpr
    exact HigherDirectImagesIndependentCoefficients.flasqueHigherVanishing.{max a b,u,v,r,s}
      f _ (coefficientLift_injective_flasque.{max a v s,max b u v r s,u,r} R M hM)
  restriction := exactUnitTransport Res₀ Res₁ HX HY _ c₀.restriction c₁.restriction
    c₀.restriction_unit c₁.restriction_unit

variable {c₀ : SectionsData.{a} f} {c₁ : SectionsData.{max a b} f}

private def coefficientIteratedTransport (d : CoefficientTransportData.{a,b} f c₀ c₁) :
    UnitTransport (D₀ ⋙ ΓY₀) (D₁ ⋙ ΓY₁) JX HY
      (coefficientCompositeSquare.{b,max a u v r s} f) d.source d.targetModules
      (iteratedUnit D₀ ΓY₀) (iteratedUnit D₁ ΓY₁) :=
  composeUnitTransport d.pushforward d.targetSections

private def coefficientRestrictedTransport (d : CoefficientTransportData.{a,b} f c₀ c₁) :
    UnitTransport (D₀ ⋙ ΓY₀) (D₁ ⋙ ΓY₁) JX HY
      (coefficientCompositeSquare.{b,max a u v r s} f) d.source d.targetModules
      (sectionsTermwiseUnit.{a} f c₀.restriction) (sectionsTermwiseUnit.{max a b} f c₁.restriction) := by
  let t := composeUnitTransport d.sourceSections d.restriction
  refine ⟨d.restrictedIso f, fun I ↦ ?_⟩
  have h : coefficientRestrictedSquare.{b,max a u v r s} f =
      coefficientCompositeSquare.{b,max a u v r s} f := by
    apply Iso.ext
    ext M x
    rfl
  rw [sectionsTermwiseUnit_eq, sectionsTermwiseUnit_eq, ← h]
  exact t.on_complex I

private lemma coefficientModelCoherence (d : CoefficientTransportData.{a,b} f c₀ c₁)
    (h₀ : ∀ I, c₀.ModelEquation f I) (h₁ : ∀ I, c₁.ModelEquation f I) :
    d.ModelCoherence f := by
  intro I hI
  haveI := sectionsTermwiseUnit_isIso.{a} f c₀ I hI
  haveI : IsIso ((iteratedUnit D₀ ΓY₀).app I) := by
    rw [← (h₀ I).1]
    infer_instance
  exact ⟨h₀ I, h₁ ((JX).mapCochainComplexPlus.obj I),
    lifted_unit_isIso (coefficientRestrictedTransport f d) I,
    lifted_unit_isIso (coefficientIteratedTransport f d) I⟩

private lemma coefficientDerivedCoherence (d : CoefficientTransportData.{a,b} f c₀ c₁)
    (h₀ : ∀ I, c₀.ModelEquation f I) (h₁ : ∀ I, c₁.ModelEquation f I) :
    d.DerivedCoherence f :=
  transport_commutes (coefficientRestrictedTransport f d) (coefficientIteratedTransport f d)
    c₀.iteratedIso c₁.iteratedIso (fun I ↦ (h₀ I).1) (fun I ↦ (h₁ I).1)
    (sectionsTermwiseUnit_isIso.{a} f c₀)

private lemma coefficientCohomologyCoherence (d : CoefficientTransportData.{a,b} f c₀ c₁)
    (hd : d.DerivedCoherence f) : d.CohomologyCoherence f := by
  intro K n
  let F := DerivedCategory.Plus.homologyFunctor (SectionModules.{max a b u r} S (⊤ : Opens Y)) n
  have h := congrArg F.map (hd K)
  have hn := (d.targetModules.cohomology n).inv.naturality (c₀.iteratedIso.hom.app K)
  simp only [CategoryTheory.Functor.map_comp] at h
  simp only [CategoryTheory.Functor.comp_map] at hn
  simp only [SectionsData.cohomologyIso, CoefficientTransportData.iteratedCohomologyIso,
    CoefficientTransportData.restrictedCohomologyIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    CategoryTheory.Functor.map_comp, Category.assoc,
    Category.comp_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% hn]
  exact congrArg (fun k ↦ (HY).map ((c₀.restriction.cohomology n).inv.app
    ((ΓX₀).rightDerivedFunctorPlus.obj K)) ≫ (d.targetModules.cohomology n).inv.app _ ≫ k) h

end CoefficientTransport

attribute [local instance] HasDerivedCategory.standard in
theorem coefficientTransport : coefficientTransportType.{a,b,m,u,v,r,s} := by
  intro X Y R S f
  letI := sectionHasSheafify.{max a m v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a m v r s,u} X
  letI := sectionHasSheafify.{max a m u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a m u r s,v} Y
  letI := sectionHasSheafify.{max a b m v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a b m v r s,u} X
  letI := sectionHasSheafify.{max a b m u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a b m u r s,v} Y
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{max a m,u,v,r,s} f).1
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{max a m,u,v,r,s} f).2
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{max a b m,u,v,r,s} f).1
  letI := (HigherDirectImagesIndependentCoefficients.adequateEnoughInjectives.{max a b m,u,v,r,s} f).2
  have hX := coefficient_lift_ambient_sheaf_exact.{max b u v r s,u,r,max a m v s} X R
  have hY := coefficient_lift_ambient_sheaf_exact.{max b u v r s,v,s,max a m u r} Y S
  letI := hX.1
  letI := hX.2
  letI := hY.1
  letI := hY.2
  let c₀ := sectionsData.{max a m} f
  let c₁ := sectionsData.{max a b m} f
  let d := coefficientTransportData.{max a m,b} f c₀ c₁
  have h₀ := sectionsData_modelEquation.{max a m} f
  have h₁ := sectionsData_modelEquation.{max a b m} f
  have hc := coefficientDerivedCoherence f d h₀ h₁
  have hh := coefficientCohomologyCoherence f d hc
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hX.1, hX.2, hY.1, hY.2,
    c₀, c₁, d,
    fun I ↦ ⟨(coefficientRestrictedTransport f d).on_complex I,
      (coefficientIteratedTransport f d).on_complex I⟩,
    coefficientModelCoherence f d h₀ h₁, hc, hh, ?_, ?_, ?_⟩
  · intro K
    let P := ((coefficientLift.{a,m,u,v,r,s} f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj K
    let z := (d.originalPlacementIso.{a,b,m} f).hom.app K
    refine ⟨?_, fun n ↦ ?_⟩
    · simp only [SectionsData.onOriginalComplexes, isoWhiskerLeft_hom, whiskerLeft_app]
      rw [reassoc_of% (hc P)]
      exact congrArg ((d.restrictedIso f).hom.app P ≫ ·) (c₁.iteratedIso.hom.naturality z).symm
    · simp only [SectionsData.onOriginalCohomology, isoWhiskerLeft_hom, whiskerLeft_app]
      rw [reassoc_of% (hh P n)]
      exact congrArg ((d.restrictedCohomologyIso f n).hom.app P ≫ ·)
        ((c₁.cohomologyIso n).hom.naturality z).symm
  · letI := ambient_equivalence.{max a m v s,u,r} X R
    exact ⟨inferInstance, fun c' ↦
      ⟨siteTransportData.{max a m} f c₀ c', cohomologyCoherence.{max a m} f _ _ _⟩⟩
  · letI := ambient_equivalence.{max a b m v s,u,r} X R
    exact ⟨inferInstance, fun c' ↦
      ⟨siteTransportData.{max a b m} f c₁ c', cohomologyCoherence.{max a b m} f _ _ _⟩⟩

end AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
