import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafUniverseTransport
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Sites.CompatibleSheafification

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

universe a u r b

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

attribute [local instance] HasDerivedCategory.standard

theorem enoughInjectives : enoughInjectivesType.{a,u,r} := by
  intro X R
  exact ambient_enough_injectives.{a,u,r} X R

theorem openEnoughInjectives : openEnoughInjectivesType.{a,u,r} := by
  intro X R U
  exact ambient_enough_injectives.{a,u,r} (TopCat.of U) (U.sheafRestrict.obj R)

def cohomology : cohomologyType.{a,u,r} := @cohomologyValue.{a,u,r}

def system : systemType.{a,u,r} := @systemValue.{a,u,r}

def openSections : openSectionsType.{a,u,r} := @openSectionsValue.{a,u,r}

def sectionsRestriction : sectionsRestrictionType.{a,u,r} := @sectionsRestrictionValue.{a,u,r}

def openCohomology : openCohomologyType.{a,u,r} := @openCohomologyValue.{a,u,r}

theorem resolution : resolutionType.{a,u,r} := by
  intro X R U _ M I _ i hi hI n
  exact SheafCohomology.resolutionModelMap_isIso _ i hi
    (fun q ↦ (by haveI := hI q; exact AcyclicTermComparison.rightAcyclic_of_injective _ _)) n

theorem resolutionNaturality : resolutionNaturalityType.{a,u,r} := by
  intro X R U _ M N I J _ _ i hi j hj f g h n
  exact SheafCohomology.resolutionModelMap_naturality _ i hi j hj f g (congrArg _ h) n

theorem zero : zeroType.{a,u,r} := by
  intro X R U _
  letI := original_sections_left_exact.{a,u,r} X R U
  exact ClassicalDerivedValues.rightZero _ _ _

theorem longExact : longExactType.{a,u,r} := by
  intro X R U _
  letI := original_sections_left_exact.{a,u,r} X R U
  exact UniversalDeltaFunctors.rightDelta _ _ _

open private restrictionValueIso restrictionValueIso_zero restrictionValueIso_boundary
  restrictionValueIso_model from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology

set_option maxHeartbeats 1600000 in
theorem locality : localityType.{a,u,r} := by
  intro X R U _ _
  dsimp only
  letI := openModulesAbelian.{a} R U
  let J := originalRestriction.{a} R U
  let Γ := sectionsValue.{a} R U
  let ΓU := openSectionsValue.{a} R U
  let c := sectionsRestrictionValue.{a} R U
  have h := original_restriction_exact.{a,u,r} X R U
  letI := h.1
  letI := h.2
  have hJ : ∀ M, Injective M → Injective (J.obj M) := by
    obtain ⟨_, _, _, _, hJ⟩ := original_open_extension.{a,u,r} X R U
    exact hJ
  refine ⟨restrictionValueIso J ΓU Γ c hJ, restrictionValueIso_zero J ΓU Γ c hJ, ?_, ?_⟩
  · intro S hS
    exact ⟨hS.map_of_exact J, restrictionValueIso_boundary J ΓU Γ c hJ S hS⟩
  · intro M I _ i hi hI
    letI := hi
    letI := HomologicalComplex.quasiIso_map_of_preservesHomology i J
    have hJi : QuasiIso (mapAugmentation J i) := by
      unfold mapAugmentation
      exact quasiIso_comp _ _
    refine ⟨hJi, fun q ↦ hJ _ (hI q), ?_⟩
    intro n
    exact restrictionValueIso_model J ΓU Γ c hJ i hi hJi n


section ModelComparison

open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [EnoughInjectives A] [EnoughInjectives A']
  (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
  [F.Additive] [G.Additive] [J.Additive] [H.Additive]
  [J.PreservesHomology] [H.PreservesHomology]
  (c : F ⋙ H ≅ J ⋙ G)

omit [EnoughInjectives A] [EnoughInjectives A'] in
private theorem mapAugmentation_quasiIso
    {M : A} {I : CochainComplex A ℤ}
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i) :
    QuasiIso (mapAugmentation J i) := by
  letI := hi
  letI := HomologicalComplex.quasiIso_map_of_preservesHomology i J
  unfold mapAugmentation
  infer_instance

omit [EnoughInjectives A] [EnoughInjectives A'] in
private theorem mapAugmentation_naturality {M N : A} {I K : CochainComplex A ℤ}
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I)
    (k : (CochainComplex.singleFunctor A 0).obj N ⟶ K)
    (f : M ⟶ N) (g : I ⟶ K)
    (h : i ≫ g = (CochainComplex.singleFunctor A 0).map f ≫ k) :
    mapAugmentation J i ≫ (J.mapHomologicalComplex (.up ℤ)).map g =
      (CochainComplex.singleFunctor A' 0).map (J.map f) ≫ mapAugmentation J k := by
  unfold mapAugmentation
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ (J.mapHomologicalComplex (.up ℤ)).map k)
    ((J.mapCochainComplexSingleFunctor 0).inv.naturality f).symm |>.trans
      (Category.assoc _ _ _)

private theorem modelComparison_naturality {I K : CochainComplex A ℤ} (g : I ⟶ K) (n : ℕ) :
    H.map (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)) ≫
        (modelComparison F G J H c K n).hom =
      (modelComparison F G J H c I n).hom ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (.up ℤ)).map
            ((J.mapHomologicalComplex (.up ℤ)).map g)) (n : ℤ) := by
  let Q := HomologicalComplex.homologyFunctor B' (.up ℤ) (n : ℤ)
  let f := (F.mapHomologicalComplex (.up ℤ)).map g
  let h := (H.mapHomologicalComplex (.up ℤ)).map f
  let j := (G.mapHomologicalComplex (.up ℤ)).map
    ((J.mapHomologicalComplex (.up ℤ)).map g)
  let t := NatIso.mapHomologicalComplex c (.up ℤ)
  let e (L : CochainComplex A ℤ) :=
    ((((F.mapHomologicalComplex (.up ℤ)).obj L).sc (n : ℤ)).mapHomologyIso H).inv
  have h₁ : H.map (HomologicalComplex.homologyMap f (n : ℤ)) ≫ e K =
      e I ≫ Q.map h :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ (n : ℤ)).map f) H
  have h₂ : Q.map h ≫ Q.map (t.hom.app K) = Q.map (t.hom.app I) ≫ Q.map j := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact congrArg Q.map (t.hom.naturality g)
  change _ ≫ (e K ≫ Q.map (t.hom.app K)) = (e I ≫ Q.map (t.hom.app I)) ≫ Q.map j
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Compare two systems of derived values through all source injective
resolutions, using acyclicity of their image terms under the second functor. -/
theorem compareResolutions
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M)) :
    ResolutionComparison F G J H c := by
  let S := CochainComplex.singleFunctor A 0
  choose K k hkmono hkq hkI hkbound using fun M : A ↦
    InjectiveComplexReplacement.replacement _ (S.obj M) 0 inferInstance
  letI (M : A) : (K M).IsStrictlyGE 0 := hkbound M
  let T (n : ℕ) := rightValue F n ⋙ H
  let T' (n : ℕ) := J ⋙ rightValue G n
  let a {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
      (i : S.obj M ⟶ I) (hi : QuasiIso i) (n : ℕ) :=
    H.map (resolutionModelMap F i hi n)
  let b {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
      (i : S.obj M ⟶ I) (hi : QuasiIso i) (n : ℕ) :=
    resolutionModelMap G (mapAugmentation J i) (mapAugmentation_quasiIso J i hi) n
  have ha {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
      (i : S.obj M ⟶ I) (hi : QuasiIso i) (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
      IsIso (a i hi n) := by
    letI := SheafCohomology.resolutionModelMap_isIso F i hi
      (fun q ↦ by letI := hI q; exact AcyclicTermComparison.rightAcyclic_of_injective F _) n
    dsimp [a]
    infer_instance
  have hb {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
      (i : S.obj M ⟶ I) (hi : QuasiIso i) (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
      IsIso (b i hi n) :=
    SheafCohomology.resolutionModelMap_isIso G _ _ (fun q ↦ hJ _ (hI q)) n
  let app (M : A) (n : ℕ) : (T n).obj M ≅ (T' n).obj M := by
    letI := ha (k M) (hkq M) (hkI M) n
    letI := hb (k M) (hkq M) (hkI M) n
    exact (asIso (a (k M) (hkq M) n)).symm ≪≫
      modelComparison F G J H c (K M) n ≪≫ asIso (b (k M) (hkq M) n)
  have modelSquare (n : ℕ) (M : A) :
      a (k M) (hkq M) n ≫ (app M n).hom =
        (modelComparison F G J H c (K M) n).hom ≫ b (k M) (hkq M) n := by
    letI := ha (k M) (hkq M) (hkI M) n
    letI := hb (k M) (hkq M) (hkI M) n
    exact (asIso (a (k M) (hkq M) n)).hom_inv_id_assoc _
  have modelNat (n : ℕ) {M N : A} (f : M ⟶ N)
      {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
      (i : S.obj N ⟶ I) (hi : QuasiIso i) (hI : ∀ q, Injective (I.X q)) :
      ∃ g : K M ⟶ I,
        a (k M) (hkq M) n ≫ (T n).map f =
          H.map (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g)
            (n : ℤ)) ≫ a i hi n ∧
        b (k M) (hkq M) n ≫ (T' n).map f =
          HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map
            ((J.mapHomologicalComplex (.up ℤ)).map g)) (n : ℤ) ≫ b i hi n := by
    letI : Mono (k M) := HomologicalComplex.mono_of_mono_f _ (hkmono M)
    letI : QuasiIso (k M) := hkq M
    obtain ⟨g, hg⟩ := SheafCohomology.injectiveResolutionLift (k M) (S.map f ≫ i) hI
    refine ⟨g, ?_, ?_⟩
    · change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
      rw [← H.map_comp, ← H.map_comp]
      exact congrArg H.map (SheafCohomology.resolutionModelMap_naturality F _ _ _ _ f g
        (congrArg DerivedCategory.Q.map hg) n)
    · exact SheafCohomology.resolutionModelMap_naturality G _ _ _ _ (J.map f) _
        (congrArg DerivedCategory.Q.map (mapAugmentation_naturality J _ _ f g hg)) n
  let e (n : ℕ) : T n ≅ T' n := NatIso.ofComponents (fun M ↦ app M n) (by
    intro M N f
    obtain ⟨g, hg, hJg⟩ := modelNat n f (k N) (hkq N) (hkI N)
    letI := ha (k M) (hkq M) (hkI M) n
    apply (cancel_epi (a (k M) (hkq M) n)).mp
    rw [← Category.assoc, hg, Category.assoc, modelSquare, ← Category.assoc,
      modelComparison_naturality, Category.assoc, ← hJg,
      ← Category.assoc, ← modelSquare, Category.assoc])
  refine ⟨e, fun M I _ i hi hI ↦ ⟨mapAugmentation_quasiIso J i hi, ?_⟩⟩
  intro n
  change a i hi n ≫ (app M n).hom = (modelComparison F G J H c I n).hom ≫ b i hi n
  obtain ⟨g, hg, hJg⟩ := modelNat n (𝟙 M) i hi hI
  dsimp only [T, T', Functor.comp_map] at hg hJg
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hg hJg
  letI := ha (k M) (hkq M) (hkI M) n
  letI := ha i hi hI n
  letI := IsIso.of_isIso_fac_right hg.symm
  apply (cancel_epi (H.map (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)))).mp
  rw [← Category.assoc, ← hg, modelSquare, ← Category.assoc,
    modelComparison_naturality, Category.assoc, ← hJg]


/-- An augmented injective model determines the comparison at its coefficient. -/
theorem resolutionComparison_unique
    {e e' : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n}
    (he : IsResolutionComparison F G J H c e)
    (he' : IsResolutionComparison F G J H c e') : e = e' := by
  funext n
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let S := (CochainComplex.singleFunctor A 0).obj M
  obtain ⟨I, i, _, hi, hI, hge⟩ :=
    InjectiveComplexReplacement.replacement _ S 0 (by dsimp [S]; infer_instance)
  letI := hge
  obtain ⟨hJi, h⟩ := he M I i hi hI
  obtain ⟨hJi', h'⟩ := he' M I i hi hI
  letI := SheafCohomology.resolutionModelMap_isIso F i hi
    (fun q ↦ by letI := hI q; exact AcyclicTermComparison.rightAcyclic_of_injective F _) n
  apply (cancel_epi (H.map (resolutionModelMap F i hi n))).mp
  exact (h n).trans (h' n).symm

end ModelComparison

open private exactDerivedPlus exactDerivedPlusFactors exactDerivedPlusSingle
  exactDerivedPlus_map_augmentation exactDerivedPlusCompιIso
  mapPlusTriangleIso mapPlusTriangleIso_hom₁ mapPlusTriangleIso_hom₃
  mapPlusCompIso restrictionDerivedUnit unit_isIso_of_injective
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology


section ExactComparison

open CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
set_option maxHeartbeats 1000000

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [EnoughInjectives A] [EnoughInjectives A']
  (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
  [F.Additive] [G.Additive] [J.Additive] [H.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (c : F ⋙ H ≅ J ⋙ G)

private def cochainExactHomologyIso (n : ℤ) :
    HomologicalComplex.homologyFunctor B (.up ℤ) n ⋙ H ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B' (.up ℤ) n :=
  NatIso.ofComponents (fun K => ((K.sc n).mapHomologyIso H).symm)
    (fun {_ _} f => ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ n).map f) H)

private def fullExactHomologyFactors (n : ℤ) :
    DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor B n ⋙ H) ≅
      DerivedCategory.Q ⋙ (H.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B' n) :=
  (associator ..).symm ≪≫ isoWhiskerRight (DerivedCategory.homologyFunctorFactors B n) H ≪≫
    cochainExactHomologyIso H n ≪≫
    isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors B' n).symm ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight H.mapDerivedCategoryFactors.symm _ ≪≫
    (associator ..)

private def fullExactHomologyIso (n : ℤ) :
    DerivedCategory.homologyFunctor B n ⋙ H ≅
      H.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B' n := by
  exact (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := B)) (HomologicalComplex.quasiIso B (.up ℤ)) B').preimageIso
      (fullExactHomologyFactors H n)

private lemma fullExactHomologyIso_app (K : CochainComplex B ℤ) (n : ℤ) :
    (fullExactHomologyIso H n).hom.app (DerivedCategory.Q.obj K) =
      H.map ((DerivedCategory.homologyFunctorFactors B n).hom.app K) ≫
        ((K.sc n).mapHomologyIso H).inv ≫
        (DerivedCategory.homologyFunctorFactors B' n).inv.app
          ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (DerivedCategory.homologyFunctor B' n).map (H.mapDerivedCategoryFactors.inv.app K) := by
  have eq := (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := B)) (HomologicalComplex.quasiIso B (.up ℤ)) B').map_preimage
      (fullExactHomologyFactors H n).hom
  simpa [fullExactHomologyIso, fullExactHomologyFactors, cochainExactHomologyIso] using
    NatTrans.congr_app eq K

private def exactHomologyIso (n : ℤ) :
    DerivedCategory.Plus.homologyFunctor B n ⋙ H ≅
      exactDerivedPlus H ⋙ DerivedCategory.Plus.homologyFunctor B' n :=
  (associator ..) ≪≫ isoWhiskerLeft _ (fullExactHomologyIso H n) ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (exactDerivedPlusCompιIso H).symm _ ≪≫
    (associator ..)

private lemma cochainExactHomology_shiftIso
    (m n n' : ℤ) (hn : m + n = n') (K : CochainComplex B ℤ) :
    (cochainExactHomologyIso H n).hom.app (K⟦m⟧) ≫
        (HomologicalComplex.homologyFunctor B' (.up ℤ) n).map
          (((H.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app K) ≫
        (CochainComplex.ShiftSequence.shiftIso B' m n n' hn).hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      H.map ((CochainComplex.ShiftSequence.shiftIso B m n n' hn).hom.app K) ≫
        (cochainExactHomologyIso H n').hom.app K := by
  let q := CochainComplex.shiftShortComplexFunctorIso B m n n' hn
  let q' := CochainComplex.shiftShortComplexFunctorIso B' m n n' hn
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let Sh := HomologicalComplex.shortComplexFunctor B' (.up ℤ) n
  have e : Sh.map ((Hc.commShiftIso m).hom.app K) ≫ q'.hom.app (Hc.obj K) =
      (H.mapShortComplex).map (q.hom.app K) := by
    ext <;> simp [q, q', Hc, Sh, CochainComplex.shiftShortComplexFunctorIso, HomologicalComplex.XIsoOfEq,
      eqToIso, eqToHom_map]
  have eq := ShortComplex.mapHomologyIso_inv_naturality (q.hom.app K) H
  simp only [CochainComplex.ShiftSequence.shiftIso_hom_app]
  change (((K⟦m⟧).sc n).mapHomologyIso H).inv ≫
    ShortComplex.homologyMap (Sh.map ((Hc.commShiftIso m).hom.app K)) ≫
    ShortComplex.homologyMap (q'.hom.app (Hc.obj K)) = _
  rw [← ShortComplex.homologyMap_comp, e]
  exact eq.symm

private lemma cochainExactHomology_shiftMap
    {K L : CochainComplex B ℤ} {m n n' : ℤ} (hn : m + n = n')
    (f : ShiftedHom K L m) :
    (cochainExactHomologyIso H n).hom.app K ≫
        (HomologicalComplex.homologyFunctor B' (.up ℤ) 0).shiftMap
          (f.map (H.mapHomologicalComplex (.up ℤ))) n n' hn =
      H.map ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftMap f n n' hn) ≫
        (cochainExactHomologyIso H n').hom.app L := by
  let Cn := HomologicalComplex.homologyFunctor B (.up ℤ) n
  let Cn' := HomologicalComplex.homologyFunctor B' (.up ℤ) n
  let Hc := H.mapHomologicalComplex (.up ℤ)
  have hh : (cochainExactHomologyIso H n).hom.app K ≫ Cn'.map (Hc.map f) =
      H.map (Cn.map f) ≫ (cochainExactHomologyIso H n).hom.app (L⟦m⟧) :=
    ((cochainExactHomologyIso H n).hom.naturality f).symm
  change (cochainExactHomologyIso H n).hom.app K ≫
      Cn'.map (Hc.map f ≫ (Hc.commShiftIso m).hom.app L) ≫
      (CochainComplex.ShiftSequence.shiftIso B' m n n' hn).hom.app (Hc.obj L) =
    H.map (Cn.map f ≫ (CochainComplex.ShiftSequence.shiftIso B m n n' hn).hom.app L) ≫
      (cochainExactHomologyIso H n').hom.app L
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% hh]
  exact congrArg (H.map (Cn.map f) ≫ ·) (cochainExactHomology_shiftIso H m n n' hn L)

private lemma shiftMap_commShift_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [τ.CommShift ℤ]
    (V : D ⥤ E) [V.ShiftSequence ℤ] {X Y : C} {m n n' : ℤ} (hn : m + n = n')
    (f : ShiftedHom X Y m) :
    (V.shift n).map (τ.app X) ≫ V.shiftMap (f.map G) n n' hn =
      V.shiftMap (f.map F) n n' hn ≫ (V.shift n').map (τ.app Y) := by
  have h := ShiftedHom.map_naturality (a := m) f τ
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  have eq := congrArg (fun g : ShiftedHom (F.obj X) (G.obj Y) m => V.shiftMap g n n' hn) h
  have h₁ := V.shiftMap_comp (f.map F) (τ.app Y) n n' hn
  have h₂ := V.shiftMap_comp' (τ.app X) (f.map G) n n' hn
  exact h₂.symm.trans (eq.symm.trans h₁)

private lemma fullExactHomology_shiftMap_Q
    {K L : CochainComplex B ℤ} {m n n' : ℤ} (hn : m + n = n')
    (f : ShiftedHom K L m) :
    (fullExactHomologyIso H n).hom.app (DerivedCategory.Q.obj K) ≫
        (DerivedCategory.homologyFunctor B' 0).shiftMap
          ((f.map DerivedCategory.Q).map H.mapDerivedCategory) n n' hn =
      H.map ((DerivedCategory.homologyFunctor B 0).shiftMap
        (f.map DerivedCategory.Q) n n' hn) ≫
        (fullExactHomologyIso H n').hom.app (DerivedCategory.Q.obj L) := by
  let ψ := H.mapDerivedCategoryFactors
  haveI : ψ.inv.CommShift ℤ := NatTrans.CommShift.of_iso_inv ψ ℤ
  have h := shiftMap_commShift_naturality ψ.inv (DerivedCategory.homologyFunctor B' 0) hn f
  simp only [ShiftedHom.comp_map, DerivedCategory.shift_homologyFunctor, ψ] at h
  simp only [fullExactHomologyIso_app, Category.assoc]
  rw [h]
  rw [DerivedCategory.shiftMap_homologyFunctor_map_Q _ n n' hn,
    DerivedCategory.shiftMap_homologyFunctor_map_Q _ n n' hn]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [← H.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [H.map_comp, Category.assoc]
  have eq := cochainExactHomology_shiftMap H hn f
  simp only [cochainExactHomologyIso, Iso.symm_hom, NatIso.ofComponents_hom_app] at eq
  simp only [reassoc_of% eq]
  erw [H.map_id, Category.id_comp]

private lemma shiftMap_exact_naturality
    {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
    [HasShift C ℤ] [HasShift C' ℤ]
    (E : C ⥤ C') [E.CommShift ℤ] (L : C ⥤ D) [L.ShiftSequence ℤ]
    (L' : C' ⥤ D') [L'.ShiftSequence ℤ] (H : D ⥤ D')
    (e : ∀ n : ℤ, L.shift n ⋙ H ≅ E ⋙ L'.shift n)
    {m n n' : ℤ} (hn : m + n = n')
    (h : ∀ Y : C,
      (e n).hom.app (Y⟦m⟧) ≫
        (L'.shift n).map ((E.commShiftIso m).hom.app Y) ≫
        (L'.shiftIso m n n' hn).hom.app (E.obj Y) =
      H.map ((L.shiftIso m n n' hn).hom.app Y) ≫ (e n').hom.app Y)
    {X Y : C} (f : ShiftedHom X Y m) :
    (e n).hom.app X ≫ L'.shiftMap (f.map E) n n' hn =
      H.map (L.shiftMap f n n' hn) ≫ (e n').hom.app Y := by
  have hh : (e n).hom.app X ≫ (L'.shift n).map (E.map f) =
      H.map ((L.shift n).map f) ≫ (e n).hom.app (Y⟦m⟧) :=
    ((e n).hom.naturality f).symm
  simp only [Functor.shiftMap, ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% hh, h Y]

private lemma fullExactHomology_shiftMap
    {K L : DerivedCategory B} {m n n' : ℤ} (hn : m + n = n')
    (f : ShiftedHom K L m) :
    (fullExactHomologyIso H n).hom.app K ≫
        (DerivedCategory.homologyFunctor B' 0).shiftMap
          (f.map H.mapDerivedCategory) n n' hn =
      H.map ((DerivedCategory.homologyFunctor B 0).shiftMap f n n' hn) ≫
        (fullExactHomologyIso H n').hom.app L := by
  refine shiftMap_exact_naturality H.mapDerivedCategory
    (DerivedCategory.homologyFunctor B 0) (DerivedCategory.homologyFunctor B' 0) H
    (fullExactHomologyIso H) hn ?_ f
  intro Y
  let Q := DerivedCategory.Q (C := B)
  obtain ⟨Y₀, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Q Y
  have h := fullExactHomology_shiftMap_Q H hn (𝟙 (Y₀⟦m⟧))
  let E := H.mapDerivedCategory
  let L₀ := DerivedCategory.homologyFunctor B 0
  let L₁ := DerivedCategory.homologyFunctor B' 0
  let Cn := DerivedCategory.homologyFunctor B n
  let Cn' := DerivedCategory.homologyFunctor B' n
  let q := (Q.commShiftIso m).hom.app Y₀
  let e' := (shiftFunctor _ m).map e.hom
  let σ := (L₀.shiftIso m n n' hn).hom
  let σ' := (L₁.shiftIso m n n' hn).hom
  have h₀ : (fullExactHomologyIso H n).hom.app (Q.obj (Y₀⟦m⟧)) ≫
      Cn'.map (E.map q) ≫ Cn'.map ((E.commShiftIso m).hom.app (Q.obj Y₀)) ≫
      σ'.app (E.obj (Q.obj Y₀)) =
      H.map (Cn.map q) ≫ H.map (σ.app (Q.obj Y₀)) ≫
        (fullExactHomologyIso H n').hom.app (Q.obj Y₀) := by
    have hqmap : ShiftedHom.map (a := m) (𝟙 (Y₀⟦m⟧)) Q = q := by
      change Q.map (𝟙 _) ≫ q = q
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    change _ ≫ (DerivedCategory.homologyFunctor B' 0).shiftMap
      ((ShiftedHom.map (a := m) (𝟙 (Y₀⟦m⟧)) Q).map E) n n' hn =
        H.map ((DerivedCategory.homologyFunctor B 0).shiftMap
          (ShiftedHom.map (a := m) (𝟙 (Y₀⟦m⟧)) Q) n n' hn) ≫ _ at h
    rw [hqmap] at h
    simp only [Functor.shiftMap, ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc] at h
    exact h
  have hq : H.map (Cn.map q) ≫ (fullExactHomologyIso H n).hom.app ((Q.obj Y₀)⟦m⟧) =
      (fullExactHomologyIso H n).hom.app (Q.obj (Y₀⟦m⟧)) ≫ Cn'.map (E.map q) :=
    (fullExactHomologyIso H n).hom.naturality q
  have hY₀ : (fullExactHomologyIso H n).hom.app ((Q.obj Y₀)⟦m⟧) ≫
      Cn'.map ((E.commShiftIso m).hom.app (Q.obj Y₀)) ≫
      σ'.app (E.obj (Q.obj Y₀)) =
      H.map (σ.app (Q.obj Y₀)) ≫ (fullExactHomologyIso H n').hom.app (Q.obj Y₀) := by
    apply (cancel_epi (H.map (Cn.map q))).mp
    simpa only [reassoc_of% hq, Category.assoc] using h₀
  have h₁ : H.map (Cn.map e') ≫ (fullExactHomologyIso H n).hom.app (Y⟦m⟧) =
      (fullExactHomologyIso H n).hom.app ((Q.obj Y₀)⟦m⟧) ≫ Cn'.map (E.map e') :=
    (fullExactHomologyIso H n).hom.naturality e'
  have h₂ : Cn'.map (E.map e') ≫ Cn'.map ((E.commShiftIso m).hom.app Y) =
      Cn'.map ((E.commShiftIso m).hom.app (Q.obj Y₀)) ≫
      Cn'.map ((shiftFunctor _ m).map (E.map e.hom)) := by
    simp only [← Cn'.map_comp]
    exact congrArg Cn'.map ((E.commShiftIso m).hom.naturality e.hom)
  have h₃ : Cn'.map ((shiftFunctor _ m).map (E.map e.hom)) ≫ σ'.app (E.obj Y) =
      σ'.app (E.obj (Q.obj Y₀)) ≫ (DerivedCategory.homologyFunctor B' n').map (E.map e.hom) :=
    σ'.naturality (E.map e.hom)
  have h₄ : H.map (Cn.map e') ≫ H.map (σ.app Y) =
      H.map (σ.app (Q.obj Y₀)) ≫ H.map ((DerivedCategory.homologyFunctor B n').map e.hom) := by
    simp only [← H.map_comp]
    exact congrArg H.map (σ.naturality e.hom)
  have h₅ : H.map ((DerivedCategory.homologyFunctor B n').map e.hom) ≫
      (fullExactHomologyIso H n').hom.app Y =
      (fullExactHomologyIso H n').hom.app (Q.obj Y₀) ≫
        (DerivedCategory.homologyFunctor B' n').map (E.map e.hom) :=
    (fullExactHomologyIso H n').hom.naturality e.hom
  change (fullExactHomologyIso H n).hom.app (Y⟦m⟧) ≫
      Cn'.map ((E.commShiftIso m).hom.app Y) ≫ σ'.app (E.obj Y) =
      H.map (σ.app Y) ≫ (fullExactHomologyIso H n').hom.app Y
  apply (cancel_epi (H.map (Cn.map e'))).mp
  simp only [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₄, h₅]
  rw [h₃, ← Category.assoc _ (σ'.app _), ← Category.assoc, hY₀, Category.assoc]

private lemma plusHomology_shiftMap
    {C : Type*} [Category* C] [Abelian C]
    {K L : DerivedCategory.Plus C} {m n n' : ℤ} (hn : m + n = n')
    (f : ShiftedHom K L m) :
    (DerivedCategory.Plus.homologyFunctor C 0).shiftMap f n n' hn =
      (DerivedCategory.homologyFunctor C 0).shiftMap (f.map DerivedCategory.Plus.ι) n n' hn := by
  simp [DerivedCategory.Plus.homologyFunctor, Functor.shiftMap, ShiftedHom.map,
    Functor.shiftIso, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [Category.id_comp]
  rfl

private lemma exactHomologyIso_hom_app (K : DerivedCategory.Plus B) (n : ℤ) :
    (exactHomologyIso H n).hom.app K =
      (fullExactHomologyIso H n).hom.app (DerivedCategory.Plus.ι.obj K) ≫
        (DerivedCategory.homologyFunctor B' n).map ((exactDerivedPlusCompιIso H).inv.app K) := by
  simp [exactHomologyIso]
  apply Category.id_comp

private lemma exactHomology_shiftMap
    {K L : DerivedCategory.Plus B} {m n n' : ℤ} (hn : m + n = n')
    (f : ShiftedHom K L m) :
    (exactHomologyIso H n).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor B' 0).shiftMap
          (f.map (exactDerivedPlus H)) n n' hn =
      H.map ((DerivedCategory.Plus.homologyFunctor B 0).shiftMap f n n' hn) ≫
        (exactHomologyIso H n').hom.app L := by
  let q := exactDerivedPlusCompιIso H
  haveI : q.inv.CommShift ℤ := NatTrans.CommShift.of_iso_inv q ℤ
  have eq := shiftMap_commShift_naturality q.inv (DerivedCategory.homologyFunctor B' 0) hn f
  simp only [ShiftedHom.comp_map, DerivedCategory.shift_homologyFunctor, q] at eq
  rw [exactHomologyIso_hom_app, exactHomologyIso_hom_app, plusHomology_shiftMap,
    plusHomology_shiftMap, Category.assoc]
  erw [eq, ← Category.assoc, fullExactHomology_shiftMap H hn (f.map DerivedCategory.Plus.ι)]
  exact Category.assoc _ _ _

private lemma exactHomologyIso_app (K : CochainComplex.Plus B) (n : ℤ) :
    (exactHomologyIso H n).hom.app (DerivedCategory.Plus.Q.obj K) =
      H.map ((DerivedCategory.homologyFunctorFactors B n).hom.app K.obj) ≫
        ((K.obj.sc n).mapHomologyIso H).inv ≫
        (DerivedCategory.homologyFunctorFactors B' n).inv.app
          ((H.mapHomologicalComplex (.up ℤ)).obj K.obj) ≫
        (DerivedCategory.Plus.homologyFunctor B' n).map ((exactDerivedPlusFactors H).inv.app K) := by
  rw [exactHomologyIso_hom_app]
  have hι : (exactDerivedPlusCompιIso H).inv.app (DerivedCategory.Plus.Q.obj K) = 𝟙 _ := rfl
  erw [hι, CategoryTheory.Functor.map_id, Category.comp_id]
  exact fullExactHomologyIso_app H K.obj n

private def exactComparisonComplexIso :
    F.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus ≅
      J.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus :=
  mapPlusCompIso F H (J ⋙ G) c ≪≫ (mapPlusCompIso J G (J ⋙ G) (Iso.refl _)).symm

private instance : (exactComparisonComplexIso F G J H c).hom.CommShift ℤ := by
  dsimp only [exactComparisonComplexIso, Iso.trans_hom, Iso.symm_hom]
  haveI := NatTrans.CommShift.of_iso_inv (mapPlusCompIso J G (J ⋙ G) (Iso.refl _)) ℤ
  infer_instance

private def postExactUnit :
    (F.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus) ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ⋙ exactDerivedPlus H :=
  (associator ..).hom ≫ whiskerLeft _ (exactDerivedPlusFactors H).inv ≫
    (associator ..).inv ≫ whiskerRight F.rightDerivedFunctorPlusUnit _ ≫ (associator ..).hom

private instance : (postExactUnit F H).CommShift ℤ := by
  dsimp only [postExactUnit]
  haveI := NatTrans.CommShift.of_iso_inv (exactDerivedPlusFactors H) ℤ
  infer_instance

private def preExactUnit :
    (F.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus) ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ exactDerivedPlus J ⋙ G.rightDerivedFunctorPlus :=
  whiskerRight (exactComparisonComplexIso F G J H c).hom _ ≫ (associator ..).hom ≫
    restrictionDerivedUnit J G

private instance : (preExactUnit F G J H c).CommShift ℤ := by
  dsimp only [preExactUnit]
  infer_instance

private lemma exactCompositeDerives :
    (CochainComplex.Plus.localizerMorphism A).Derives
      ((F.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus) ⋙ DerivedCategory.Plus.Q) := by
  intro K L f hf
  simp only [Functor.comp_map]
  rw [HomotopyCategory.Plus.inverseImage_quasiIso_mapCochainComplexPlus_injectiveObjectι] at hf
  dsimp
  apply Localization.inverts _ (CochainComplex.Plus.quasiIso B')
  exact homotopyEquivalences_le_quasiIso _ _ _
    (H.homotopyEquivalences_mapCochainComplexPlus_map _
      (F.homotopyEquivalences_mapCochainComplexPlus_map _
        ((InjectiveObject.ι A).homotopyEquivalences_mapCochainComplexPlus_map _ hf)))

private lemma postExactUnit_isDerived :
    (F.rightDerivedFunctorPlus ⋙ exactDerivedPlus H).IsRightDerivedFunctor
      (postExactUnit F H) (CochainComplex.Plus.quasiIso A) := by
  refine (exactCompositeDerives F H).isRightDerivedFunctor_of_isIso _ (fun K => ?_)
  dsimp [postExactUnit]
  haveI := unit_isIso_of_injective F
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj K) fun i => (K.obj.X i).property
  infer_instance

private lemma preExactUnit_isDerived
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M)) :
    (exactDerivedPlus J ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (preExactUnit F G J H c) (CochainComplex.Plus.quasiIso A) := by
  refine (exactCompositeDerives F H).isRightDerivedFunctor_of_isIso _ (fun K => ?_)
  let L := J.mapCochainComplexPlus.obj ((InjectiveObject.ι A).mapCochainComplexPlus.obj K)
  haveI : IsIso (G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A').obj L)) :=
    AcyclicTermComparison.rightComparison_homotopy G _ fun i => hJ _ (K.obj.X i).property
  haveI : IsIso (G.rightDerivedFunctorPlusUnit.app L) := by
    simp only [Functor.rightDerivedFunctorPlusUnit_app]
    infer_instance
  dsimp [preExactUnit, restrictionDerivedUnit]
  infer_instance

private def exactDerivedComparison
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M)) :
    F.rightDerivedFunctorPlus ⋙ exactDerivedPlus H ≅
      exactDerivedPlus J ⋙ G.rightDerivedFunctorPlus := by
  letI := postExactUnit_isDerived F H
  letI := preExactUnit_isDerived F G J H c hJ
  exact rightDerivedUnique _ _ (postExactUnit F H) (preExactUnit F G J H c)
    (CochainComplex.Plus.quasiIso A)

private instance (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M)) :
    (exactDerivedComparison F G J H c hJ).hom.CommShift ℤ := by
  letI := postExactUnit_isDerived F H
  letI := preExactUnit_isDerived F G J H c hJ
  refine NatTrans.CommShift.of_isRightDerivedFunctor
    (postExactUnit F H) (preExactUnit F G J H c)
    (𝟙 _) (CochainComplex.Plus.quasiIso A) ?_
  simp [exactDerivedComparison, Functor.rightDerivedUnique]

private lemma exactDerivedComparison_unit
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M))
    (K : CochainComplex.Plus A) :
    (postExactUnit F H).app K ≫
      (exactDerivedComparison F G J H c hJ).hom.app (DerivedCategory.Plus.Q.obj K) =
    (preExactUnit F G J H c).app K := by
  letI := postExactUnit_isDerived F H
  letI := preExactUnit_isDerived F G J H c hJ
  simp [exactDerivedComparison, Functor.rightDerivedUnique]

private def exactComparisonIso
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M)) (n : ℕ) :
    rightValue F n ⋙ H ≅ J ⋙ rightValue G n := by
  let S := DerivedCategory.Plus.singleFunctor A 0
  let S' := DerivedCategory.Plus.singleFunctor A' 0
  let RF := F.rightDerivedFunctorPlus
  let RG := G.rightDerivedFunctorPlus
  let HH := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let HH' := DerivedCategory.Plus.homologyFunctor B' (n : ℤ)
  exact associator (S ⋙ RF) HH H ≪≫
    isoWhiskerLeft (S ⋙ RF) (exactHomologyIso H (n : ℤ)) ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (associator S RF (exactDerivedPlus H)) HH' ≪≫
    isoWhiskerRight (isoWhiskerLeft S (exactDerivedComparison F G J H c hJ)) HH' ≪≫
    isoWhiskerRight (associator S (exactDerivedPlus J) RG).symm HH' ≪≫
    isoWhiskerRight (isoWhiskerRight (exactDerivedPlusSingle J) RG) HH' ≪≫
    isoWhiskerRight (associator J S' RG) HH' ≪≫ associator J _ HH'

private lemma exactComparisonIso_hom_app
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M)) (n : ℕ) (M : A) :
    (exactComparisonIso F G J H c hJ n).hom.app M =
      (exactHomologyIso H (n : ℤ)).hom.app
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≫
      (DerivedCategory.Plus.homologyFunctor B' (n : ℤ)).map
        ((exactDerivedComparison F G J H c hJ).hom.app ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫
          G.rightDerivedFunctorPlus.map ((exactDerivedPlusSingle J).hom.app M)) := by
  simp [exactComparisonIso, CategoryTheory.Functor.map_comp]
  apply Category.id_comp

private lemma exactComparison_model
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M))
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i)
    (hJi : QuasiIso (mapAugmentation J i)) (n : ℕ) :
    H.map (resolutionModelMap F i hi n) ≫ (exactComparisonIso F G J H c hJ n).hom.app M =
      (modelComparison F G J H c I n).hom ≫
        resolutionModelMap G (mapAugmentation J i) hJi n := by
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let L : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let q : L ⟶ K := ObjectProperty.homMk i
  let K' := J.mapCochainComplexPlus.obj K
  let L' : CochainComplex.Plus A' :=
    ⟨(CochainComplex.singleFunctor A' 0).obj (J.obj M), 0, inferInstance⟩
  let q' : L' ⟶ K' := ObjectProperty.homMk (mapAugmentation J i)
  let Q := DerivedCategory.Plus.Q (C := A)
  let Q' := DerivedCategory.Plus.Q (C := A')
  let QB := DerivedCategory.Plus.Q (C := B)
  let QB' := DerivedCategory.Plus.Q (C := B')
  let RF := F.rightDerivedFunctorPlus
  let RG := G.rightDerivedFunctorPlus
  let EJ := exactDerivedPlus J
  let EH := exactDerivedPlus H
  let β := DerivedCategory.homologyFunctorFactors B (n : ℤ)
  let β' := DerivedCategory.homologyFunctorFactors B' (n : ℤ)
  let HH := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let HH' := DerivedCategory.Plus.homologyFunctor B' (n : ℤ)
  let σ := exactDerivedPlusSingle J
  let θ := exactDerivedPlusFactors J
  let θ' := exactDerivedPlusFactors H
  let α := F.rightDerivedFunctorPlusUnit
  let α' := G.rightDerivedFunctorPlusUnit
  let τ := exactDerivedComparison F G J H c hJ
  let γ := exactComparisonComplexIso F G J H c
  let v := exactHomologyIso H (n : ℤ)
  haveI : IsIso (Q.map q) := Localization.inverts Q (CochainComplex.Plus.quasiIso A) q hi
  haveI : IsIso (Q'.map q') := Localization.inverts Q' (CochainComplex.Plus.quasiIso A') q' hJi
  have hq : EJ.map (Q.map q) ≫ θ.hom.app K = σ.hom.app M ≫ Q'.map q' :=
    exactDerivedPlus_map_augmentation J i
  have hq' : θ.inv.app K ≫ EJ.map (inv (Q.map q)) ≫ σ.hom.app M = inv (Q'.map q') := by
    apply (cancel_mono (Q'.map q')).mp
    rw [Category.assoc, Category.assoc, ← hq, ← EJ.map_comp_assoc,
      IsIso.inv_hom_id, EJ.map_id, Category.id_comp, Iso.inv_hom_id_app, IsIso.inv_hom_id]
  have hn : EH.map (RF.map (inv (Q.map q))) ≫ τ.hom.app (Q.obj L) =
      τ.hom.app (Q.obj K) ≫ RG.map (EJ.map (inv (Q.map q))) :=
    τ.hom.naturality (inv (Q.map q))
  have hτ : θ'.inv.app (F.mapCochainComplexPlus.obj K) ≫ EH.map (α.app K) ≫
      τ.hom.app (Q.obj K) = QB'.map (γ.hom.app K) ≫ α'.app K' ≫ RG.map (θ.inv.app K) := by
    simpa [postExactUnit, preExactUnit, restrictionDerivedUnit, Category.assoc] using
      exactDerivedComparison_unit F G J H c hJ K
  have hα : θ'.inv.app (F.mapCochainComplexPlus.obj K) ≫
      EH.map (α.app K ≫ RF.map (inv (Q.map q))) ≫ τ.hom.app (Q.obj L) ≫
      RG.map (σ.hom.app M) =
      QB'.map (γ.hom.app K) ≫ α'.app K' ≫ RG.map (inv (Q'.map q')) := by
    rw [EH.map_comp, Category.assoc, reassoc_of% hn,
      ← Category.assoc (EH.map (α.app K)), ← Category.assoc (θ'.inv.app _), hτ]
    simp only [Category.assoc, ← RG.map_comp, hq']
  let comparison := (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I
  have hiγ : (γ.hom.app K).hom = comparison := by
    ext q
    simp [γ, exactComparisonComplexIso, mapPlusCompIso, comparison, K]
  have hb : (HomologicalComplex.homologyFunctor B' (.up ℤ) (n : ℤ)).map comparison ≫
      β'.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj K'.obj) =
      β'.inv.app ((H.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        HH'.map (QB'.map (γ.hom.app K)) := by
    rw [← hiγ]
    exact β'.inv.naturality (γ.hom.app K).hom
  let z := α.app K ≫ RF.map (inv (Q.map q))
  rw [exactComparisonIso_hom_app]
  change H.map (β.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫ HH.map z) ≫
      (v.hom.app (RF.obj (Q.obj L)) ≫
        HH'.map (τ.hom.app (Q.obj L) ≫ RG.map (σ.hom.app M))) =
    (((((F.mapHomologicalComplex (.up ℤ)).obj I).sc (n : ℤ)).mapHomologyIso H).inv ≫
      (HomologicalComplex.homologyFunctor B' (.up ℤ) (n : ℤ)).map comparison) ≫
      (β'.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj K'.obj) ≫
        HH'.map (α'.app K' ≫ RG.map (inv (Q'.map q'))))
  have hv : H.map (HH.map z) ≫ v.hom.app (RF.obj (Q.obj L)) =
      v.hom.app (QB.obj (F.mapCochainComplexPlus.obj K)) ≫ HH'.map (EH.map z) :=
    v.hom.naturality z
  simp only [H.map_comp, Category.assoc, reassoc_of% hv, reassoc_of% hb, ← HH'.map_comp]
  dsimp only [v, QB]
  rw [exactHomologyIso_app]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc]
  erw [Iso.inv_hom_id_app, H.map_id, Category.id_comp]
  dsimp only [HH', z]
  erw [← CategoryTheory.Functor.map_comp, hα]
  rfl

private lemma exactComparison_boundary
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M))
    (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ) :
    (exactComparisonIso F G J H c hJ n).hom.app S.X₃ ≫ rightBoundary G (hS.map_of_exact J) n =
      H.map (rightBoundary F hS n) ≫ (exactComparisonIso F G J H c hJ (n + 1)).hom.app S.X₁ := by
  let RF := F.rightDerivedFunctorPlus
  let RG := G.rightDerivedFunctorPlus
  let E := exactDerivedPlus H
  let EJ := exactDerivedPlus J
  let T := plusTriangle A hS
  let τ := exactDerivedComparison F G J H c hJ
  let γ := ((mapTriangleCompIso RF E).inv.app T) ≫
    ((mapTriangleIso τ).app T).hom ≫
    ((mapTriangleCompIso EJ RG).app T).hom ≫
    RG.mapTriangle.map (mapPlusTriangleIso J hS).hom
  have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  have hd := (DerivedCategory.Plus.homologyFunctor B' 0).homologySequenceδ_naturality γ
    (n : ℤ) ((n + 1 : ℕ) : ℤ) hn
  have he := exactHomology_shiftMap H (m := 1) (n := (n : ℤ))
    (n' := ((n + 1 : ℕ) : ℤ)) (by omega) (RF.mapTriangle.obj T).mor₃
  change (exactHomologyIso H _).hom.app _ ≫
    (DerivedCategory.Plus.homologyFunctor B' 0).homologySequenceδ
      (E.mapTriangle.obj (RF.mapTriangle.obj T)) _ _ hn = _ at he
  change _ = H.map (rightBoundary F hS n) ≫ (exactHomologyIso H _).hom.app _ at he
  rw [exactComparisonIso_hom_app, exactComparisonIso_hom_app]
  let HH' := DerivedCategory.Plus.homologyFunctor B' (n : ℤ)
  let HH₁' := DerivedCategory.Plus.homologyFunctor B' ((n + 1 : ℕ) : ℤ)
  have h₁ : γ.hom₁ = τ.hom.app ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁) ≫
      RG.map ((exactDerivedPlusSingle J).hom.app S.X₁) := by
    simp [γ, mapPlusTriangleIso_hom₁, T]
    erw [Category.id_comp]
    rfl
  have h₃ : γ.hom₃ = τ.hom.app ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₃) ≫
      RG.map ((exactDerivedPlusSingle J).hom.app S.X₃) := by
    simp [γ, mapPlusTriangleIso_hom₃, T]
    erw [Category.id_comp]
    rfl
  change HH'.map γ.hom₃ ≫ rightBoundary G (hS.map_of_exact J) n =
    (DerivedCategory.Plus.homologyFunctor B' 0).homologySequenceδ
      (E.mapTriangle.obj (RF.mapTriangle.obj T)) _ _ hn ≫ HH₁'.map γ.hom₁ at hd
  rw [h₁, h₃] at hd
  rw [Category.assoc, hd, ← Category.assoc]
  erw [he, Category.assoc]

private lemma exactComparison_unique
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M))
    (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
    (he : IsResolutionComparison F G J H c e) (n : ℕ) :
    e n = exactComparisonIso F G J H c hJ n := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let L := (CochainComplex.singleFunctor A 0).obj M
  obtain ⟨I, i, _, hi, hI, hb⟩ := InjectiveComplexReplacement.replacement A L 0 inferInstance
  letI := hb
  obtain ⟨hJi, eq⟩ := he M I i hi hI
  haveI : IsIso (resolutionModelMap F i hi n) :=
    SheafCohomology.resolutionModelMap_isIso F _ _
      (fun q => by letI := hI q; exact AcyclicTermComparison.rightAcyclic_of_injective F _) _
  apply (cancel_epi (H.map (resolutionModelMap F i hi n))).mp
  exact (eq n).trans (exactComparison_model F G J H c hJ i hi hJi n).symm

/-- A comparison normalized on the source injective resolutions satisfies the
same model equation on every strictly nonnegative augmented quasi-isomorphism. -/
theorem normalizedComparison_model
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M))
    (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
    (he : IsResolutionComparison F G J H c e)
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i)
    (hJi : QuasiIso (mapAugmentation J i)) (n : ℕ) :
    H.map (resolutionModelMap F i hi n) ≫ (e n).hom.app M =
      (modelComparison F G J H c I n).hom ≫
        resolutionModelMap G (mapAugmentation J i) hJi n := by
  rw [exactComparison_unique F G J H c hJ e he n]
  exact exactComparison_model F G J H c hJ i hi hJi n

/-- Exact change of input and output intertwines the connecting maps of the
short exact stalk triangles through the same augmented-resolution comparison. -/
theorem normalizedComparison_boundary
    (hJ : ∀ M : A, Injective M → rightAcyclicValue G (J.obj M))
    (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
    (he : IsResolutionComparison F G J H c e)
    (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ) :
    (e n).hom.app S.X₃ ≫ rightBoundary G (hS.map_of_exact J) n =
      H.map (rightBoundary F hS n) ≫ (e (n + 1)).hom.app S.X₁ := by
  rw [exactComparison_unique F G J H c hJ e he n,
    exactComparison_unique F G J H c hJ e he (n + 1)]
  exact exactComparison_boundary F G J H c hJ S hS n

end ExactComparison

section HomologyComparison
variable {B B' : Type*} [Category* B] [Category* B'] [Abelian B] [Abelian B']
    (H : B ⥤ B') [H.Additive] [H.PreservesHomology]

open HomologicalComplex

private theorem mapHomologyIso_stalk (M : B) :
    let S := (CochainComplex.singleFunctor B 0).obj M
    ((S.sc 0).mapHomologyIso H).hom ≫
      H.map (singleObjHomologySelfIso (.up ℤ) 0 M).hom =
    homologyMap ((H.mapCochainComplexSingleFunctor 0).hom.app M) 0 ≫
      (singleObjHomologySelfIso (.up ℤ) 0 (H.obj M)).hom := by
  let S := (CochainComplex.singleFunctor B 0).obj M
  let T := (H.mapHomologicalComplex (.up ℤ)).obj S
  let U := (CochainComplex.singleFunctor B' 0).obj (H.obj M)
  let k : T ⟶ U := (H.mapCochainComplexSingleFunctor 0).hom.app M
  change ((S.sc 0).mapHomologyIso H).hom ≫ H.map (singleObjHomologySelfIso _ _ M).hom =
    homologyMap k 0 ≫ (singleObjHomologySelfIso _ _ (H.obj M)).hom
  rw [← cancel_epi (T.homologyπ 0)]
  rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, cyclesMap_i_assoc]
  let D := S.sc 0
  let h := D.homologyData.left
  let h' := h.map H
  change (D.map H).homologyπ ≫ (D.mapHomologyIso H).hom ≫ H.map
    (singleObjHomologySelfIso (.up ℤ) 0 M).hom =
    (D.map H).iCycles ≫ k.f 0 ≫ (singleObjXSelf (.up ℤ) 0 (H.obj M)).hom
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq h H]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc, ← Functor.map_comp]
  have hs : h.π ≫ h.homologyIso.inv ≫ (singleObjHomologySelfIso (.up ℤ) 0 M).hom =
      h.i ≫ (singleObjXSelf (.up ℤ) 0 M).hom := by
    rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv_assoc]
    change _ ≫ S.homologyπ 0 ≫ _ = _
    rw [homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom,
      ← Category.assoc]
    apply congrArg (fun z ↦ z ≫ (singleObjXSelf (.up ℤ) 0 M).hom)
    exact h.cyclesIso_inv_comp_iCycles
  change _ ≫ H.map h.π ≫ H.map (h.homologyIso.inv ≫ _) = _
  rw [← H.map_comp]
  rw [hs, H.map_comp]
  have ht := ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i h'
  change _ ≫ H.map h.i = (D.map H).iCycles at ht
  rw [reassoc_of% ht]
  congr 1
  change _ = ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app M).f 0 ≫ _
  rw [singleMapHomologicalComplex_hom_app_self, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HomologyComparison

section Stalk
open HomologicalComplex

private def mappedStalkHomology {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] (M : A) :
    (((F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj M)).homology 0) ≅ F.obj M :=
  (homologyFunctor B (.up ℤ) 0).mapIso
    ((singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
    singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  (F : A ⥤ B) (H : B ⥤ B') [F.Additive] [H.Additive] [H.PreservesHomology]

private theorem mappedStalkHomology_postcomp (M : A) :
    let K := (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj M)
    H.map (mappedStalkHomology F M).inv ≫ ((K.sc 0).mapHomologyIso H).inv =
      (mappedStalkHomology (F ⋙ H) M).inv := by
  let S := (CochainComplex.singleFunctor B 0).obj (F.obj M)
  let K := (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj M)
  let k : K ⟶ S := (singleMapHomologicalComplex F (.up ℤ) 0).hom.app M
  let j : (H.mapHomologicalComplex (.up ℤ)).obj S ⟶
      (CochainComplex.singleFunctor B' 0).obj (H.obj (F.obj M)) :=
    (singleMapHomologicalComplex H (.up ℤ) 0).hom.app (F.obj M)
  have hk : (H.mapHomologicalComplex (.up ℤ)).map k ≫ j =
      (singleMapHomologicalComplex (F ⋙ H) (.up ℤ) 0).hom.app M := by
    apply HomologicalComplex.hom_ext
    intro q
    by_cases hq : q = 0
    · subst q
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, k, j,
        singleMapHomologicalComplex_hom_app_self, Functor.map_comp, Functor.comp_map,
        Functor.comp_obj, Category.assoc]
      rw [← H.map_comp_assoc, ← H.map_comp_assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    · apply ((isZero_single_obj_X (.up ℤ) 0 _ q hq).eq_of_tgt)
  rw [← cancel_mono (mappedStalkHomology (F ⋙ H) M).hom,
    Iso.inv_hom_id]
  simp only [Category.assoc]
  change H.map (mappedStalkHomology F M).inv ≫ ((K.sc 0).mapHomologyIso H).inv ≫
      homologyMap ((singleMapHomologicalComplex (F ⋙ H) (.up ℤ) 0).hom.app M) 0 ≫ _ = _
  have hn := ShortComplex.mapHomologyIso_inv_naturality ((shortComplexFunctor B (.up ℤ) 0).map k) H
  change H.map (homologyMap k 0) ≫ ((S.sc 0).mapHomologyIso H).inv =
    ((K.sc 0).mapHomologyIso H).inv ≫ homologyMap ((H.mapHomologicalComplex (.up ℤ)).map k) 0 at hn
  rw [← hk, homologyMap_comp, Category.assoc, ← reassoc_of% hn, ← H.map_comp_assoc]
  have hs : (mappedStalkHomology F M).inv ≫ homologyMap k 0 =
      (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv := by
    change _ ≫ ((homologyFunctor B (.up ℤ) 0).mapIso
      ((singleMapHomologicalComplex F (.up ℤ) 0).app M)).hom = _
    simp [mappedStalkHomology, Category.assoc]
  rw [hs]
  change H.map _ ≫ ((S.sc 0).mapHomologyIso H).inv ≫
    homologyMap ((H.mapCochainComplexSingleFunctor 0).hom.app (F.obj M)) 0 ≫
      (singleObjHomologySelfIso (.up ℤ) 0 (H.obj (F.obj M))).hom = _
  rw [← mapHomologyIso_stalk H (F.obj M), Iso.inv_hom_id_assoc, ← H.map_comp,
    Iso.inv_hom_id, H.map_id]

end Stalk

section DegreeZero
open HomologicalComplex

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [EnoughInjectives A] [EnoughInjectives A']
  (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
  [F.Additive] [G.Additive] [J.Additive] [H.Additive] [H.PreservesHomology]
  [PreservesFiniteLimits J] [PreservesFiniteLimits G]
  (c : F ⋙ H ≅ J ⋙ G)

theorem resolutionComparison_zero
    (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
    (he : IsResolutionComparison F G J H c e) :
    whiskerRight (rightDegreeZeroUnit F) H ≫ (e 0).hom =
      c.hom ≫ whiskerLeft J (rightDegreeZeroUnit G) := by
  let E (M : A) : Prop :=
    H.map ((rightDegreeZeroUnit F).app M) ≫ (e 0).hom.app M =
      c.hom.app M ≫ (rightDegreeZeroUnit G).app (J.obj M)
  have hI (M : A) (hM : Injective M) : E M := by
    let S := (CochainComplex.singleFunctor A 0).obj M
    have hs (q : ℤ) : Injective (S.X q) := by
      by_cases hq : q = 0
      · subst q
        exact Injective.of_iso (singleObjXSelf (.up ℤ) 0 M).symm hM
      · exact (isZero_single_obj_X (.up ℤ) 0 M q hq).injective
    obtain ⟨hj, hm⟩ := he M S (𝟙 S) (by infer_instance) hs
    have h := hm 0
    let K : CochainComplex A' ℤ := (J.mapHomologicalComplex (.up ℤ)).obj S
    let j : (CochainComplex.singleFunctor A' 0).obj (J.obj M) ⟶ K :=
      (J.mapCochainComplexSingleFunctor 0).inv.app M
    have hj' : mapAugmentation J (𝟙 S) = j := by
      rw [mapAugmentation, CategoryTheory.Functor.map_id]
      exact Category.comp_id j
    letI : K.IsStrictlyGE 0 := by
      dsimp only [K, S]
      infer_instance
    simp only [hj'] at h
    have h' : QuasiIso j := by dsimp [j]; infer_instance
    change H.map ((rightDegreeZeroUnit F).app M) ≫ _ = _
    rw [AdvancedHomologicalAlgebra.SheafCohomology.rightDegreeZeroUnit_stalk,
      Functor.map_comp, Category.assoc, h]
    simp only [modelComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc]
    change H.map (mappedStalkHomology F M).inv ≫
      (((F.mapHomologicalComplex (.up ℤ)).obj S).sc 0 |>.mapHomologyIso H).inv ≫
      homologyMap ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app S) 0 ≫
      resolutionModelMap G j h' 0 = _
    rw [← Category.assoc, mappedStalkHomology_postcomp]
    have hh := AdvancedHomologicalAlgebra.SheafCohomology.homology_stalk_comparison
      J G (F ⋙ H) c.symm M
    have hn := AdvancedHomologicalAlgebra.SheafCohomology.resolutionModelMap_naturality
      G j h' (𝟙 ((CochainComplex.singleFunctor A' 0).obj (J.obj M)))
      (by infer_instance) (𝟙 (J.obj M))
      ((J.mapCochainComplexSingleFunctor 0).hom.app M)
      (by
        apply congrArg DerivedCategory.Q.map
        rw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact (J.mapCochainComplexSingleFunctor 0).inv_hom_id_app M) 0
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn
    rw [hn, AdvancedHomologicalAlgebra.SheafCohomology.rightDegreeZeroUnit_stalk]
    simpa only [Category.assoc] using! congrArg
      (fun k ↦ k ≫ resolutionModelMap G (𝟙 ((CochainComplex.singleFunctor A' 0).obj (J.obj M)))
        (by infer_instance) 0) hh
  let τ := whiskerRight (rightDegreeZeroUnit F) H ≫ (e 0).hom
  let σ := c.hom ≫ whiskerLeft J (rightDegreeZeroUnit G)
  have ug : IsIso (rightDegreeZeroUnit G) :=
    AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightZero _ _ G
  letI := ug
  apply NatTrans.ext
  funext M
  let i := Injective.ι M
  let T := J ⋙ rightValue G 0
  have hm : Mono ((rightValue G 0).map (J.map i)) := by
    haveI : Mono (J.map i) := by dsimp [i]; infer_instance
    have hh := (rightDegreeZeroUnit G).naturality (J.map i)
    have h : (rightValue G 0).map (J.map i) =
        inv ((rightDegreeZeroUnit G).app (J.obj M)) ≫
          G.map (J.map i) ≫ (rightDegreeZeroUnit G).app (J.obj (Injective.under M)) := by
      rw [hh, IsIso.inv_hom_id_assoc]
    rw [h]
    infer_instance
  haveI : Mono (T.map i) := hm
  apply (cancel_mono (T.map i)).mp
  change τ.app M ≫ T.map i = σ.app M ≫ T.map i
  rw [← τ.naturality i, ← σ.naturality i]
  exact congrArg (fun k ↦ (F ⋙ H).map i ≫ k) (hI _ inferInstance)

end DegreeZero

theorem siteComparison : siteComparisonType.{a,u,r} := by
  intro X R U _
  refine compareResolutions _ _ _ _ (siteSectionsIso.{a} R U) ?_
  intro M hM
  letI := (transportEquivalence.{a} R).map_injective_iff M |>.2 hM
  exact AcyclicTermComparison.rightAcyclic_of_injective _ _

theorem siteComparisonOriginal : siteComparisonOriginalType.{a,u,r} := by
  intro X R U _
  obtain ⟨e, he⟩ := siteComparison.{a,u,r} R U
  exact ⟨e, fun n ↦ recoverOriginalScalars.{a} R U _ n (e n), he, fun _ ↦ rfl⟩

theorem flasque : flasqueType.{a,u,r} := by
  intro X R U _ M hM n
  obtain ⟨V, rfl⟩ := (opensEquiv.{max a u r} X).surjective U
  obtain ⟨e, _⟩ := siteComparison.{a,u,r} R V
  have hv := SheafCohomology.flasque (liftedRing.{a} R) V ((transport.{a} R).obj M)
    ((ambient_flasque.{a,u,r} X R M).2 hM) n
  have hzero := hv.of_iso ((e (n + 1)).app M)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (liftedScalars.{a} R V).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hzero

theorem ambientComparison : ambientComparisonType.{a,u,r,b} := by
  intro X R U _ _
  let J := liftSheafCoefficients.{b,u,r,max a u r} R
  have he := coefficient_lift_ambient_sheaf_exact.{b,u,r,a} X R
  letI := he.1
  letI := he.2
  refine compareResolutions _ _ J _ _ ?_
  intro M hM
  let Γ := sectionsValue.{max b a} R U
  letI := original_sections_left_exact.{max b a,u,r} X R U
  apply (AcyclicTermComparison.rightVanishing _ _ Γ _).2
  intro n
  exact flasque.{max b a,u,r} R U (J.obj M)
    ((coefficient_lift_flasque.{b,u,r,max a u r} X R M).2
      (original_injectives_flasque.{a,u,r} X R M hM)) n

section ForgetScalars

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

private theorem toSheafPreservesFiniteColimits : PreservesFiniteColimits (SheafOfModules.toSheaf.{max a u r} R) := by
  let J := SheafOfModules.toSheaf.{max a u r} R
  let E := (originalAbelianEquivalence.{max a u r} X).functor
  have c : transport.{a} R ⋙ SheafOfModules.toSheaf (liftedRing.{a} R) ≅ J ⋙ E :=
    (forgetAbelianTransport.{a,u,r,0} X R).1
  haveI : PreservesFiniteColimits (J ⋙ E) := preservesFiniteColimits_of_natIso c
  exact preservesFiniteColimits_of_reflects_of_preserves J E

private instance (U : Opens X) :
    PreservesFiniteLimits (abelianSectionsValue.{a,u,r} X U) := by
  let L := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max a u r}
  let V := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max a u r}).obj (op U)
  change PreservesFiniteLimits (L ⋙ V)
  infer_instance

theorem abelianEnoughInjectives (X : TopCat.{u}) :
    EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X) :=
  EnoughInjectives.of_equivalence (originalAbelianEquivalence.{max a u r} X).functor

theorem abelianSiteComparison : abelianSiteComparisonType.{a,u,r} := by
  intro X U _
  refine compareResolutions _ _ _ _ (abelianSiteSectionsIso.{a,u,r} X U) ?_
  intro M hM
  letI := (originalAbelianEquivalence.{max a u r} X).map_injective_iff M |>.2 hM
  exact AcyclicTermComparison.rightAcyclic_of_injective _ _

private theorem forgetInjectiveFlasque (M : AmbientSheaves.{a} R) (hM : Injective M) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf.{max a u r} R).obj M) := by
  have h := original_injectives_flasque.{a,u,r} X R M hM
  exact ⟨fun {V W} i ↦ (AddCommGrpCat.epi_iff_surjective _).2 (h W.unop V.unop i.unop)⟩

theorem forgottenResolution :
    Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients.forgottenResolutionType.{a,u,r} := by
  intro X R M I _ i hi hI
  let J := SheafOfModules.toSheaf.{max a u r} R
  letI : PreservesFiniteColimits J := toSheafPreservesFiniteColimits.{a,u,r} R
  exact ⟨mapAugmentation_quasiIso J i hi, fun q ↦ forgetInjectiveFlasque.{a,u,r} R _ (hI q)⟩


theorem abelianFlasque (X : TopCat.{u}) (U : Opens X)
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)]
    (M : OriginalAbelianSheaves.{a,u,r} X) (hM : TopCat.Sheaf.IsFlasque M) (n : ℕ) :
    IsZero ((rightValue (abelianSectionsValue.{a,u,r} X U) (n + 1)).obj M) := by
  obtain ⟨V, rfl⟩ := (opensEquiv.{max a u r} X).surjective U
  let E := abelianTransport.{a,u,r} X
  obtain ⟨e, _⟩ := abelianSiteComparison.{a,u,r} X V
  haveI : TopCat.Sheaf.IsFlasque (E.obj M) :=
    ⟨fun i ↦ hM.epi ((opensEquiv.{max a u r} X).equivalence.functor.op.map i)⟩
  exact (SheafCohomology.abelianFlasqueAcyclic _ V (E.obj M) inferInstance n).of_iso
    ((e (n + 1)).app M)

theorem forgetComparison : forgetComparisonType.{a,u,r} := by
  intro X R U _ _
  let J := SheafOfModules.toSheaf.{max a u r} R
  let F := sectionsValue.{a} R U
  let G := abelianSectionsValue.{a,u,r} X U
  let H := forget₂ (SectionModules.{a} R U) AddCommGrpCat.{max a u r}
  letI : PreservesFiniteColimits J := toSheafPreservesFiniteColimits.{a,u,r} R
  let c : F ⋙ H ≅ J ⋙ G := Iso.refl _
  refine compareResolutions F G J H c ?_
  intro M hM
  apply (AcyclicTermComparison.rightVanishing _ _ G _).2
  intro n
  exact abelianFlasque.{a,u,r} X U (J.obj M) (forgetInjectiveFlasque.{a,u,r} R M hM) n

end ForgetScalars

theorem siteComparisonZero : siteComparisonZeroType.{a,u,r} := by
  intro X R U _
  obtain ⟨e, he⟩ := siteComparison.{a,u,r} R U
  exact ⟨e, he, resolutionComparison_zero _ _ _ _ _ _ he⟩

theorem ambientComparisonZero : ambientComparisonZeroType.{a,u,r,b} := by
  intro X R U _ _
  have hex := coefficient_lift_ambient_sheaf_exact.{b,u,r,a} X R
  letI := hex.1
  letI := original_sections_left_exact.{max b a,u,r} X R U
  obtain ⟨e, he⟩ := ambientComparison.{a,u,r,b} R U
  exact ⟨e, he, resolutionComparison_zero _ _ _ _ _ _ he⟩

theorem forgetComparisonZero : forgetComparisonZeroType.{a,u,r} := by
  intro X R U _ _
  obtain ⟨e, he⟩ := forgetComparison.{a,u,r} R U
  exact ⟨e, he, resolutionComparison_zero _ _ _ _ _ _ he⟩

theorem abelianSiteComparisonZero : abelianSiteComparisonZeroType.{a,u,r} := by
  intro X U _
  obtain ⟨e, he⟩ := abelianSiteComparison.{a,u,r} X U
  exact ⟨e, he, resolutionComparison_zero _ _ _ _ _ _ he⟩

theorem siteComparisonOriginalZero : siteComparisonOriginalZeroType.{a,u,r} := by
  intro X R U _
  obtain ⟨e, he, hz⟩ := siteComparisonZero.{a,u,r} R U
  refine ⟨e, he, ?_⟩
  let F := sectionsValue.{a} R (opensEquiv X U)
  let G := sectionsValue.{0} (liftedRing.{a} R) U
  let J := transport.{a} R
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r}
    (sectionRingEquiv.{a} R U)
  apply NatTrans.ext
  funext M
  have hu := congrArg (fun t ↦ t.app M) hz
  change E.inverse.map ((rightDegreeZeroUnit F).app M) ≫ (e 0).hom.app M =
    (siteSectionsIso.{a} R U).hom.app M ≫ (rightDegreeZeroUnit G).app (J.obj M) at hu
  have hh := E.counitIso.inv.naturality ((rightDegreeZeroUnit F).app M)
  simp only [Functor.id_map, Functor.comp_map] at hh
  simp only [recoverOriginalScalars, originalSiteSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Category.id_comp, Category.assoc]
  change (rightDegreeZeroUnit F).app M ≫ E.counitIso.inv.app ((rightValue F 0).obj M) ≫
      E.functor.map ((e 0).hom.app M) =
    E.counitIso.inv.app (F.obj M) ≫ E.functor.map ((siteSectionsIso.{a} R U).hom.app M) ≫
      E.functor.map ((rightDegreeZeroUnit G).app (J.obj M))
  rw [reassoc_of% hh, ← E.functor.map_comp, hu, E.functor.map_comp]


private theorem exactResolutionComparison_of_zero
    {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [EnoughInjectives A] [EnoughInjectives A']
    (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
    [F.Additive] [G.Additive] [J.Additive] [H.Additive] [H.PreservesHomology]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (c : F ⋙ H ≅ J ⋙ G)
    (hJ : ∀ M : A, Injective M →
      Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue G (J.obj M))
    (he : DegreeZeroResolutionComparison F G J H c) :
    ExactResolutionComparison F G J H c := by
  letI := H.preservesFiniteLimits_of_preservesHomology
  letI := H.preservesFiniteColimits_of_preservesHomology
  obtain ⟨e, hm, h₀⟩ := he
  refine ⟨e, hm, h₀, fun S hS ↦ ⟨hS.map_of_exact J, ?_⟩⟩
  exact normalizedComparison_boundary F G J H c hJ e hm S hS

theorem siteComparisonExact : siteComparisonExactType.{a,u,r} := by
  intro X R U _
  refine exactResolutionComparison_of_zero _ _ _ _ _ ?_ (siteComparisonZero.{a,u,r} R U)
  intro M hM
  letI := (transportEquivalence.{a} R).map_injective_iff M |>.2 hM
  exact AcyclicTermComparison.rightAcyclic_of_injective _ _

theorem ambientComparisonExact : ambientComparisonExactType.{a,u,r,b} := by
  intro X R U _ _
  let J := liftSheafCoefficients.{b,u,r,max a u r} R
  let Γ := sectionsValue.{max b a} R U
  have h := coefficient_lift_ambient_sheaf_exact.{b,u,r,a} X R
  letI := h.1
  letI := h.2
  letI := original_sections_left_exact.{max b a,u,r} X R U
  refine exactResolutionComparison_of_zero _ Γ J _ _ ?_ (ambientComparisonZero.{a,u,r,b} R U)
  intro M hM
  apply (AcyclicTermComparison.rightVanishing _ _ Γ _).2
  intro n
  exact flasque.{max b a,u,r} R U (J.obj M)
    ((coefficient_lift_flasque.{b,u,r,max a u r} X R M).2
      (original_injectives_flasque.{a,u,r} X R M hM)) n

theorem forgetComparisonExact : forgetComparisonExactType.{a,u,r} := by
  intro X R U _ _
  let J := SheafOfModules.toSheaf.{max a u r} R
  let G := abelianSectionsValue.{a,u,r} X U
  letI : PreservesFiniteColimits J := toSheafPreservesFiniteColimits.{a,u,r} R
  refine exactResolutionComparison_of_zero _ G J _ _ ?_ (forgetComparisonZero.{a,u,r} R U)
  intro M hM
  apply (AcyclicTermComparison.rightVanishing _ _ G _).2
  intro n
  exact abelianFlasque.{a,u,r} X U (J.obj M) (forgetInjectiveFlasque.{a,u,r} R M hM) n

theorem abelianSiteComparisonExact : abelianSiteComparisonExactType.{a,u,r} := by
  intro X U _
  refine exactResolutionComparison_of_zero _ _ _ _ _ ?_ (abelianSiteComparisonZero.{a,u,r} X U)
  intro M hM
  letI := (originalAbelianEquivalence.{max a u r} X).map_injective_iff M |>.2 hM
  exact AcyclicTermComparison.rightAcyclic_of_injective _ _

theorem siteComparisonOriginalExact : siteComparisonOriginalExactType.{a,u,r} := by
  intro X R U _
  dsimp only
  let F := sectionsValue.{a} R (opensEquiv X U)
  let G := sectionsValue.{0} (liftedRing.{a} R) U
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r}
    (sectionRingEquiv.{a} R U)
  obtain ⟨e, hm, h₀⟩ := siteComparisonOriginalZero.{a,u,r} R U
  obtain ⟨e', hm', _, hb⟩ := siteComparisonExact.{a,u,r} R U
  have he : e' = e := resolutionComparison_unique F G
    (transport.{a} R) (liftedScalars.{a} R U) (siteSectionsIso.{a} R U) hm' hm
  subst e'
  refine ⟨e, hm, h₀, ?_⟩
  intro S hS
  obtain ⟨hJS, hδ⟩ := hb S hS
  refine ⟨hJS, ?_⟩
  intro n
  have h (n : ℕ) (M : AmbientSheaves.{a} R) :
      (recoverOriginalScalars.{a} R U _ n (e n)).hom.app M =
        E.counitIso.inv.app ((rightValue F n).obj M) ≫ E.functor.map ((e n).hom.app M) := by
    simp [recoverOriginalScalars, E]
    rfl
  rw [h, h, Category.assoc]
  change E.counitIso.inv.app _ ≫ E.functor.map ((e n).hom.app S.X₃) ≫
      E.functor.map (rightBoundary G hJS n) = _
  rw [← E.functor.map_comp, hδ n, E.functor.map_comp]
  erw [← reassoc_of% (E.counitIso.inv.naturality (rightBoundary F hS n))]

set_option maxHeartbeats 600000 in
theorem forgetSiteCompatibility : forgetSiteCompatibilityType.{a,u,r} := by
  intro X R U _ _
  dsimp only
  let V := opensEquiv X U
  let R' := liftedRing.{a} R
  let F := sectionsValue.{a} R V
  let G := sectionsValue.{0} R' U
  let C := abelianSectionsValue.{a,u,r} X V
  let D := AdvancedHomologicalAlgebra.SheafTheory.abelianSections _ U
  let J := transport.{a} R
  let E := abelianTransport.{a,u,r} X
  let O := SheafOfModules.toSheaf.{max a u r} R
  let O' := SheafOfModules.toSheaf.{max a u r} R'
  let H := liftedScalars.{a} R U
  let K := forget₂ (SectionModules.{a} R V) AddCommGrpCat.{max a u r}
  let K' := forget₂ (SectionModules.{0} R' U) AddCommGrpCat.{max a u r}
  obtain ⟨e, he, e₀, eδ⟩ := siteComparisonExact.{a,u,r} R U
  obtain ⟨f, hf, f₀, fδ⟩ := forgetComparisonExact.{a,u,r} R V
  obtain ⟨s, hs, s₀, sδ⟩ := abelianSiteComparisonExact.{a,u,r} X U
  obtain ⟨t, ht, t₀, tδ⟩ := forgetComparisonExact.{0,max a u r,max a u r} R' U
  refine ⟨e, f, s, t, he, hf, hs, ht, ?_⟩
  have sameMap {P Q : SectionModules.{a} R V} (g : P ⟶ Q) :
      K.map g = K'.map (H.map g) := rfl
  have core (n : ℕ) (M : AmbientSheaves.{a} R) :
      (f n).hom.app M ≫ (s n).hom.app (O.obj M) =
        K'.map ((e n).hom.app M) ≫ (t n).hom.app (J.obj M) := by
    induction n generalizing M with
    | zero =>
      haveI := zero.{a,u,r} R V
      let z := (rightDegreeZeroUnit F).app M
      let z₁ := (rightDegreeZeroUnit C).app (O.obj M)
      let z₂ := (rightDegreeZeroUnit G).app (J.obj M)
      let z₃ := (rightDegreeZeroUnit D).app (E.obj (O.obj M))
      have left₀ : K.map z ≫ (f 0).hom.app M = z₁ :=
        (NatTrans.congr_app f₀ M).trans (Category.id_comp _)
      have left₁ : z₁ ≫ (s 0).hom.app (O.obj M) = z₃ :=
        (NatTrans.congr_app s₀ (O.obj M)).trans (Category.id_comp _)
      have right₀ : K'.map (H.map z) ≫ K'.map ((e 0).hom.app M) = K'.map z₂ := by
        have h : K'.map ((siteSectionsIso.{a} R U).hom.app M) = 𝟙 (K'.obj (H.obj (F.obj M))) := by
          ext x
          rfl
        calc
          _ = K'.map (H.map z ≫ (e 0).hom.app M) := (K'.map_comp _ _).symm
          _ = K'.map ((siteSectionsIso.{a} R U).hom.app M ≫ z₂) :=
            congrArg K'.map (NatTrans.congr_app e₀ M)
          _ = K'.map z₂ := (K'.map_comp _ _).trans ((congrArg (fun k ↦ k ≫ K'.map z₂) h).trans
            (Category.id_comp _))
      have right₁ : K'.map z₂ ≫ (t 0).hom.app (J.obj M) = z₃ :=
        (NatTrans.congr_app t₀ (J.obj M)).trans (Category.id_comp _)
      haveI : IsIso z := by dsimp [z]; infer_instance
      apply (cancel_epi (K.map z)).mp
      refine ((reassoc_of% left₀) ((s 0).hom.app (O.obj M))).trans (left₁.trans ?_)
      exact ((congrArg (fun k ↦ k ≫ K'.map ((e 0).hom.app M) ≫ (t 0).hom.app (J.obj M))
        (sameMap z)).trans (((reassoc_of% right₀) ((t 0).hom.app (J.obj M))).trans right₁)).symm
    | succ n ih =>
      let S := UniversalDeltaFunctors.injectiveSequence M
      let hS := UniversalDeltaFunctors.injectiveSequence_shortExact M
      obtain ⟨hJS, hE⟩ := eδ S hS
      obtain ⟨hOS, hF⟩ := fδ S hS
      obtain ⟨hEOS, hA⟩ := sδ (S.map O) hOS
      obtain ⟨hOJS, hT⟩ := tδ (S.map J) hJS
      let d := rightBoundary F hS n
      let d₁ := rightBoundary C hOS n
      let d₂ := rightBoundary G hJS n
      let d₃ := rightBoundary D hEOS n
      have h₁ : (e n).hom.app S.X₃ ≫ d₂ =
          H.map d ≫ (e (n + 1)).hom.app M := hE n
      have h₂ : (f n).hom.app S.X₃ ≫ d₁ =
          K.map d ≫ (f (n + 1)).hom.app M := hF n
      have h₃ : (s n).hom.app (O.obj S.X₃) ≫ d₃ =
          d₁ ≫ (s (n + 1)).hom.app (O.obj M) := hA n
      have h₄ : (t n).hom.app (J.obj S.X₃) ≫ d₃ =
          K'.map d₂ ≫ (t (n + 1)).hom.app (J.obj M) := hT n
      haveI : Epi d := by
        exact UniversalDeltaFunctors.dimensionShift_epi (systemValue.{a} R V)
          (longExact.{a,u,r} R V) (fun I _ n ↦ ClassicalDerivedValues.rightInjectiveVanishing _ _ F I n)
          M n
      haveI : Epi (K.map d) := CategoryTheory.Functor.map_epi K d
      apply (cancel_epi (K.map d)).mp
      calc
        _ = (f n).hom.app S.X₃ ≫ d₁ ≫ (s (n + 1)).hom.app (O.obj M) :=
          ((reassoc_of% h₂) ((s (n + 1)).hom.app (O.obj M))).symm
        _ = (f n).hom.app S.X₃ ≫ (s n).hom.app (O.obj S.X₃) ≫ d₃ :=
          congrArg (fun k ↦ (f n).hom.app S.X₃ ≫ k) h₃.symm
        _ = K'.map ((e n).hom.app S.X₃) ≫ (t n).hom.app (J.obj S.X₃) ≫ d₃ :=
          (reassoc_of% (ih S.X₃)) d₃
        _ = K'.map ((e n).hom.app S.X₃) ≫ K'.map d₂ ≫ (t (n + 1)).hom.app (J.obj M) :=
          congrArg (fun k ↦ K'.map ((e n).hom.app S.X₃) ≫ k) h₄
        _ = K'.map (H.map d) ≫ K'.map ((e (n + 1)).hom.app M) ≫ (t (n + 1)).hom.app (J.obj M) := by
          rw [← K'.map_comp_assoc, h₁, K'.map_comp_assoc]
        _ = _ := congrArg (fun k ↦ k ≫ K'.map ((e (n + 1)).hom.app M) ≫ (t (n + 1)).hom.app (J.obj M))
          (sameMap d).symm
  intro M n
  have rid :
      (rightValue D n).map
        ((Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.forgetAbelianComparisonValue.{a,u,r,0} X R).1.hom.app M) =
          𝟙 ((rightValue D n).obj (O'.obj (J.obj M))) :=
    (rightValue D n).map_id _
  refine (core n M).trans ?_
  exact congrArg (fun k ↦ K'.map ((e n).hom.app M) ≫ k)
    ((Category.comp_id ((t n).hom.app (J.obj M))).symm.trans
      (congrArg (fun k ↦ (t n).hom.app (J.obj M) ≫ k) rid.symm))


set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 1000000 in
private def abelianLift_sheafification (X : TopCat.{u}) :
    (whiskeringRight (Opens X)ᵒᵖ _ _).obj AddCommGrpCat.uliftFunctor.{b,max a u r} ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max a b u r} ≅
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max a u r} ⋙
      abelianCoefficientLift.{a,u,r,b} X := by
  let J := Opens.grothendieckTopology X
  let A := AddCommGrpCat.{max a u r}
  let B := AddCommGrpCat.{max a b u r}
  let V := AddCommGrpCat.uliftFunctor.{b,max a u r}
  let F := (whiskeringRight (Opens X)ᵒᵖ A B).obj V
  haveI (U : Opens X) : PreservesColimitsOfShape (J.Cover U)ᵒᵖ (forget A) :=
    (preservesFilteredColimitsOfSize_of_univLE.{max a u r,max a u r,u,u}
      (forget A)).preserves_filtered_colimits _
  haveI (U : Opens X) : PreservesColimitsOfShape (J.Cover U)ᵒᵖ (forget B) :=
    (preservesFilteredColimitsOfSize_of_univLE.{max a b u r,max a b u r,u,u}
      (forget B)).preserves_filtered_colimits _
  apply ((FullyFaithful.ofFullyFaithful (sheafToPresheaf J B)).whiskeringRight _).preimageIso
  exact isoWhiskerLeft F (CategoryTheory.plusPlusFunctorIsoSheafification J B).symm ≪≫
    (J.sheafificationWhiskerRightIso V).symm ≪≫
    isoWhiskerRight (CategoryTheory.plusPlusFunctorIsoSheafification J A) F

set_option maxHeartbeats 1000000 in
private lemma abelianLift_exact (X : TopCat.{u}) :
    PreservesFiniteLimits (abelianCoefficientLift.{a,u,r,b} X) ∧
      PreservesFiniteColimits (abelianCoefficientLift.{a,u,r,b} X) := by
  let J := Opens.grothendieckTopology X
  let A := AddCommGrpCat.{max a u r}
  let B := AddCommGrpCat.{max a b u r}
  let T := abelianCoefficientLift.{a,u,r,b} X
  let V := AddCommGrpCat.uliftFunctor.{b,max a u r}
  let F := (whiskeringRight (Opens X)ᵒᵖ A B).obj V
  let I := sheafToPresheaf J A
  let L := presheafToSheaf J A
  constructor
  · haveI : PreservesFiniteLimits (T ⋙ sheafToPresheaf J B) :=
      inferInstanceAs (PreservesFiniteLimits (I ⋙ F))
    exact preservesFiniteLimits_of_reflects_of_preserves T (sheafToPresheaf J B)
  · haveI : PreservesFiniteColimits (L ⋙ T) :=
      preservesFiniteColimits_of_natIso (abelianLift_sheafification.{a,u,r,b} X)
    constructor
    intro K _ _
    constructor
    intro D
    let P := D ⋙ I
    let hP := colimit.isColimit P
    haveI : PreservesColimit (P ⋙ L) T :=
      preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hP)
        (isColimitOfPreserves (L ⋙ T) hP)
    exact preservesColimit_of_iso_diagram T
      (associator D I L ≪≫ isoWhiskerLeft D (sheafificationNatIso J A).symm ≪≫ rightUnitor D)

private lemma abelianLift_injective_flasque {X : TopCat.{u}}
    (M : OriginalAbelianSheaves.{a,u,r} X) (hM : Injective M) :
    TopCat.Sheaf.IsFlasque ((abelianCoefficientLift.{a,u,r,b} X).obj M) := by
  let E := abelianTransport.{a,u,r} X
  letI : Injective (E.obj M) :=
    (originalAbelianEquivalence.{max a u r} X).map_injective_iff M |>.2 hM
  have h := SheafInjectivesAndRestriction.abelian_injective_flasque _ (E.obj M) inferInstance
  refine ⟨fun {S T} f ↦ ?_⟩
  obtain ⟨S, rfl⟩ : ∃ W, op (opensEquiv.{max a u r} X W) = S := by
    obtain ⟨W, hW⟩ := (opensEquiv.{max a u r} X).surjective S.unop
    exact ⟨W, congrArg op hW⟩
  obtain ⟨T, rfl⟩ : ∃ W, op (opensEquiv.{max a u r} X W) = T := by
    obtain ⟨W, hW⟩ := (opensEquiv.{max a u r} X).surjective T.unop
    exact ⟨W, congrArg op hW⟩
  let g : op S ⟶ op T := (opensEquiv.{max a u r} X).equivalence.functor.op.preimage f
  have hE := h.epi g
  have hf : (opensEquiv.{max a u r} X).equivalence.functor.op.map g = f := Functor.map_preimage _ _
  let V := AddCommGrpCat.uliftFunctor.{b,max a u r}
  change Epi (V.map (M.obj.map f))
  rw [← hf]
  exact Functor.map_epi V ((E.obj M).obj.map g)


theorem abelianAmbientComparisonExact : abelianAmbientComparisonExactType.{a,u,r,b} := by
  intro X U _ _
  let F := abelianSectionsValue.{a,u,r} X U
  let G := abelianSectionsValue.{max a b,u,r} X U
  let J := abelianCoefficientLift.{a,u,r,b} X
  let H := AddCommGrpCat.uliftFunctor.{b,max a u r}
  let c := abelianCoefficientSectionsIso.{a,u,r,b} X U
  have h := abelianLift_exact.{a,u,r,b} X
  letI := h.1
  letI := h.2
  letI : PreservesFiniteLimits G := comp_preservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max a b u r})
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max a b u r}).obj (op U))
  have hJ (M : OriginalAbelianSheaves.{a,u,r} X) (hM : Injective M) :
      Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue G (J.obj M) := by
    apply (AcyclicTermComparison.rightVanishing _ _ G _).2
    intro n
    exact abelianFlasque.{max a b,u,r} X U (J.obj M)
      (abelianLift_injective_flasque.{a,u,r,b} M hM) n
  obtain ⟨e, he⟩ := compareResolutions F G J H c hJ
  exact exactResolutionComparison_of_zero F G J H c hJ
    ⟨e, he, resolutionComparison_zero F G J H c e he⟩

set_option maxHeartbeats 700000 in
theorem forgetAmbientCompatibility : forgetAmbientCompatibilityType.{a,u,r,b} := by
  intro X R U _ _ _ _
  dsimp only
  let F := sectionsValue.{a} R U
  let G := sectionsValue.{max a b} R U
  let C := abelianSectionsValue.{a,u,r} X U
  let D := abelianSectionsValue.{max a b,u,r} X U
  let J := liftSheafCoefficients.{b,u,r,max a u r} R
  let E := abelianCoefficientLift.{a,u,r,b} X
  let O := SheafOfModules.toSheaf.{max a u r} R
  let O' := SheafOfModules.toSheaf.{max a b u r} R
  let H := ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U))
  let B := AddCommGrpCat.uliftFunctor.{b,max a u r}
  let K := forget₂ (SectionModules.{a} R U) AddCommGrpCat.{max a u r}
  let K' := forget₂ (SectionModules.{max a b} R U) AddCommGrpCat.{max a b u r}
  obtain ⟨e, he, e₀, eδ⟩ := ambientComparisonExact.{a,u,r,b} R U
  obtain ⟨f, hf, f₀, fδ⟩ := forgetComparisonExact.{a,u,r} R U
  obtain ⟨s, hs, s₀, sδ⟩ := abelianAmbientComparisonExact.{a,u,r,b} X U
  obtain ⟨t, ht, t₀, tδ⟩ := forgetComparisonExact.{max a b,u,r} R U
  refine ⟨e, f, s, t, he, hf, hs, ht, ?_⟩
  intro M n
  have rid (n : ℕ) :
      (rightValue D n).map
        ((Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.forgetAbelianComparisonValue.{b,u,r,max a u r} X R).2.hom.app M) =
        𝟙 ((rightValue D n).obj (E.obj (O.obj M))) :=
    (rightValue D n).map_id _
  suffices h : B.map ((f n).hom.app M) ≫ (s n).hom.app (O.obj M) =
      K'.map ((e n).hom.app M) ≫ (t n).hom.app (J.obj M) by
    rw [rid]
    exact h.trans (congrArg (K'.map ((e n).hom.app M) ≫ ·)
      (Category.comp_id ((t n).hom.app (J.obj M))).symm)
  clear rid
  induction n generalizing M with
  | zero =>
    haveI := zero.{a,u,r} R U
    apply (cancel_epi (B.map (K.map ((rightDegreeZeroUnit F).app M)))).mp
    have hF := NatTrans.congr_app f₀ M
    have hS := NatTrans.congr_app s₀ (O.obj M)
    have hE := NatTrans.congr_app e₀ M
    have hT := NatTrans.congr_app t₀ (J.obj M)
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hF hS hE hT
    change _ ≫ B.map ((f 0).hom.app M) ≫ (s 0).hom.app (O.obj M) =
      K'.map (H.map ((rightDegreeZeroUnit F).app M)) ≫
        K'.map ((e 0).hom.app M) ≫ (t 0).hom.app (J.obj M)
    rw [← B.map_comp_assoc, hF, B.map_comp_assoc, hS,
      ← K'.map_comp_assoc, hE, K'.map_comp_assoc, hT]
    simp [abelianCoefficientSectionsIso,
      Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue]
    erw [B.map_id]
    rfl
  | succ n ih =>
    let S := UniversalDeltaFunctors.injectiveSequence M
    let hS := UniversalDeltaFunctors.injectiveSequence_shortExact M
    obtain ⟨hJS, hE⟩ := eδ S hS
    obtain ⟨hOS, hF⟩ := fδ S hS
    obtain ⟨hEOS, hA⟩ := sδ (S.map O) hOS
    obtain ⟨hOJS, hT⟩ := tδ (S.map J) hJS
    have h₁ := hE n
    have h₂ := hF n
    have h₃ := hA n
    have h₄ := hT n
    haveI : Epi (rightBoundary F hS n) := by
      exact UniversalDeltaFunctors.dimensionShift_epi (systemValue.{a} R U)
        (longExact.{a,u,r} R U) (fun I _ n ↦ ClassicalDerivedValues.rightInjectiveVanishing _ _ F I n)
        M n
    let δ := B.map (K.map (rightBoundary F hS n))
    let δ₁ := K'.map (rightBoundary G hJS n)
    let δ₂ := B.map (rightBoundary C hOS n)
    let δ₃ := rightBoundary D hEOS n
    let E₀ := K'.map ((e n).hom.app S.X₃)
    let E₁ := K'.map ((e (n + 1)).hom.app M)
    let F₀ := B.map ((f n).hom.app S.X₃)
    let F₁ := B.map ((f (n + 1)).hom.app M)
    let S₀ := (s n).hom.app (O.obj S.X₃)
    let S₁ := (s (n + 1)).hom.app (O.obj M)
    let T₀ := (t n).hom.app (J.obj S.X₃)
    let T₁ := (t (n + 1)).hom.app (J.obj M)
    have hE' : E₀ ≫ δ₁ = δ ≫ E₁ := by
      have h := congrArg K'.map h₁
      simp only [CategoryTheory.Functor.map_comp] at h
      exact h
    have hF' : F₀ ≫ δ₂ = δ ≫ F₁ := by
      have h := congrArg B.map h₂
      simp only [CategoryTheory.Functor.map_comp] at h
      exact h
    have hS' : S₀ ≫ δ₃ = δ₂ ≫ S₁ := h₃
    have hT' : T₀ ≫ δ₃ = δ₁ ≫ T₁ := h₄
    have hi : F₀ ≫ S₀ = E₀ ≫ T₀ := ih S.X₃
    haveI : Epi δ := inferInstanceAs (Epi (B.map (K.map (rightBoundary F hS n))))
    apply (cancel_epi δ).mp
    calc
      δ ≫ (F₁ ≫ S₁) = (δ ≫ F₁) ≫ S₁ := (Category.assoc _ _ _).symm
      _ = (F₀ ≫ δ₂) ≫ S₁ := congrArg (· ≫ S₁) hF'.symm
      _ = F₀ ≫ (δ₂ ≫ S₁) := Category.assoc _ _ _
      _ = F₀ ≫ (S₀ ≫ δ₃) := congrArg (F₀ ≫ ·) hS'.symm
      _ = (F₀ ≫ S₀) ≫ δ₃ := (Category.assoc _ _ _).symm
      _ = (E₀ ≫ T₀) ≫ δ₃ := congrArg (· ≫ δ₃) hi
      _ = E₀ ≫ (T₀ ≫ δ₃) := Category.assoc _ _ _
      _ = E₀ ≫ (δ₁ ≫ T₁) := congrArg (E₀ ≫ ·) hT'
      _ = (E₀ ≫ δ₁) ≫ T₁ := (Category.assoc _ _ _).symm
      _ = (δ ≫ E₁) ≫ T₁ := congrArg (· ≫ T₁) hE'
      _ = δ ≫ (E₁ ≫ T₁) := Category.assoc _ _ _




section DerivedMaps

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- The map of degree-wise derived functors induced by a transformation. -/
private def derivedValueMap (c : F ⟶ G) (n : ℕ) : rightValue F n ⟶ rightValue G n :=
  whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (whiskerRight c.rightDerivedFunctorPlus (DerivedCategory.Plus.homologyFunctor B (n : ℤ)))

private theorem derivedValueMap_model (c : F ⟶ G)
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i) (n : ℕ) :
    resolutionModelMap F i hi n ≫ (derivedValueMap c n).app M =
      HomologicalComplex.homologyMap ((c.mapHomologicalComplex (.up ℤ)).app I) (n : ℤ) ≫
        resolutionModelMap G i hi n := by
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let S : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let q : S ⟶ K := ObjectProperty.homMk i
  let Q := DerivedCategory.Plus.Q (C := A)
  let Q' := DerivedCategory.Plus.Q (C := B)
  let RF := F.rightDerivedFunctorPlus
  let RG := G.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let α := F.rightDerivedFunctorPlusUnit
  let β := G.rightDerivedFunctorPlusUnit
  let h := (c.mapHomologicalComplex (.up ℤ)).app I
  let θ := DerivedCategory.homologyFunctorFactors B (n : ℤ)
  let t := c.rightDerivedFunctorPlus
  haveI : IsIso (Q.map q) :=
    Localization.inverts Q (CochainComplex.Plus.quasiIso A) q hi
  have e := t.naturality (inv (Q.map q))
  have hc := c.rightDerivedFunctorPlus_fac_app K
  have hθ : HomologicalComplex.homologyMap h (n : ℤ) ≫
      θ.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) =
      θ.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        H.map (Q'.map (c.mapCochainComplexPlus.app K)) :=
    θ.inv.naturality h
  change (θ.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      H.map (α.app K ≫ RF.map (inv (Q.map q)))) ≫ H.map (t.app (Q.obj S)) =
    HomologicalComplex.homologyMap h (n : ℤ) ≫
      (θ.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        H.map (β.app K ≫ RG.map (inv (Q.map q))))
  rw [Category.assoc, ← H.map_comp, Category.assoc, e, ← Category.assoc, hc,
    Category.assoc, H.map_comp, ← Category.assoc, ← hθ, Category.assoc]


private theorem derivedValueMap_zero (c : F ⟶ G) :
    rightDegreeZeroUnit F ≫ derivedValueMap c 0 = c ≫ rightDegreeZeroUnit G := by
  apply NatTrans.ext
  funext M
  let S := (CochainComplex.singleFunctor A 0).obj M
  let f := ((F.mapCochainComplexSingleFunctor 0).inv.app M)
  let g := ((G.mapCochainComplexSingleFunctor 0).inv.app M)
  let k := (c.mapHomologicalComplex (.up ℤ)).app S
  let Q := CochainComplex.singleFunctor B 0
  have hk : f ≫ k = Q.map (c.app M) ≫ g := by
    apply HomologicalComplex.hom_ext
    intro q
    by_cases hq : q = 0
    · subst q
      simp only [f, g, k, HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
      change ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M).f 0 ≫
        c.app (S.X 0) = ((HomologicalComplex.single B (.up ℤ) 0).map (c.app M)).f 0 ≫
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app M).f 0
      simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← c.naturality]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (F.obj M) q hq).eq_of_src _ _
  change (rightDegreeZeroUnit F).app M ≫ (derivedValueMap c 0).app M =
    c.app M ≫ (rightDegreeZeroUnit G).app M
  rw [SheafCohomology.rightDegreeZeroUnit_stalk, Category.assoc,
    derivedValueMap_model c (𝟙 S) (by infer_instance), SheafCohomology.rightDegreeZeroUnit_stalk]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  change (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      HomologicalComplex.homologyMap f 0 ≫ HomologicalComplex.homologyMap k 0 ≫ _ =
    c.app M ≫ (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (G.obj M)).inv ≫
      HomologicalComplex.homologyMap g 0 ≫ _
  rw [← HomologicalComplex.homologyMap_comp_assoc, hk,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_inv_naturality_assoc]

open CategoryTheory.Pretriangulated in
private theorem derivedValueMap_boundary (c : F ⟶ G)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (derivedValueMap c n).app S.X₃ ≫ rightBoundary G hS n =
      rightBoundary F hS n ≫ (derivedValueMap c (n + 1)).app S.X₁ := by
  let T := plusTriangle A hS
  let t := c.rightDerivedFunctorPlus
  let φ : F.rightDerivedFunctorPlus.mapTriangle.obj T ⟶
      G.rightDerivedFunctorPlus.mapTriangle.obj T :=
    { hom₁ := t.app T.obj₁
      hom₂ := t.app T.obj₂
      hom₃ := t.app T.obj₃
      comm₁ := t.naturality T.mor₁
      comm₂ := t.naturality T.mor₂
      comm₃ := by
        dsimp
        simp only [Category.assoc, NatTrans.shift_app_comm t (1 : ℤ) T.obj₁,
          NatTrans.naturality_assoc] }
  exact (DerivedCategory.Plus.homologyFunctor B 0).homologySequenceδ_naturality φ
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)

end DerivedMaps

def coefficientCohomology : coefficientCohomologyType.{a,u,r} := @coefficientCohomologyValue.{a,u,r}

theorem coefficientFlasque : coefficientFlasqueType.{a,u,r} := by
  intro X R U _ M hM n
  exact flasque.{a,u,r} R U _ ((coefficient_lift_flasque.{max u r,u,r,a} X R M).2 hM) n

theorem coefficientZero : coefficientZeroType.{a,u,r} := by
  intro X R U _
  dsimp only
  letI := zero.{a,u,r} R U
  infer_instance

theorem coefficientLongExact : coefficientLongExactType.{a,u,r} := by
  intro X R U _ S hS
  dsimp only
  have hT := (coefficient_lift_original_sheaf_short_exact.{0,u,r,a} X R S).1 hS
  have hF := longExact.{a,u,r} R U
  exact ⟨hT, fun n ↦ ⟨hF.exact₁ hT n, hF.exact₂ hT n, hF.exact₃ hT n⟩, hF.mono_zero hT⟩

/-- The abelian Hom representation on the original site sends a morphism
to the value of that morphism on the original adjunction-unit section. -/
theorem abelianUnit : abelianUnitType.{a,u,r} := by
  intro X U D
  dsimp only
  let R := AdvancedHomologicalAlgebra.SheafTheory.constantIntegerRingSheaf X
  let T := SheafOfModules.toSheaf.{max a u r} R
  let L := originalExtendedUnitOf.{max a r} R U D.overExtension
  let A := originalAbelianUnit.{a,u,r} X U D
  let Γ := abelianSectionsValue.{a,u,r} X (opensEquiv X U)
  let s := originalAbelianUnitSection.{a,u,r} X U D
  letI : T.IsEquivalence := originalIntegerForgetIsEquivalence.{max a r} X
  let E := T.asEquivalence
  let P := Functor.FullyFaithful.ofFullyFaithful T
  let c (F : OriginalAbelianSheaves.{a,u,r} X) : T.obj (E.inverse.obj F) ≅ F := E.counitIso.app F
  let d (F : OriginalAbelianSheaves.{a,u,r} X) :
      (L ⟶ E.inverse.obj F) ≃+ (A ⟶ T.obj (E.inverse.obj F)) :=
    { toEquiv := P.homEquiv
      map_add' := fun _ _ ↦ T.map_add }
  let post (F : OriginalAbelianSheaves.{a,u,r} X) :
      (A ⟶ F) ≃+ (A ⟶ T.obj (E.inverse.obj F)) :=
    { toEquiv := (Iso.refl A).homCongr (c F).symm
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.add_comp] }
  let e (F : OriginalAbelianSheaves.{a,u,r} X) : (A ⟶ F) ≃+ Γ.obj F :=
    (post F).trans ((d F).symm.trans ((D.sectionRepresentation (E.inverse.obj F)).trans
      (Γ.mapIso (c F)).addCommGroupIsoToAddEquiv))
  have he (F : OriginalAbelianSheaves.{a,u,r} X) (f : A ⟶ F) : e F f = Γ.map f s := by
    let g := P.preimage (f ≫ (c F).inv)
    have hg : T.map g ≫ (c F).hom = f := by
      change T.map (P.preimage (f ≫ (c F).inv)) ≫ (c F).hom = f
      rw [P.map_preimage, Category.assoc, (c F).inv_hom_id, Category.comp_id]
    have hf : post F f = f ≫ (c F).inv := by
      simp [post, Iso.homCongr]
    change Γ.map (c F).hom (D.sectionRepresentation (E.inverse.obj F) (P.preimage (post F f))) = _
    rw [hf, D.sectionRepresentation_apply]
    change Γ.map (c F).hom (Γ.map (T.map g) s) = _
    rw [← ConcreteCategory.comp_apply, ← Γ.map_comp, hg]
    rfl
  let E' : preadditiveCoyoneda.obj (op A) ≅ Γ :=
    NatIso.ofComponents (fun F ↦ (e F).toAddCommGrpIso) (by
      intro F G f
      ext g
      change e G (g ≫ f) = Γ.map f (e F g)
      rw [he, he, Γ.map_comp, ConcreteCategory.comp_apply])
  exact ⟨E', he⟩

section RestrictionMaps

variable {A B B' : Type*} [Category* A] [Category* B] [Category* B']
  [Abelian A] [Abelian B] [Abelian B'] [EnoughInjectives A]
  (G : A ⥤ B) (H : B ⥤ B') [G.Additive] [H.Additive] [H.PreservesHomology]

private theorem mapAugmentation_id {M : A} {I : CochainComplex A ℤ}
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) :
    mapAugmentation (𝟭 A) i = i := by
  have h : ((𝟭 A).mapCochainComplexSingleFunctor 0).inv.app M =
      𝟙 ((CochainComplex.singleFunctor A 0).obj M) := by
    ext q
    by_cases hq : q = 0
    · subst q
      simp [Functor.mapCochainComplexSingleFunctor]
    · exact (HomologicalComplex.isZero_single_obj_X _ 0 M q hq).eq_of_src _ _
  unfold mapAugmentation
  rw [h]
  exact Category.id_comp _

/-- Exact postcomposition commutes with the canonical augmented model maps. -/
private theorem exactPostcomposition [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] :
    ∃ e : ∀ n : ℕ, rightValue G n ⋙ H ≅ rightValue (G ⋙ H) n,
      whiskerRight (rightDegreeZeroUnit G) H ≫ (e 0).hom = rightDegreeZeroUnit (G ⋙ H) ∧
      (∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
        (e n).hom.app S.X₃ ≫ rightBoundary (G ⋙ H) hS n =
          H.map (rightBoundary G hS n) ≫ (e (n + 1)).hom.app S.X₁) ∧
      ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
        (∀ q : ℤ, Injective (I.X q)) → ∀ n : ℕ,
          H.map (resolutionModelMap G i hi n) ≫ (e n).hom.app M =
            ((((G.mapHomologicalComplex (.up ℤ)).obj I).sc (n : ℤ)).mapHomologyIso H).inv ≫
              resolutionModelMap (G ⋙ H) i hi n := by
  let c : G ⋙ H ≅ (𝟭 A) ⋙ (G ⋙ H) := Iso.refl _
  obtain ⟨e, he⟩ := compareResolutions G (G ⋙ H) (𝟭 A) H c
    (fun M hM ↦ by letI := hM; exact AcyclicTermComparison.rightAcyclic_of_injective _ _)
  have hz := resolutionComparison_zero G (G ⋙ H) (𝟭 A) H c e he
  have hb := normalizedComparison_boundary G (G ⋙ H) (𝟭 A) H c
    (fun M hM ↦ by letI := hM; exact AcyclicTermComparison.rightAcyclic_of_injective _ _) e he
  refine ⟨e, ?_, ?_, ?_⟩
  · change _ = 𝟙 (G ⋙ H) ≫ rightDegreeZeroUnit (G ⋙ H) at hz
    simpa only [Category.id_comp] using hz
  · exact hb
  intro M I _ i hi hI n
  obtain ⟨hi', h⟩ := he M I i hi hI
  have hn := h n
  simp only [mapAugmentation_id] at hn
  have hh :
      (modelComparison G (G ⋙ H) (𝟭 A) H c I n).hom =
        ((((G.mapHomologicalComplex (.up ℤ)).obj I).sc (n : ℤ)).mapHomologyIso H).inv := by
    have ht : (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I =
        𝟙 ((H.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj I)) := by
      ext q
      rfl
    simp only [modelComparison, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
      Iso.app_hom, ht]
    let K := (G.mapHomologicalComplex (.up ℤ)).obj I
    let K' := (H.mapHomologicalComplex (.up ℤ)).obj K
    let H' := HomologicalComplex.homologyFunctor B' (.up ℤ) (n : ℤ)
    exact (congrArg (fun f ↦ ((K.sc (n : ℤ)).mapHomologyIso H).inv ≫ f)
      (H'.map_id K')).trans (Category.comp_id _)
  rw [hh] at hn
  exact hn

theorem restrictionMap : restrictionMapType.{a,u,r} := by
  intro X R U V f _
  dsimp only
  let G := sectionsValue.{a} R V
  let F := sectionsValue.{a} R U
  let H := restrictSectionScalars.{a} X R f
  let c := restrictSections.{a} X R f
  letI := original_sections_left_exact.{a,u,r} X R V
  obtain ⟨e, hz, hb, he⟩ := exactPostcomposition G H
  let t (n : ℕ) : rightValue F n ⟶ rightValue G n ⋙ H :=
    derivedValueMap c n ≫ (e n).inv
  refine ⟨t, ?_, ?_, ?_⟩
  · change rightDegreeZeroUnit F ≫ (derivedValueMap c 0 ≫ (e 0).inv) = _
    rw [← Category.assoc, derivedValueMap_zero, Category.assoc, ← hz, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · intro S hS n
    apply (cancel_mono ((e (n + 1)).hom.app S.X₁)).mp
    simp only [t, NatTrans.comp_app, Category.assoc]
    rw [← hb S hS n, Iso.inv_hom_id_app_assoc, derivedValueMap_boundary,
      Iso.inv_hom_id_app, Category.comp_id]
  intro M I _ i hi hI n
  have hi' := he M I i hi hI n
  let K := (G.mapHomologicalComplex (.up ℤ)).obj I
  let b := (K.sc (n : ℤ)).mapHomologyIso H
  have h :
      resolutionModelMap (G ⋙ H) i hi n ≫ (e n).inv.app M =
        b.hom ≫ H.map (resolutionModelMap G i hi n) := by
    apply (cancel_epi b.inv).mp
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, ← hi', Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  change resolutionModelMap F i hi n ≫ ((derivedValueMap c n).app M ≫ (e n).inv.app M) = _
  rw [← Category.assoc, derivedValueMap_model, Category.assoc, h]

end RestrictionMaps


section RepresentedBoundary

open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
set_option maxHeartbeats 500000

universe v
variable {A : Type*} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  (P : A) (Γ : A ⥤ AddCommGrpCat.{v}) [Γ.Additive]

private theorem shiftMap_comp_shifted {C B : Type*} [Category* C] [Category* B] [HasShift C ℤ]
    (F : C ⥤ B) [F.ShiftSequence ℤ] {X Y Z : C} {n m k a b c : ℤ}
    (f : ShiftedHom X Y n) (g : ShiftedHom Y Z m)
    (hab : n + a = b) (hbc : m + b = c) (hmn : m + n = k) :
    F.shiftMap (f.comp g hmn) a c (by omega) =
      F.shiftMap f a b hab ≫ F.shiftMap g b c hbc := by
  rw [Functor.shiftMap, Functor.shiftMap, Category.assoc, F.shiftIso_hom_app_comp_shiftMap g n k hmn a b c hab hbc]
  simp only [ShiftedHom.comp, Functor.shiftMap, Functor.map_comp, Category.assoc]

private abbrev dSingle := DerivedCategory.Plus.singleFunctor A 0
private abbrev dIncl := DerivedCategory.Plus.ι (C := A)

private def extInPlus {X Y : A} {n : ℤ} (f : Ext X Y n) :
    ShiftedHom ((dSingle (A := A)).obj X) ((dSingle (A := A)).obj Y) n :=
  (Functor.FullyFaithful.ofFullyFaithful (dIncl (A := A))).preimage
    (f ≫ ((dIncl (A := A)).commShiftIso n).inv.app ((dSingle (A := A)).obj Y))

@[simp]
private lemma extInPlus_map {X Y : A} {n : ℤ} (f : Ext X Y n) :
    (extInPlus f).map (dIncl (A := A)) = f := by
  unfold extInPlus ShiftedHom.map
  rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private lemma incl_shifted_injective {X Y : DerivedCategory.Plus A} {n : ℤ}
    {f g : ShiftedHom X Y n} (h : f.map (dIncl (A := A)) = g.map (dIncl (A := A))) : f = g := by
  apply (dIncl (A := A)).map_injective
  simpa [ShiftedHom.map] using
    congrArg (fun x ↦ x ≫ ((dIncl (A := A)).commShiftIso n).inv.app Y) h

private abbrev derivedSections := Γ.rightDerivedFunctorPlus ⋙
  DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} 0

private def evalExt {M : A} {n : ℕ} (s : Γ.obj P) (f : Ext P M (n : ℤ)) :
    (rightValue Γ n).obj M :=
  (derivedSections Γ).shiftMap (extInPlus f) 0 (n : ℤ) (add_zero _)
    ((rightDegreeZeroUnit Γ).app P s)

private lemma evalExt_boundary (s : Γ.obj P) {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) (f : Ext P S.X₃ (n : ℤ)) :
    evalExt P Γ s (n := n + 1) (ShiftedHom.comp f hS.singleδ (by omega)) =
      rightBoundary Γ hS n (evalExt P Γ s f) := by
  let T := plusTriangle A hS
  have heq : extInPlus (ShiftedHom.comp f hS.singleδ (show 1 + (n : ℤ) = ((n+1 : ℕ) : ℤ) by omega)) =
      (extInPlus f).comp T.mor₃ (show 1 + (n : ℤ) = ((n+1 : ℕ) : ℤ) by omega) := by
    apply incl_shifted_injective
    rw [extInPlus_map, ShiftedHom.map_comp, extInPlus_map]
    have hd : ShiftedHom.map T.mor₃ (dIncl (A := A)) = hS.singleδ := by
      change (hS.singleδ ≫ ((dIncl (A := A)).commShiftIso (1 : ℤ)).inv.app T.obj₁) ≫
        ((dIncl (A := A)).commShiftIso (1 : ℤ)).hom.app T.obj₁ = hS.singleδ
      rw [Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _
    rw [hd]
  have hb : (derivedSections Γ).shiftMap T.mor₃ (n : ℤ) ((n+1 : ℕ) : ℤ) (by omega) =
      rightBoundary Γ hS n := by
    let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} 0
    let R := Γ.rightDerivedFunctorPlus
    change (R ⋙ H).shiftMap T.mor₃ (n : ℤ) ((n+1 : ℕ) : ℤ) (by omega) =
      H.shiftMap (ShiftedHom.map T.mor₃ R) (n : ℤ) ((n+1 : ℕ) : ℤ) (by omega)
    unfold Functor.shiftMap ShiftedHom.map
    simp only [Functor.shiftIso, Functor.ShiftSequence.leftComp_shiftIso, Iso.trans_hom,
      Functor.associator_inv_app, NatTrans.id_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.comp_map, Category.id_comp, Category.assoc, Functor.map_comp]
    rfl
  unfold evalExt
  rw [heq, shiftMap_comp_shifted (derivedSections Γ) _ _ (add_zero _) (by omega), hb]
  rfl

private lemma evalExt_zero (s : Γ.obj P) {M : A} (f : P ⟶ M) :
    evalExt P Γ s (n := 0) (zeroHom f) =
      (rightDegreeZeroUnit Γ).app M (Γ.map f s) := by
  have hf : extInPlus (zeroHom f) = ShiftedHom.mk₀ (0 : ℤ) rfl ((dSingle (A := A)).map f) := by
    apply incl_shifted_injective
    rw [extInPlus_map, ShiftedHom.map_mk₀]
    simp only [zeroHom, ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero',
      eqToIso_refl, Iso.refl_trans]
    rfl
  unfold evalExt
  rw [hf]
  have hz : (derivedSections Γ).shiftMap (ShiftedHom.mk₀ (0 : ℤ) rfl ((dSingle (A := A)).map f))
      0 ((0 : ℕ) : ℤ) (add_zero _) = (rightValue Γ 0).map f := by
    change (derivedSections Γ).shiftMap (ShiftedHom.mk₀ (0 : ℤ) rfl ((dSingle (A := A)).map f))
      0 0 (add_zero _) = _
    simp [Functor.shiftMap, ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero', Functor.shiftIso_zero_hom_app,
      derivedSections, rightValue, ← Functor.map_comp]
    rfl
  rw [hz]
  exact (congr($( (rightDegreeZeroUnit Γ).naturality f ) s)).symm

private lemma chainShift_evaluation {I : CochainComplex A ℤ} (n : ℤ)
    (z : Cocycle ((CochainComplex.singleFunctor A 0).obj P) I n) (s : Γ.obj P)
    (e : HomComplex ((CochainComplex.singleFunctor A 0).obj P) I ≅
      (Γ.mapHomologicalComplex (.up ℤ)).obj I)
    (he : e.hom.f n z.val = Γ.map (Cochain.fromSingleEquiv (zero_add n) z) s) :
    let B := AddCommGrpCat.{v}
    let S := (CochainComplex.singleFunctor B 0).obj (Γ.obj P)
    let D := (Γ.mapHomologicalComplex (.up ℤ)).obj I
    let g : ShiftedHom S D n :=
      (HomologicalComplex.singleMapHomologicalComplex Γ (.up ℤ) 0).inv.app P ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm z) (Γ.mapHomologicalComplex (.up ℤ))
    (HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftMap g 0 n (add_zero n)
        ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (Γ.obj P)).inv s) =
      HomologicalComplex.homologyMap e.hom n
        ((HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z)) := by
  dsimp only
  let B := AddCommGrpCat.{v}
  let S := (CochainComplex.singleFunctor B 0).obj (Γ.obj P)
  let D := (Γ.mapHomologicalComplex (.up ℤ)).obj I
  let J := HomComplex ((CochainComplex.singleFunctor A 0).obj P) I
  let g : ShiftedHom S D n :=
    (HomologicalComplex.singleMapHomologicalComplex Γ (.up ℤ) 0).inv.app P ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm z) (Γ.mapHomologicalComplex (.up ℤ))
  let d := (CochainComplex.shiftShortComplexFunctorIso B n 0 n (add_zero n)).hom.app D
  let E := HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj P) I n
  let a : S.cycles 0 := (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (Γ.obj P)).inv s
  let b : J.cycles n := E.cyclesIso.inv z
  have ha : S.homologyπ 0 a =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (Γ.obj P)).inv s :=
    congr($(HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (.up ℤ) 0 (Γ.obj P)) s)
  have hb : J.homologyπ n b =
      (HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z) :=
    (congr($(E.π_comp_homologyIso_inv) z)).symm
  have hr : ShortComplex.cyclesMap d (HomologicalComplex.cyclesMap g 0 a) =
      HomologicalComplex.cyclesMap e.hom n b := by
    apply (AddCommGrpCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    have h1 := congr($(ShortComplex.cyclesMap_i d) (HomologicalComplex.cyclesMap g 0 a))
    have h2 := congr($(HomologicalComplex.cyclesMap_i g 0) a)
    have h3 := congr($(HomologicalComplex.cyclesMap_i e.hom n) b)
    have h4 := congr($(HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (.up ℤ) 0 (Γ.obj P)) s)
    have h5 := congr($(E.cyclesIso_inv_comp_iCycles) z)
    change D.iCycles n (ShortComplex.cyclesMap d (HomologicalComplex.cyclesMap g 0 a)) =
      D.iCycles n (HomologicalComplex.cyclesMap e.hom n b)
    change D.iCycles n (ShortComplex.cyclesMap d (HomologicalComplex.cyclesMap g 0 a)) =
      d.τ₂ ((D⟦n⟧).iCycles 0 (HomologicalComplex.cyclesMap g 0 a)) at h1
    change (D⟦n⟧).iCycles 0 (HomologicalComplex.cyclesMap g 0 a) =
      g.f 0 (S.iCycles 0 a) at h2
    change D.iCycles n (HomologicalComplex.cyclesMap e.hom n b) =
      e.hom.f n (J.iCycles n b) at h3
    change S.iCycles 0 a = _ at h4
    change J.iCycles n b = z.val at h5
    simp only [h1, h2, h3, h4, h5, he]
    have hg : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (Γ.obj P)).inv ≫
        g.f 0 ≫ d.τ₂ = Γ.map (Cochain.fromSingleEquiv (zero_add n) z) := by
      simp only [g, d, ShiftedHom.map, HomologicalComplex.comp_f,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
        Category.id_comp, Category.comp_id, Iso.inv_hom_id_assoc,
        CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂,
        Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f, Cocycle.rightShift_coe]
      rw [Cochain.rightShift_v _ _ _ _ 0 0 (add_zero 0) n (zero_add n)]
      simp only [Cochain.fromSingleEquiv, Functor.map_comp, Category.assoc]
      simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, D, eqToHom_map]
    exact congr($(hg) s)
  have hh₁ := congr($(HomologicalComplex.homologyπ_naturality g 0) a)
  have hh₂ := congr($(ShortComplex.homologyπ_naturality d) (HomologicalComplex.cyclesMap g 0 a))
  have hh₃ := congr($(HomologicalComplex.homologyπ_naturality e.hom n) b)
  change HomologicalComplex.homologyMap g 0 (S.homologyπ 0 a) =
    (D⟦n⟧).homologyπ 0 (HomologicalComplex.cyclesMap g 0 a) at hh₁
  change ShortComplex.homologyMap d ((D⟦n⟧).homologyπ 0 (HomologicalComplex.cyclesMap g 0 a)) =
    D.homologyπ n (ShortComplex.cyclesMap d (HomologicalComplex.cyclesMap g 0 a)) at hh₂
  change HomologicalComplex.homologyMap e.hom n (J.homologyπ n b) =
    D.homologyπ n (HomologicalComplex.cyclesMap e.hom n b) at hh₃
  simp only [Functor.shiftMap, Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    CochainComplex.ShiftSequence.shiftIso_hom_app, ← ha, ← hb]
  exact (congrArg (fun t ↦ ShortComplex.homologyMap d t) hh₁).trans (hh₂.trans
    ((congrArg (fun t ↦ D.homologyπ n t) hr).trans hh₃.symm))

private lemma shiftMap_comp_functor {C D B : Type*} [Category* C] [Category* D] [Category* B]
    [HasShift C ℤ] [HasShift D ℤ] (R : C ⥤ D) [R.CommShift ℤ]
    (H : D ⥤ B) [H.ShiftSequence ℤ] {X Y : C} {n a b : ℤ}
    (f : ShiftedHom X Y n) (h : n + a = b) :
    (R ⋙ H).shiftMap f a b h = H.shiftMap (f.map R) a b h := by
  unfold Functor.shiftMap ShiftedHom.map
  simp only [Functor.shiftIso, Functor.ShiftSequence.leftComp_shiftIso, Iso.trans_hom,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.comp_map,
    Category.id_comp, Category.assoc, Functor.map_comp]
  change (H.shift a).map (R.map f) ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

private lemma shiftedMap_Qplus {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex.Plus C} {n : ℤ} (f : ShiftedHom K L n) :
    (f.map (DerivedCategory.Plus.Q (C := C))).map DerivedCategory.Plus.ι =
      (f.map (CochainComplex.Plus.ι C)).map DerivedCategory.Q := by
  rw [← ShiftedHom.comp_map, ← ShiftedHom.comp_map]
  have h := ShiftedHom.map_naturality_1 f (DerivedCategory.Plus.QCompιIso C)
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at h
  have e : (DerivedCategory.Plus.QCompιIso C).hom.app L = 𝟙 (DerivedCategory.Q.obj L.obj) := rfl
  have e' : (DerivedCategory.Plus.QCompιIso C).inv.app K = 𝟙 (DerivedCategory.Q.obj K.obj) := rfl
  rw [e, e'] at h
  let x := f.map (DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι)
  let y := f.map (CochainComplex.Plus.ι C ⋙ DerivedCategory.Q)
  let Z := DerivedCategory.Q.obj L.obj
  have ei := (CategoryTheory.shiftFunctor (DerivedCategory C) n).map_id Z
  change (𝟙 (DerivedCategory.Q.obj K.obj) ≫
    (x ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) n).map (𝟙 Z))) = y at h
  erw [ei, Category.comp_id, Category.id_comp] at h
  exact h

private lemma shiftedMap_complexPlus {K L : CochainComplex.Plus A} {n : ℤ} (f : ShiftedHom K L n) :
    (f.map Γ.mapCochainComplexPlus).map (CochainComplex.Plus.ι AddCommGrpCat.{v}) =
      (f.map (CochainComplex.Plus.ι A)).map (Γ.mapHomologicalComplex (.up ℤ)) := by
  rw [← ShiftedHom.comp_map, ← ShiftedHom.comp_map]
  simpa [Functor.mapCochainComplexPlusCompι, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Functor.map_id, Category.comp_id] using
    (ShiftedHom.map_naturality_1 f Γ.mapCochainComplexPlusCompι)

private def complexShiftInPlus {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex.Plus C} {n : ℤ} (f : ShiftedHom K.obj L.obj n) : ShiftedHom K L n :=
  ObjectProperty.homMk (f ≫ ((CochainComplex.Plus.ι C).commShiftIso n).inv.app L)

private lemma complexShiftInPlus_map {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex.Plus C} {n : ℤ} (f : ShiftedHom K.obj L.obj n) :
    (complexShiftInPlus f).map (CochainComplex.Plus.ι C) = f := by
  change (f ≫ ((CochainComplex.Plus.ι C).commShiftIso n).inv.app L) ≫
    ((CochainComplex.Plus.ι C).commShiftIso n).hom.app L = f
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private lemma plus_shiftMap_Q {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex.Plus C} {n a b : ℤ} (f : ShiftedHom K L n) (h : n + a = b) :
    (DerivedCategory.Plus.homologyFunctor C 0).shiftMap
      (f.map (DerivedCategory.Plus.Q (C := C))) a b h =
    (DerivedCategory.homologyFunctorFactors C a).hom.app K.obj ≫
      (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
        (f.map (CochainComplex.Plus.ι C)) a b h ≫
      (DerivedCategory.homologyFunctorFactors C b).inv.app L.obj := by
  change (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor C 0).shiftMap _ _ _ _ = _
  rw [shiftMap_comp_functor, shiftedMap_Qplus,
    DerivedCategory.shiftMap_homologyFunctor_map_Q _ _ _ h]
  rfl

private lemma extInPlus_class {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i)
    {n : ℤ} (z : Cocycle ((CochainComplex.singleFunctor A 0).obj P) I n) :
    let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
    let S (N : A) : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj N, 0, inferInstance⟩
    let q : S M ⟶ K := ObjectProperty.homMk i
    let f : ShiftedHom (S P) K n := complexShiftInPlus (Cocycle.equivHomShift.symm z)
    haveI : IsIso (DerivedCategory.Plus.Q.map q) :=
      Localization.inverts _ (CochainComplex.Plus.quasiIso A) q hi
    extInPlus (injectiveClassMap P M I i hi n (CohomologyClass.mk z)) =
      (f.map DerivedCategory.Plus.Q).comp (ShiftedHom.mk₀ 0 rfl (inv (DerivedCategory.Plus.Q.map q))) (zero_add n) := by
  dsimp only
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let S (N : A) : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj N, 0, inferInstance⟩
  let q : S M ⟶ K := ObjectProperty.homMk i
  let f : ShiftedHom (S P) K n := complexShiftInPlus (Cocycle.equivHomShift.symm z)
  haveI : IsIso (DerivedCategory.Plus.Q.map q) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso A) q hi
  haveI : QuasiIso i := hi
  change _ = (f.map DerivedCategory.Plus.Q).comp _ _
  apply incl_shifted_injective
  rw [extInPlus_map, ShiftedHom.map_comp, shiftedMap_Qplus, complexShiftInPlus_map,
    ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀]
  have hq : dIncl.map (inv (DerivedCategory.Plus.Q.map q)) = inv (DerivedCategory.Q.map i) := by
    exact Functor.map_inv _ _
  rw [hq]
  exact congrArg (fun g ↦ g ≫ (CategoryTheory.shiftFunctor _ n).map (inv (DerivedCategory.Q.map i)))
    (ExtShiftedHom.classToDerived_mk z)

private lemma evalExt_model
    (hunit : ∀ M : A, (rightDegreeZeroUnit Γ).app M =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) 0).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℤ) 0).app M) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (Γ.obj M)).inv ≫
      resolutionModelMap Γ (𝟙 ((CochainComplex.singleFunctor A 0).obj M))
        (by infer_instance) 0)
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i)
    (n : ℕ) (z : Cocycle ((CochainComplex.singleFunctor A 0).obj P) I (n : ℤ)) (s : Γ.obj P)
    (e : HomComplex ((CochainComplex.singleFunctor A 0).obj P) I ≅
      (Γ.mapHomologicalComplex (.up ℤ)).obj I)
    (he : e.hom.f (n : ℤ) z.val = Γ.map (Cochain.fromSingleEquiv (zero_add (n : ℤ)) z) s) :
    evalExt P Γ s (injectiveClassMap P M I i hi (n : ℤ) (CohomologyClass.mk z)) =
      resolutionModelMap Γ i hi n (HomologicalComplex.homologyMap e.hom (n : ℤ)
        ((HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm (CohomologyClass.mk z))) := by
  let B := AddCommGrpCat.{v}
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let L (T : A) : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj T, 0, inferInstance⟩
  let S : CochainComplex.Plus B := ⟨(CochainComplex.singleFunctor B 0).obj (Γ.obj P), 0, inferInstance⟩
  let q : L M ⟶ K := ObjectProperty.homMk i
  let f : ShiftedHom (L P) K (n : ℤ) := complexShiftInPlus (Cocycle.equivHomShift.symm z)
  let QA := DerivedCategory.Plus.Q (C := A)
  let QB := DerivedCategory.Plus.Q (C := B)
  let H0 := DerivedCategory.Plus.homologyFunctor B 0
  let Hn := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let F := Γ.mapCochainComplexPlus
  let η := Γ.rightDerivedFunctorPlusUnit
  let R := Γ.rightDerivedFunctorPlus
  let β := DerivedCategory.homologyFunctorFactors B
  let b : S ⟶ F.obj (L P) :=
    ObjectProperty.homMk ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℤ) 0).inv.app P)
  let c := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (Γ.obj P)
  haveI : IsIso (QA.map q) := Localization.inverts QA (CochainComplex.Plus.quasiIso A) q hi
  have hmodel : resolutionModelMap Γ i hi n =
      (β (n : ℤ)).inv.app (F.obj K).obj ≫ Hn.map (η.app K ≫ R.map (inv (QA.map q))) := rfl
  have hunit' : (rightDegreeZeroUnit Γ).app P =
      c.inv ≫ (β 0).inv.app S.obj ≫ H0.map (QB.map b) ≫ H0.map (η.app (L P)) := by
    rw [hunit]
    have hh : resolutionModelMap Γ (𝟙 (L P).obj) (by infer_instance) 0 =
        (β 0).inv.app (F.obj (L P)).obj ≫ H0.map (η.app (L P)) := by
      change (β 0).inv.app (F.obj (L P)).obj ≫ H0.map
        (η.app (L P) ≫ R.map (inv (QA.map (𝟙 (L P))))) = _
      have hi : inv (QA.map (𝟙 (L P))) = 𝟙 (QA.obj (L P)) := by
        calc
          _ = QA.map (inv (𝟙 (L P))) := (Functor.map_inv QA (𝟙 (L P))).symm
          _ = QA.map (𝟙 (L P)) := congrArg QA.map IsIso.inv_id
          _ = _ := QA.map_id _
      rw [hi]
      have hr : R.map (𝟙 (QA.obj (L P))) = 𝟙 (R.obj (QA.obj (L P))) := R.map_id _
      rw [hr]
      erw [Category.comp_id]
    rw [hh]
    have hb := (β 0).inv.naturality b.hom
    change HomologicalComplex.homologyMap b.hom 0 ≫ (β 0).inv.app (F.obj (L P)).obj =
      (β 0).inv.app S.obj ≫ H0.map (QB.map b) at hb
    change (c.inv ≫ HomologicalComplex.homologyMap b.hom 0) ≫
      (β 0).inv.app (F.obj (L P)).obj ≫ H0.map (η.app (L P)) = _
    simpa only [Category.assoc] using
      congrArg (fun t ↦ c.inv ≫ t) ((reassoc_of% hb) (H0.map (η.app (L P))))
  have hnat := congrArg (fun g : ShiftedHom (QB.obj (F.obj (L P))) (R.obj (QA.obj K)) (n : ℤ) ↦
    H0.shiftMap g 0 (n : ℤ) (add_zero _)) (ShiftedHom.map_naturality f η)
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, Functor.shiftMap_comp, Functor.shiftMap_comp',
    ShiftedHom.comp_map, ShiftedHom.comp_map] at hnat
  change H0.shiftMap ((f.map F).map QB) 0 (n : ℤ) (add_zero _) ≫ Hn.map (η.app K) =
      H0.map (η.app (L P)) ≫ H0.shiftMap ((f.map QA).map R) 0 (n : ℤ) (add_zero _) at hnat
  have hex := extInPlus_class P i hi z
  change extInPlus (injectiveClassMap P M I i hi (n : ℤ) (CohomologyClass.mk z)) =
    (f.map QA).comp (ShiftedHom.mk₀ 0 rfl (inv (QA.map q))) (zero_add _) at hex
  unfold evalExt
  rw [hex, shiftMap_comp_functor, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀, Functor.shiftMap_comp]
  have hcat : (rightDegreeZeroUnit Γ).app P ≫
        (H0.shiftMap ((f.map QA).map R) 0 (n : ℤ) (add_zero _) ≫ Hn.map (R.map (inv (QA.map q)))) =
      c.inv ≫ (β 0).inv.app S.obj ≫ H0.shiftMap
        (ShiftedHom.map (b ≫ f.map F : ShiftedHom S (F.obj K) (n : ℤ)) QB) 0 (n : ℤ) (add_zero _) ≫
        Hn.map (η.app K ≫ R.map (inv (QA.map q))) := by
    simp only [hunit', Category.assoc, ← reassoc_of% hnat]
    rw [← Functor.map_comp]
    have hcomp : H0.shiftMap (ShiftedHom.map (b ≫ f.map F : ShiftedHom S (F.obj K) (n : ℤ)) QB)
        0 (n : ℤ) (add_zero _) =
      H0.map (QB.map b) ≫ H0.shiftMap ((f.map F).map QB) 0 (n : ℤ) (add_zero _) := by
      rw [← ShiftedHom.mk₀_comp 0 rfl b, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
        ShiftedHom.mk₀_comp, Functor.shiftMap_comp']
      rfl
    rw [hcomp, Category.assoc]
  have hchain : ShiftedHom.map (b ≫ f.map F : ShiftedHom S (F.obj K) (n : ℤ)) (CochainComplex.Plus.ι B) =
      b.hom ≫ ShiftedHom.map (Cocycle.equivHomShift.symm z) (Γ.mapHomologicalComplex (.up ℤ)) := by
    rw [← ShiftedHom.mk₀_comp 0 rfl b, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
      ShiftedHom.mk₀_comp, shiftedMap_complexPlus, complexShiftInPlus_map]
    rfl
  rw [plus_shiftMap_Q _ (add_zero _), hchain, Category.assoc, Iso.inv_hom_id_app_assoc] at hcat
  rw [hmodel]
  have hchainEval : (HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftMap
      (b.hom ≫ ShiftedHom.map (Cocycle.equivHomShift.symm z) (Γ.mapHomologicalComplex (.up ℤ)))
      0 (n : ℤ) (add_zero _) (c.inv s) = _ :=
    chainShift_evaluation P Γ (n : ℤ) z s e he
  have happly := congr($(hcat) s)
  simp only [ConcreteCategory.comp_apply] at happly ⊢
  erw [hchainEval] at happly
  exact happly

private theorem representedExt_laws (s : Γ.obj P)
    (E : ∀ (M : A) (n : ℕ), (rightValue Γ n).obj M ≃+ Ext P M (n : ℤ))
    (model : ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
        (∀ q : ℤ, Injective (I.X q)) →
        let L := (CochainComplex.singleFunctor A 0).obj P
        ∃ c : HomComplex L I ≅ ((Γ.mapHomologicalComplex (.up ℤ)).obj I),
          (∀ (q : ℤ) (f : Cochain L I q),
            c.hom.f q f = Γ.map (Cochain.fromSingleEquiv (zero_add q) f) s) ∧
          ∀ (n : ℕ) (x : CohomologyClass L I (n : ℤ)),
            E M n (resolutionModelMap Γ i hi n
              (HomologicalComplex.homologyMap c.hom (n : ℤ)
                ((HomComplex.homologyAddEquiv L I (n : ℤ)).symm x))) =
              injectiveClassMap P M I i hi (n : ℤ) x) :
    (∀ (M : A) (f : P ⟶ M),
      E M 0 ((rightDegreeZeroUnit Γ).app M (Γ.map f s)) = zeroHom f) ∧
    (∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ) (x : (rightValue Γ n).obj S.X₃),
      E S.X₁ (n + 1) (rightBoundary Γ hS n x) =
        ShiftedHom.comp (E S.X₃ n x) hS.singleδ (by omega)) := by
  have hEval (M : A) (n : ℕ) (x : (rightValue Γ n).obj M) : evalExt P Γ s (E M n x) = x := by
    obtain ⟨I, i, _, hi, hI, hB⟩ :=
      InjectiveComplexReplacement.replacement A ((CochainComplex.singleFunctor A 0).obj M) 0 inferInstance
    letI : I.IsStrictlyGE 0 := hB
    haveI := SheafCohomology.resolutionModelMap_isIso Γ i hi (fun q ↦ by
      letI := hI q
      exact AcyclicTermComparison.rightAcyclic_of_injective Γ _) n
    obtain ⟨c, hc, hm⟩ := model M I i hi hI
    let L := (CochainComplex.singleFunctor A 0).obj P
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) (n : ℤ)
    let a : CohomologyClass L I (n : ℤ) ≃+ (rightValue Γ n).obj M :=
      (HomComplex.homologyAddEquiv L I (n : ℤ)).symm.trans
        ((H.mapIso c).addCommGroupIsoToAddEquiv.trans
          (asIso (resolutionModelMap Γ i hi n)).addCommGroupIsoToAddEquiv)
    obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (a.symm x)
    have hx : a (CohomologyClass.mk z) = x := by rw [hz, AddEquiv.apply_symm_apply]
    have hev := evalExt_model P Γ (SheafCohomology.rightDegreeZeroUnit_stalk Γ)
      i hi n z s c (hc _ z.val)
    rw [← hx]
    have hcat := hm n (CohomologyClass.mk z)
    change E M n (a (CohomologyClass.mk z)) = _ at hcat
    rw [hcat]
    exact hev
  have hinv (M : A) (n : ℕ) (y : Ext P M (n : ℤ)) : E M n (evalExt P Γ s y) = y := by
    have h := hEval M n ((E M n).symm y)
    rw [AddEquiv.apply_symm_apply] at h
    rw [h, AddEquiv.apply_symm_apply]
  constructor
  · intro M f
    rw [← evalExt_zero P Γ s f, hinv]
  · intro S hS n x
    rw [← hinv S.X₁ (n + 1) (ShiftedHom.comp (E S.X₃ n x) hS.singleδ (by omega))] 
    congr 1
    rw [evalExt_boundary P Γ s hS n, hEval]

end RepresentedBoundary

section ExtComparison

open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
open private homComplexPostcomp homologyAddEquiv_postcomp_mk
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology

universe v
variable {A : Type*} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  (P : A) (Γ : A ⥤ AddCommGrpCat.{v}) [Γ.Additive]
  (e : preadditiveCoyoneda.obj (op P) ≅ Γ)

private abbrev degreeZeroComplex := (CochainComplex.singleFunctor A 0).obj P

local notation "L" => degreeZeroComplex P

/-- A cocycle out of a stalk is evaluated by the additive representation of sections. -/
private def evaluatedHomComplex (I : CochainComplex A ℤ) :
    HomComplex L I ≅ (Γ.mapHomologicalComplex (.up ℤ)).obj I := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦
    ((Cochain.fromSingleEquiv (zero_add q) : Cochain L I q ≃+ (P ⟶ I.X q)).trans
      (e.app (I.X q)).addCommGroupIsoToAddEquiv).toAddCommGrpIso) ?_
  intro q r h
  have hr : r = q + 1 := h.symm
  subst r
  ext z
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  change Γ.map (I.d q (q + 1)) (e.hom.app (I.X q)
    (Cochain.fromSingleEquiv (zero_add q) (Cochain.fromSingleMk f (zero_add q)))) =
    e.hom.app (I.X (q + 1)) (Cochain.fromSingleEquiv (zero_add (q + 1))
      (δ q (q + 1) (Cochain.fromSingleMk f (zero_add q))))
  rw [Cochain.δ_fromSingleMk f (zero_add q) (q + 1) (q + 1) (zero_add (q + 1))]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact congr($(e.hom.naturality (I.d q (q + 1))) f).symm

private lemma evaluatedHomComplex_naturality {I J : CochainComplex A ℤ} (g : I ⟶ J) :
    (evaluatedHomComplex P Γ e I).hom ≫ (Γ.mapHomologicalComplex (.up ℤ)).map g =
    homComplexPostcomp L g ≫ (evaluatedHomComplex P Γ e J).hom := by
  ext q z
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  change Γ.map (g.f q) (e.hom.app (I.X q)
    (Cochain.fromSingleEquiv (zero_add q) (Cochain.fromSingleMk f (zero_add q)))) =
    e.hom.app (J.X q) (Cochain.fromSingleEquiv (zero_add q)
      ((Cochain.fromSingleMk f (zero_add q)).comp (Cochain.ofHom g) (add_zero q)))
  rw [← Cochain.fromSingleMk_postcomp f (zero_add q) g]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact congr($(e.hom.naturality (g.f q)) f).symm

local notation "S" => CochainComplex.singleFunctor A 0

/-- Cohomology of the represented sections on the chosen injective model. -/
private def sectionModelEquiv {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (S).obj M ⟶ I) (hi : QuasiIso i) (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
    CohomologyClass L I (n : ℤ) ≃+ (rightValue Γ n).obj M := by
  letI := SheafCohomology.resolutionModelMap_isIso Γ i hi
    (fun q ↦ by letI := hI q; exact AcyclicTermComparison.rightAcyclic_of_injective Γ _) n
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) (n : ℤ)
  exact (HomComplex.homologyAddEquiv L I (n : ℤ)).symm.trans
    ((H.mapIso (evaluatedHomComplex P Γ e I)).addCommGroupIsoToAddEquiv.trans
      (asIso (resolutionModelMap Γ i hi n)).addCommGroupIsoToAddEquiv)

private theorem sectionModelEquiv_map {M N : A}
    {I J : CochainComplex A ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : (S).obj M ⟶ I) (hi : QuasiIso i) (hI : ∀ q, Injective (I.X q))
    (j : (S).obj N ⟶ J) (hj : QuasiIso j) (hJ : ∀ q, Injective (J.X q))
    (f : M ⟶ N) (g : I ⟶ J) (hg : i ≫ g = (S).map f ≫ j)
    (n : ℕ) (z : Cocycle L I (n : ℤ)) :
    (rightValue Γ n).map f (sectionModelEquiv P Γ e i hi hI n (CohomologyClass.mk z)) =
      sectionModelEquiv P Γ e j hj hJ n (CohomologyClass.mk (z.postcomp g)) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) (n : ℤ)
  let C := evaluatedHomComplex P Γ e I
  let D := evaluatedHomComplex P Γ e J
  let a := (HomComplex.homologyAddEquiv L I (n : ℤ)).symm (CohomologyClass.mk z)
  have h := SheafCohomology.resolutionModelMap_naturality Γ i hi j hj f g
    (congrArg DerivedCategory.Q.map hg) n
  have hc := congrArg H.map (evaluatedHomComplex_naturality P Γ e g)
  rw [H.map_comp, H.map_comp] at hc
  have hz := homologyAddEquiv_postcomp_mk L g (n : ℤ) z
  change (HomComplex.homologyAddEquiv L J (n : ℤ)) (H.map (homComplexPostcomp L g) a) =
    CohomologyClass.mk (z.postcomp g) at hz
  change (rightValue Γ n).map f (resolutionModelMap Γ i hi n (H.map C.hom a)) =
    resolutionModelMap Γ j hj n (H.map D.hom
      ((HomComplex.homologyAddEquiv L J (n : ℤ)).symm (CohomologyClass.mk (z.postcomp g))))
  rw [← hz, AddEquiv.symm_apply_apply]
  have hh : H.map C.hom ≫ resolutionModelMap Γ i hi n ≫ (rightValue Γ n).map f =
      (H.map (homComplexPostcomp L g) ≫ H.map D.hom) ≫ resolutionModelMap Γ j hj n := by
    rw [h, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ resolutionModelMap Γ j hj n) hc
  exact congr($(hh) a)

private lemma injectiveClassMap_map {M N : A} {I J : CochainComplex A ℤ}
    (i : (S).obj M ⟶ I) (hi : QuasiIso i) (j : (S).obj N ⟶ J) (hj : QuasiIso j)
    (f : M ⟶ N) (g : I ⟶ J) (hg : i ≫ g = (S).map f ≫ j)
    (n : ℕ) (z : Cocycle L I (n : ℤ)) :
    injectiveClassMap P N J j hj (n : ℤ) (CohomologyClass.mk (z.postcomp g)) =
      extMap (𝟙 P) f (n : ℤ) (injectiveClassMap P M I i hi (n : ℤ) (CohomologyClass.mk z)) := by
  have hz : z.precomp ((S).map (𝟙 P)) = z := by
    rw [CategoryTheory.Functor.map_id]
    exact Cocycle.ext (Cochain.id_comp _)
  simpa only [hz] using ExtShiftedHom.injective_natural A P P M N I J i j hi hj
    (𝟙 P) f g ⟨Homotopy.ofEq hg⟩ (n : ℤ) z

private theorem representedSectionsExt :
    ∃ E : ∀ (M : A) (n : ℕ), (rightValue Γ n).obj M ≃+ Ext P M (n : ℤ),
      (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (rightValue Γ n).obj M),
        E N n ((rightValue Γ n).map f x) = extMap (𝟙 P) f (n : ℤ) (E M n x)) ∧
      ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
        (i : (S).obj M ⟶ I) (hi : QuasiIso i) (hI : ∀ q, Injective (I.X q)) (n : ℕ)
        (x : CohomologyClass L I (n : ℤ)),
        E M n (sectionModelEquiv P Γ e i hi hI n x) = injectiveClassMap P M I i hi (n : ℤ) x := by
  choose K k hkmono hkq hkI hkbound using fun M : A ↦
    InjectiveComplexReplacement.replacement _ ((S).obj M) 0 inferInstance
  letI (M : A) : (K M).IsStrictlyGE 0 := hkbound M
  let a (M : A) (n : ℕ) := sectionModelEquiv P Γ e (k M) (hkq M) (hkI M) n
  let b (M : A) (n : ℕ) :
      CohomologyClass L (K M) (n : ℤ) ≃+ Ext P M (n : ℤ) :=
    (HomComplex.homologyAddEquiv L (K M) (n : ℤ)).symm.trans
      (Classical.choose (ExtShiftedHom.injective_comparison A P M (K M) (k M) (hkq M)
        ⟨0, fun t ht ↦ (K M).isZero_of_isStrictlyGE 0 t ht⟩ (hkI M) (n : ℤ)))
  have hb (M : A) (n : ℕ) (x : CohomologyClass L (K M) (n : ℤ)) :
      b M n x = injectiveClassMap P M (K M) (k M) (hkq M) (n : ℤ) x := by
    exact Classical.choose_spec (ExtShiftedHom.injective_comparison A P M (K M) (k M) (hkq M)
      ⟨0, fun t ht ↦ (K M).isZero_of_isStrictlyGE 0 t ht⟩ (hkI M) (n : ℤ)) x
  let E (M : A) (n : ℕ) := (a M n).symm.trans (b M n)
  have hE (M : A) (n : ℕ) (z : Cocycle L (K M) (n : ℤ)) :
      E M n (a M n (CohomologyClass.mk z)) =
        injectiveClassMap P M (K M) (k M) (hkq M) (n : ℤ) (CohomologyClass.mk z) := by
    change b M n ((a M n).symm (a M n (CohomologyClass.mk z))) = _
    rw [AddEquiv.symm_apply_apply, hb]
  have lift {M N : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
      (f : M ⟶ N) (i : (S).obj N ⟶ I) (hI : ∀ q, Injective (I.X q)) :
      ∃ g : K M ⟶ I, k M ≫ g = (S).map f ≫ i := by
    letI : Mono (k M) := HomologicalComplex.mono_of_mono_f _ (hkmono M)
    letI : QuasiIso (k M) := hkq M
    exact SheafCohomology.injectiveResolutionLift (k M) ((S).map f ≫ i) hI
  refine ⟨E, ?_, ?_⟩
  · intro M N f n x
    obtain ⟨g, hg⟩ := lift f (k N) (hkI N)
    obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective ((a M n).symm x)
    have hx : a M n (CohomologyClass.mk z) = x := by rw [hz, AddEquiv.apply_symm_apply]
    rw [← hx, hE]
    have hm := sectionModelEquiv_map P Γ e (k M) (hkq M) (hkI M)
      (k N) (hkq N) (hkI N) f g hg n z
    change (rightValue Γ n).map f (a M n (CohomologyClass.mk z)) =
        a N n (CohomologyClass.mk (z.postcomp g)) at hm
    rw [hm, hE]
    exact injectiveClassMap_map P (k M) (hkq M) (k N) (hkq N) f g hg n z
  · intro M I _ i hi hI n x
    obtain ⟨g, hg⟩ := lift (𝟙 M) i hI
    let C := sectionModelEquiv P Γ e i hi hI n
    obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective ((a M n).symm (C x))
    have hm := sectionModelEquiv_map P Γ e (k M) (hkq M) (hkI M) i hi hI (𝟙 M) g hg n z
    change (rightValue Γ n).map (𝟙 M) (a M n (CohomologyClass.mk z)) =
      C (CohomologyClass.mk (z.postcomp g)) at hm
    rw [CategoryTheory.Functor.map_id, hz, AddEquiv.apply_symm_apply] at hm
    have hx : x = CohomologyClass.mk (z.postcomp g) := C.injective hm
    change E M n (C x) = _
    rw [hx, ← hm]
    change E M n (C x) = _
    have hh : a M n (CohomologyClass.mk z) = C x := by rw [hz, AddEquiv.apply_symm_apply]
    rw [← hh, hE]
    have h := injectiveClassMap_map P (k M) (hkq M) i hi (𝟙 M) g hg n z
    simpa only [extMap, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm



theorem abelianExt : abelianExtType.{a,u,r} := by
  intro X U D _
  dsimp only
  let P := originalAbelianUnit.{a,u,r} X U D
  let Γ := abelianSectionsValue.{a,u,r} X (opensEquiv X U)
  obtain ⟨c, hc⟩ := abelianUnit.{a,u,r} X U D
  obtain ⟨E, hE, hModel⟩ := representedSectionsExt P Γ c
  obtain ⟨hz, hd⟩ := representedExt_laws P Γ (originalAbelianUnitSection.{a,u,r} X U D) E
    (fun M I _ i hi hI ↦ ⟨evaluatedHomComplex P Γ c I, fun q f ↦ hc _ _, hModel M I i hi hI⟩)
  refine ⟨E, hE, hz, hd, ?_⟩
  intro M I _ i hi hI
  exact ⟨evaluatedHomComplex P Γ c I, fun q f ↦ hc _ _, hModel M I i hi hI⟩

end ExtComparison


section AbelianExtSiteComparison
open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
set_option maxHeartbeats 600000

section Exact
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

local notation "SA" => CochainComplex.singleFunctor A 0
local notation "SB" => CochainComplex.singleFunctor B 0

private def transportedCocycle {P : A} {P' : B} (e : P' ⟶ F.obj P)
    {I : CochainComplex A ℤ} {n : ℤ} (z : Cocycle ((SA).obj P) I n) :
    Cocycle ((SB).obj P') ((F.mapHomologicalComplex (.up ℤ)).obj I) n :=
  Cocycle.equivHomShift
    ((SB).map e ≫ (F.mapCochainComplexSingleFunctor 0).inv.app P ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm z) (F.mapHomologicalComplex (.up ℤ)))

private theorem transportExt_injectiveClass {P M : A} {P' : B} (e : P' ⟶ F.obj P)
    {I : CochainComplex A ℤ} (i : (SA).obj M ⟶ I) (hi : QuasiIso i)
    (hFi : QuasiIso (mapAugmentation F i)) {n : ℤ} (z : Cocycle ((SA).obj P) I n) :
    extTransportValue F e (injectiveClassMap P M I i hi n (CohomologyClass.mk z)) =
      injectiveClassMap P' (F.obj M) ((F.mapHomologicalComplex (.up ℤ)).obj I)
        (mapAugmentation F i) hFi n (CohomologyClass.mk (transportedCocycle F e z)) := by
  let QA := DerivedCategory.Q (C := A)
  let QB := DerivedCategory.Q (C := B)
  let J := F.mapHomologicalComplex (.up ℤ)
  let D := F.mapDerivedCategory
  let c := F.mapDerivedCategoryFactors
  let b := F.mapDerivedCategorySingleFunctor 0
  let s := F.mapCochainComplexSingleFunctor 0
  let g : ShiftedHom ((SA).obj P) I n := Cocycle.equivHomShift.symm z
  letI := hi
  letI := hFi
  have hk (M : A) : b.inv.app M ≫ c.hom.app ((SA).obj M) = QB.map (s.inv.app M) :=
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app M
  have hq : QB.map (mapAugmentation F i) = b.inv.app M ≫ D.map (QA.map i) ≫ c.hom.app I := by
    unfold mapAugmentation
    rw [Functor.map_comp]
    have h := c.hom.naturality i
    change D.map (QA.map i) ≫ c.hom.app I = c.hom.app ((SA).obj M) ≫ QB.map (J.map i) at h
    rw [h, ← Category.assoc, hk]
  have hq' : D.map (inv (QA.map i)) ≫ b.hom.app M =
      c.hom.app I ≫ inv (QB.map (mapAugmentation F i)) := by
    apply (cancel_mono (QB.map (mapAugmentation F i))).mp
    calc
      _ = D.map (inv (QA.map i)) ≫ b.hom.app M ≫
          b.inv.app M ≫ D.map (QA.map i) ≫ c.hom.app I := by simp only [Category.assoc, hq]
      _ = (c.hom.app I ≫ inv (QB.map (mapAugmentation F i))) ≫ QB.map (mapAugmentation F i) := by
        rw [Iso.hom_inv_id_app_assoc, ← D.map_comp_assoc, IsIso.inv_hom_id]
        simp
  have hnat := ShiftedHom.map_naturality g c.hom
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map, ShiftedHom.comp_map] at hnat
  unfold extTransportValue injectiveClassMap
  rw [ExtShiftedHom.classToDerived_mk, ExtShiftedHom.classToDerived_mk]
  change _ = ShiftedHom.map (Cocycle.equivHomShift.symm (transportedCocycle F e z)) QB ≫ _
  rw [transportedCocycle, AddEquiv.symm_apply_apply]
  have hn :
      ShiftedHom.map (g.map QA ≫ (CategoryTheory.shiftFunctor _ n).map (inv (QA.map i)) :
          ShiftedHom (QA.obj ((SA).obj P)) (QA.obj ((SA).obj M)) n) D =
        (g.map QA).map D ≫ (CategoryTheory.shiftFunctor _ n).map (D.map (inv (QA.map i))) := by
    rw [← ShiftedHom.comp_mk₀ (g.map QA) 0 rfl (inv (QA.map i)), ShiftedHom.map_comp, ShiftedHom.map_mk₀,
      ShiftedHom.comp_mk₀]
  change QB.map ((SB).map e) ≫ b.inv.app P ≫ ShiftedHom.map
      (g.map QA ≫ (CategoryTheory.shiftFunctor _ n).map (inv (QA.map i)) :
        ShiftedHom (QA.obj ((SA).obj P)) (QA.obj ((SA).obj M)) n) D ≫
      (CategoryTheory.shiftFunctor _ n).map (b.hom.app M) = _
  rw [hn]
  simp only [Category.assoc, ← Functor.map_comp, hq']
  rw [Functor.map_comp]
  change QB.map ((SB).map e) ≫ b.inv.app P ≫ (g.map QA).map D ≫
    (CategoryTheory.shiftFunctor _ n).map (c.hom.app I) ≫
    (CategoryTheory.shiftFunctor _ n).map (inv (QB.map (mapAugmentation F i))) = _
  have hn' : (g.map QA).map D ≫ (CategoryTheory.shiftFunctor _ n).map (c.hom.app I) =
      c.hom.app ((SA).obj P) ≫ (g.map J).map QB := hnat
  rw [reassoc_of% hn', reassoc_of% (hk P)]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  rfl

private lemma cocycle_shift_coordinate {C : Type*} [Category* C] [Abelian C]
    {P : C} {I : CochainComplex C ℤ} {n : ℤ}
    (g : ShiftedHom ((CochainComplex.singleFunctor C 0).obj P) I n) :
    Cochain.fromSingleEquiv (zero_add n) (Cocycle.equivHomShift g).val =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫
        g.f 0 ≫ (I.shiftFunctorObjXIso n 0 n (zero_add n).symm).hom := by
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫
    ((Cochain.ofHom g).rightUnshift n (zero_add n)).v 0 n (zero_add n) = _
  rw [Cochain.rightUnshift_v _ _ _ 0 n (zero_add n) 0 (add_zero 0), Cochain.ofHom_v]

private lemma transportedCocycle_coordinate {P : A} {P' : B} (e : P' ⟶ F.obj P)
    {I : CochainComplex A ℤ} {n : ℤ} (z : Cocycle ((SA).obj P) I n) :
    Cochain.fromSingleEquiv (zero_add n) (transportedCocycle F e z).val =
      e ≫ F.map (Cochain.fromSingleEquiv (zero_add n) z.val) := by
  rw [transportedCocycle, cocycle_shift_coordinate]
  simp only [HomologicalComplex.comp_f, Functor.mapCochainComplexSingleFunctor, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    ShiftedHom.map, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Cocycle.equivHomShift_symm_apply,
    Cocycle.homOf_f, Cocycle.rightShift_coe]
  rw [Cochain.rightShift_v _ _ _ _ 0 0 (add_zero 0) n (zero_add n)]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToHom_map, Category.assoc]
  have hs : ((SB).map e).f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P').hom ≫
      e ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj P)).inv :=
    HomologicalComplex.single_map_f_self (.up ℤ) 0 e
  rw [hs]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change e ≫ F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ F.map (z.val.v 0 n _) =
    e ≫ F.map ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ z.val.v 0 n _)
  rw [F.map_comp]

end Exact

section UnitTransport
universe v
variable {A B : Type*} [Category* A] [Category* B]
  (E : A ≌ B) (G : B ⥤ AddCommGrpCat.{v})
  {P : A} {P' : B} (s : G.obj (E.functor.obj P)) (s' : G.obj P')

private lemma representedUnit_transport
    (hs : ∀ M : A, Function.Bijective (fun f : P ⟶ M ↦ G.map (E.functor.map f) s))
    (hs' : ∀ M : B, Function.Bijective (fun f : P' ⟶ M ↦ G.map f s')) :
    ∃ e : P' ≅ E.functor.obj P, G.map e.hom s' = s := by
  let F := E.functor
  let P₀ := F.obj P
  have hh (N : B) : Function.Bijective (fun f : P₀ ⟶ N ↦ G.map f s) := by
    let N₀ := E.inverse.obj N
    let q := E.counitIso.app N
    let h : (P ⟶ N₀) ≃ (P₀ ⟶ N) :=
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans ((Iso.refl P₀).homCongr q)
    have he (f : P ⟶ N₀) : G.map (h f) s = G.map q.hom (G.map (F.map f) s) := by
      have hf : h f = F.map f ≫ q.hom := by simp [h, Iso.homCongr]
      rw [hf, G.map_comp, ConcreteCategory.comp_apply]
      rfl
    have hmap : Function.Bijective (fun f : P ⟶ N₀ ↦ G.map (h f) s) := by
      simp only [he]
      exact (G.mapIso q).addCommGroupIsoToAddEquiv.bijective.comp (hs N₀)
    exact (Function.Bijective.of_comp_iff _ h.bijective).mp hmap
  obtain ⟨f, hf⟩ := (hs' P₀).surjective s
  obtain ⟨g, hg⟩ := (hh P').surjective s'
  change G.map f s' = s at hf
  change G.map g s = s' at hg
  have hfg : f ≫ g = 𝟙 P' := by
    apply (hs' P').injective
    change G.map (f ≫ g) s' = G.map (𝟙 P') s'
    rw [G.map_comp, ConcreteCategory.comp_apply, hf, hg, G.map_id]
    rfl
  have hgf : g ≫ f = 𝟙 P₀ := by
    apply (hh P₀).injective
    change G.map (g ≫ f) s = G.map (𝟙 P₀) s
    rw [G.map_comp, ConcreteCategory.comp_apply, hg, hf, G.map_id]
    rfl
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩
end UnitTransport

private lemma identity_homologyIso {B : Type*} [Category* B] [Abelian B] (S : ShortComplex B) :
    (S.mapHomologyIso (𝟭 B)).hom = 𝟙 S.homology := by
  let h := S.homologyData.left
  have hcycles : (h.map (𝟭 B)).cyclesIso.hom = h.cyclesIso.hom := by
    apply (cancel_mono h.i).mp
    exact ((h.map (𝟭 B)).cyclesIso_hom_comp_i).trans h.cyclesIso_hom_comp_i.symm
  have hhomology : (h.map (𝟭 B)).homologyIso.hom = h.homologyIso.hom := by
    apply (cancel_epi S.homologyπ).mp
    exact ((h.map (𝟭 B)).homologyπ_comp_homologyIso_hom).trans
      ((congrArg (fun t ↦ t ≫ h.π) hcycles).trans h.homologyπ_comp_homologyIso_hom.symm)
  rw [h.mapHomologyIso_eq]
  change (h.map (𝟭 B)).homologyIso.hom ≫ h.homologyIso.inv = _
  rw [hhomology, Iso.hom_inv_id]
  rfl

private lemma evaluatedClass_congr.{v} {A B : Type*} [Category.{v} A] [Category.{v} B]
    [Preadditive A] [Preadditive B]
    {K L : CochainComplex A ℤ} {K' L' : CochainComplex B ℤ}
    {D : CochainComplex AddCommGrpCat.{v} ℤ} {n : ℤ}
    (f : HomComplex K L ⟶ D) (g : HomComplex K' L' ⟶ D)
    (z : Cocycle K L n) (z' : Cocycle K' L' n) (h : f.f n z.val = g.f n z'.val) :
    HomologicalComplex.homologyMap f n ((HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z)) =
      HomologicalComplex.homologyMap g n ((HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z')) := by
  let hZ := HomComplex.leftHomologyData K L n
  let hZ' := HomComplex.leftHomologyData K' L' n
  let v := hZ.cyclesIso.inv z
  let v' := hZ'.cyclesIso.inv z'
  have hv : (HomComplex K L).homologyπ n v =
      (HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z) :=
    (congr($(hZ.π_comp_homologyIso_inv) z)).symm
  have hv' : (HomComplex K' L').homologyπ n v' =
      (HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z') :=
    (congr($(hZ'.π_comp_homologyIso_inv) z')).symm
  rw [← hv, ← hv']
  have hf := congr($(HomologicalComplex.homologyπ_naturality f n) v)
  have hg := congr($(HomologicalComplex.homologyπ_naturality g n) v')
  simp only [ConcreteCategory.comp_apply] at hf hg
  rw [hf, hg]
  apply congrArg (D.homologyπ n)
  apply (AddCommGrpCat.mono_iff_injective (D.iCycles n)).mp inferInstance
  have hf' := congr($(HomologicalComplex.cyclesMap_i f n) v)
  have hg' := congr($(HomologicalComplex.cyclesMap_i g n) v')
  have hZ_v := congr($(hZ.cyclesIso_inv_comp_iCycles) z)
  have hZ'_v := congr($(hZ'.cyclesIso_inv_comp_iCycles) z')
  simp only [ConcreteCategory.comp_apply] at hf' hg' hZ_v hZ'_v
  rw [hf', hg']
  change (HomComplex K L).iCycles n v = z.val at hZ_v
  change (HomComplex K' L').iCycles n v' = z'.val at hZ'_v
  rw [hZ_v, hZ'_v, h]

section AbelianSiteExt

open TopologicalSpace AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.SheafTheory
open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport (liftedSpace opensEquiv)
open Specs.AdvancedHomologicalAlgebra.SheafCohomology (abelianOpenUnitSection)

private theorem representedSiteExt_square.{v} {A B : Type*} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
    (J₀ : A ≌ B) [J₀.functor.Additive]
    (G : B ⥤ AddCommGrpCat.{v}) [G.Additive]
    (P : A) (Q : B) (s : G.obj (J₀.functor.obj P)) (t : G.obj Q)
    (q : Q ≅ J₀.functor.obj P) (hq : G.map q.hom t = s)
    (E : ∀ (M : A) (n : ℕ), (rightValue (J₀.functor ⋙ G) n).obj M ≃+ Ext P M (n : ℤ))
    (E' : ∀ (N : B) (n : ℕ), (rightValue G n).obj N ≃+ Ext Q N (n : ℤ))
    (hE : IsSectionsExtModelComparison (J₀.functor ⋙ G) P s E)
    (hE' : IsSectionsExtModelComparison G Q t E')
    (c : ∀ n : ℕ, rightValue (J₀.functor ⋙ G) n ⋙ 𝟭 AddCommGrpCat.{v} ≅ J₀.functor ⋙ rightValue G n)
    (hc : IsResolutionComparison (J₀.functor ⋙ G) G J₀.functor (𝟭 _) (Iso.refl _) c) :
    ∀ (M : A) (n : ℕ) (x : (rightValue (J₀.functor ⋙ G) n).obj M),
      E' (J₀.functor.obj M) n ((c n).hom.app M x) = extTransportValue J₀.functor q.hom (E M n x) := by
  let J := J₀.functor
  let Γ := J ⋙ G
  intro M n x
  let L := (CochainComplex.singleFunctor A 0).obj P
  obtain ⟨I, i, _, hi, hI, hB⟩ :=
    InjectiveComplexReplacement.replacement A ((CochainComplex.singleFunctor A 0).obj M) 0 inferInstance
  letI : I.IsStrictlyGE 0 := hB
  let I' := (J.mapHomologicalComplex (.up ℤ)).obj I
  let i' := mapAugmentation J i
  have hI' (j : ℤ) : Injective (I'.X j) :=
    J₀.map_injective_iff _ |>.2 (hI j)
  obtain ⟨hi', hm⟩ := hc M I i hi hI
  obtain ⟨k, hk, hsrc⟩ := hE M I i hi hI
  obtain ⟨k', hk', htgt⟩ := hE' (J.obj M) I' i' hi' hI'
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) (n : ℤ)
  let N := (Γ.mapHomologicalComplex (.up ℤ)).obj I
  haveI := SheafCohomology.resolutionModelMap_isIso Γ i hi (fun j ↦ by
    letI := hI j
    exact AcyclicTermComparison.rightAcyclic_of_injective Γ _) n
  let a₀ : CohomologyClass L I (n : ℤ) ≃+ (rightValue Γ n).obj M :=
    (HomComplex.homologyAddEquiv L I (n : ℤ)).symm.trans
      ((H.mapIso k).addCommGroupIsoToAddEquiv.trans
        (asIso (resolutionModelMap Γ i hi n)).addCommGroupIsoToAddEquiv)
  obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (a₀.symm x)
  have hx : a₀ (CohomologyClass.mk z) = x := by rw [hz, AddEquiv.apply_symm_apply]
  let z' := transportedCocycle J q.hom z
  have hsections : k.hom.f (n : ℤ) z.val = k'.hom.f (n : ℤ) z'.val := by
    rw [hk, hk', transportedCocycle_coordinate]
    change G.map (J.map (Cochain.fromSingleEquiv (zero_add (n : ℤ)) z.val)) s =
      G.map (q.hom ≫ J.map (Cochain.fromSingleEquiv (zero_add (n : ℤ)) z.val)) t
    rw [G.map_comp, ConcreteCategory.comp_apply, hq]
  have hv := evaluatedClass_congr k.hom k'.hom z z' hsections
  have hcomp : (modelComparison Γ G J (𝟭 _) (Iso.refl (Γ ⋙ 𝟭 AddCommGrpCat.{v})) I n).hom =
      𝟙 (N.homology (n : ℤ)) := by
    unfold modelComparison
    have h₀ : ((N.sc (n : ℤ)).mapHomologyIso (𝟭 _)).inv = 𝟙 (N.homology (n : ℤ)) := by
      have he : (N.sc (n : ℤ)).mapHomologyIso (𝟭 _) = Iso.refl (N.homology (n : ℤ)) := by
        apply Iso.ext
        exact identity_homologyIso (N.sc (n : ℤ))
      exact congrArg Iso.inv he
    have h₁ : ((NatIso.mapHomologicalComplex (Iso.refl (Γ ⋙ 𝟭 AddCommGrpCat.{v})) (.up ℤ)).app I).hom =
      𝟙 N := by
      ext j w
      rfl
    change ((N.sc (n : ℤ)).mapHomologyIso (𝟭 _)).inv ≫
      H.map ((NatIso.mapHomologicalComplex (Iso.refl (Γ ⋙ 𝟭 AddCommGrpCat.{v})) (.up ℤ)).app I).hom = _
    rw [h₀, h₁]
    have h₂ : H.map (𝟙 N) = 𝟙 (N.homology (n : ℤ)) := H.map_id N
    erw [h₂, Category.id_comp]
  have hcomm := congr($(hm n)
    (HomologicalComplex.homologyMap k.hom (n : ℤ)
      ((HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm (CohomologyClass.mk z))))
  rw [hcomp] at hcomm
  simp only [Category.id_comp, ConcreteCategory.comp_apply] at hcomm
  change (c n).hom.app M (a₀ (CohomologyClass.mk z)) =
    resolutionModelMap G i' hi' n
      (HomologicalComplex.homologyMap k.hom (n : ℤ)
        ((HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm (CohomologyClass.mk z))) at hcomm
  rw [hv] at hcomm
  rw [← hx, hcomm]
  have hsrc' : E M n (a₀ (CohomologyClass.mk z)) = _ := hsrc n (CohomologyClass.mk z)
  rw [hsrc']
  exact (htgt n (CohomologyClass.mk z')).trans (transportExt_injectiveClass J q.hom i hi hi' z).symm

set_option maxHeartbeats 800000 in
private theorem abelianSiteExt_aux
    (unit : abelianUnitType.{a,u,r}) (site : abelianSiteComparisonType.{a,u,r})
    (ext : abelianExtType.{a,u,r}) : abelianSiteExtType.{a,u,r} := by
  intro X U D _
  dsimp only
  let A := OriginalAbelianSheaves.{a,u,r} X
  let Y := liftedSpace.{max a u r} X
  let B := AbelianSheaves Y
  let V := opensEquiv X U
  let J := abelianTransport.{a,u,r} X
  let Γ := abelianSectionsValue.{a,u,r} X V
  let G := abelianSections Y U
  let P := originalAbelianUnit.{a,u,r} X U D
  let s := originalAbelianUnitSection.{a,u,r} X U D
  let Q := abelianOpenUnit Y U
  let t := abelianOpenUnitSection Y U
  obtain ⟨e₀, he₀⟩ := unit X U D
  obtain ⟨e₁, he₁⟩ := SheafCohomology.abelianOpenUnitRepresentation Y U
  have hu₀ (M : A) : Function.Bijective (fun f : P ⟶ M ↦ G.map (J.map f) s) := by
    have h := ((e₀.app M).addCommGroupIsoToAddEquiv).bijective
    change Function.Bijective (fun f : P ⟶ M ↦ e₀.hom.app M f) at h
    simp only [he₀] at h
    exact h
  have hu₁ (M : B) : Function.Bijective (fun f : Q ⟶ M ↦ G.map f t) := by
    have h := ((e₁.app M).addCommGroupIsoToAddEquiv).bijective
    change Function.Bijective (fun f : Q ⟶ M ↦ e₁.hom.app M f) at h
    simpa only [he₁] using h
  obtain ⟨q, hq⟩ := representedUnit_transport (originalAbelianEquivalence.{max a u r} X) G
    (P := P) (P' := Q) s t hu₀ hu₁
  obtain ⟨c, hc⟩ := site X U
  obtain ⟨E, _, _, _, hE⟩ := ext X U D
  obtain ⟨liftedExt, _, liftedModel⟩ := SheafCohomology.ext Y U
  let E' (M : B) (n : ℕ) : (rightValue G n).obj M ≃+ Ext Q M (n : ℤ) := liftedExt M n
  have hE' : IsSectionsExtModelComparison G Q t E' := liftedModel
  refine ⟨q, hq, c, hc, E, E', hE, hE', ?_⟩
  letI : (originalAbelianEquivalence.{max a u r} X).functor.Additive :=
    inferInstanceAs (abelianTransport.{a,u,r} X).Additive
  exact representedSiteExt_square (originalAbelianEquivalence.{max a u r} X) G
    P Q s t q hq E E' hE hE' c hc

end AbelianSiteExt


theorem abelianSiteExt : abelianSiteExtType.{a,u,r} :=
  abelianSiteExt_aux abelianUnit abelianSiteComparison abelianExt

end AbelianExtSiteComparison

section AbelianExtAmbientComparison

open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

universe v

private def freeYonedaLiftIso {C A B : Type*} [Category.{v} C] [Category* A] [Category* B]
    [HasCoproducts.{v} A] [HasCoproducts.{v} B] (H : A ⥤ B)
    [PreservesColimitsOfSize.{v, v} H]
    (V : C) (M : A) {N : B} (i : N ≅ H.obj M) :
    Presheaf.freeYoneda V N ≅ Presheaf.freeYoneda V M ⋙ H := by
  let e (W : Cᵒᵖ) :=
    HasColimit.isoOfNatIso (Discrete.natIso (F := Discrete.functor (fun _ : (yoneda.obj V).obj W ↦ N))
      (G := Discrete.functor (fun _ : (yoneda.obj V).obj W ↦ H.obj M)) (fun _ ↦ i)) ≪≫
      (PreservesCoproduct.iso H (fun _ : (yoneda.obj V).obj W ↦ M)).symm
  refine NatIso.ofComponents e ?_
  intro W Y f
  apply Sigma.hom_ext
  intro g
  simp [e, Presheaf.freeYoneda, ← Functor.map_comp]

private def freeAbelianSheafRepresentation (X : TopCat.{u}) (V : Opens X) :
    (abelianSectionsValue.{a,u,r} X V ⋙ forget _).CorepresentableBy
      (Sheaf.freeYoneda (Opens.grothendieckTopology X) V
        (AddCommGrpCat.of (ULift.{max a u r} ℤ))) where
  homEquiv {M} := Sheaf.freeYonedaHomEquiv.trans
    (AddCommGrpCat.coyonedaObjIsoForget.app (M.obj.obj (op V))).toEquiv
  homEquiv_comp {M N} g f := by
    change (AddCommGrpCat.coyonedaObjIsoForget.hom.app _) (Sheaf.freeYonedaHomEquiv (f ≫ g)) =
      (forget _).map ((abelianSectionsValue.{a,u,r} X V).map g)
        ((AddCommGrpCat.coyonedaObjIsoForget.hom.app _) (Sheaf.freeYonedaHomEquiv f))
    have hf : Sheaf.freeYonedaHomEquiv (f ≫ g) =
        Sheaf.freeYonedaHomEquiv f ≫ g.hom.app (op V) := by
      rfl
    rw [hf]
    exact AddCommGrpCat.coyonedaObjIsoForget.hom.naturality_apply (g.hom.app (op V)) _

private def corepresentationOfAdditive {A : Type*} [Category.{v} A] [Preadditive A]
    {Γ : A ⥤ AddCommGrpCat.{v}} {P : A} (c : preadditiveCoyoneda.obj (op P) ≅ Γ) :
    (Γ ⋙ forget _).CorepresentableBy P :=
  (Functor.CorepresentableBy.coyoneda (op P)).ofIso (isoWhiskerRight c (forget _))

set_option maxHeartbeats 900000 in
private theorem abelianUnitLiftIso (X : TopCat.{u}) (V : Opens X)
    {P : OriginalAbelianSheaves.{a,u,r} X} {Q : OriginalAbelianSheaves.{max a b,u,r} X}
    (s : (abelianSectionsValue.{a,u,r} X V).obj P)
    (t : (abelianSectionsValue.{max a b,u,r} X V).obj Q)
    (e : preadditiveCoyoneda.obj (op P) ≅ abelianSectionsValue.{a,u,r} X V)
    (e' : preadditiveCoyoneda.obj (op Q) ≅ abelianSectionsValue.{max a b,u,r} X V)
    (he : ∀ M f, e.hom.app M f = (abelianSectionsValue.{a,u,r} X V).map f s)
    (he' : ∀ N f, e'.hom.app N f = (abelianSectionsValue.{max a b,u,r} X V).map f t) :
    ∃ q : Q ≅ (abelianCoefficientLift.{a,u,r,b} X).obj P,
      (abelianSectionsValue.{max a b,u,r} X V).map q.hom t = ULift.up s := by
  let J := Opens.grothendieckTopology X
  let L := abelianCoefficientLift.{a,u,r,b} X
  let G := abelianSectionsValue.{max a b,u,r} X V
  let H := AddCommGrpCat.uliftFunctor.{b,max a u r}
  let Z := AddCommGrpCat.of (ULift.{max a u r} ℤ)
  let Z' := AddCommGrpCat.of (ULift.{max a b u r} ℤ)
  let iZ : Z' ≅ H.obj Z :=
    (AddEquiv.ulift.trans (AddEquiv.ulift.symm.trans AddEquiv.ulift.symm)).toAddCommGrpIso
  let iP := (freeAbelianSheafRepresentation.{a,u,r} X V).uniqueUpToIso (corepresentationOfAdditive e)
  let iQ := (corepresentationOfAdditive e').uniqueUpToIso (freeAbelianSheafRepresentation.{max a b,u,r} X V)
  let i : Q ≅ L.obj P := iQ ≪≫ (presheafToSheaf J _).mapIso (freeYonedaLiftIso H V Z iZ) ≪≫
    (abelianLift_sheafification.{a,u,r,b} X).app (Presheaf.freeYoneda V Z) ≪≫ L.mapIso iP
  let s' : G.obj (L.obj P) := ULift.up s
  have hP : Function.Bijective (fun f : L.obj P ⟶ L.obj P ↦ G.map f s') := by
    let b := (Functor.FullyFaithful.ofFullyFaithful L).homEquiv (X := P) (Y := P)
    apply (Function.Bijective.of_comp_iff _ b.bijective).mp
    have hs := (e.app P).addCommGroupIsoToAddEquiv.bijective
    change Function.Bijective (fun f : P ⟶ P ↦ e.hom.app P f) at hs
    simp only [he] at hs
    exact ULift.up_bijective.comp hs
  have hQ (N : OriginalAbelianSheaves.{max a b,u,r} X) :
      Function.Bijective (fun f : Q ⟶ N ↦ G.map f t) := by
    have h := (e'.app N).addCommGroupIsoToAddEquiv.bijective
    change Function.Bijective (fun f : Q ⟶ N ↦ e'.hom.app N f) at h
    simpa only [he'] using h
  obtain ⟨f, hf⟩ := (hQ (L.obj P)).surjective s'
  obtain ⟨g, hg⟩ := hP.surjective (G.map i.hom t)
  let j : L.obj P ⟶ Q := g ≫ i.inv
  have hj : G.map j s' = t := by
    change G.map g s' = G.map i.hom t at hg
    rw [show j = g ≫ i.inv from rfl, G.map_comp, ConcreteCategory.comp_apply, hg,
      ← ConcreteCategory.comp_apply, ← G.map_comp, i.hom_inv_id, G.map_id]
    rfl
  change G.map f t = s' at hf
  have hfj : f ≫ j = 𝟙 Q := by
    apply (hQ Q).injective
    change G.map (f ≫ j) t = G.map (𝟙 Q) t
    rw [G.map_comp, ConcreteCategory.comp_apply, hf, hj, G.map_id]
    rfl
  have hjf : j ≫ f = 𝟙 (L.obj P) := by
    apply hP.injective
    change G.map (j ≫ f) s' = G.map (𝟙 (L.obj P)) s'
    rw [G.map_comp, ConcreteCategory.comp_apply, hj, hf, G.map_id]
    rfl
  exact ⟨⟨f, j, hfj, hjf⟩, hf⟩

private lemma zeroHom_mk₀ {C : Type*} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    zeroHom f = ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.singleFunctor C 0).map f) := by
  simp only [zeroHom, ShiftedHom.mk₀, shiftFunctorZero', eqToIso_refl, Iso.refl_trans]
  rfl

section

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (J : A ⥤ B) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]

local notation "SA" => DerivedCategory.singleFunctor A 0
local notation "SB" => DerivedCategory.singleFunctor B 0

private lemma extTransportValue_zero {P M : A} {Q : B} (q : Q ⟶ J.obj P) (f : P ⟶ M) :
    extTransportValue J q (zeroHom f) = zeroHom (q ≫ J.map f) := by
  let b := J.mapDerivedCategorySingleFunctor 0
  let L := J.mapDerivedCategory
  rw [zeroHom_mk₀, zeroHom_mk₀]
  unfold extTransportValue
  rw [ShiftedHom.map_mk₀, ← ShiftedHom.comp_mk₀ _ (0 : ℤ) rfl, ShiftedHom.mk₀_comp_mk₀, Functor.map_comp]
  have h := b.hom.naturality f
  change L.map ((SA).map f) ≫ b.hom.app M = b.hom.app P ≫ (SB).map (J.map f) at h
  dsimp only [L, b] at h
  simp only [ShiftedHom.mk₀, Category.assoc, h, Iso.inv_hom_id_app_assoc]

private lemma extTransportValue_boundary {P : A} {Q : B} (q : Q ⟶ J.obj P)
    {S : ShortComplex A} (hS : S.ShortExact) {n m : ℤ} (x : Ext P S.X₃ n) (h : 1 + n = m) :
    extTransportValue J q (ShiftedHom.comp x hS.singleδ h) =
      ShiftedHom.comp (extTransportValue J q x) (hS.map_of_exact J).singleδ h := by
  subst m
  let b := J.mapDerivedCategorySingleFunctor 0
  let L := J.mapDerivedCategory
  rw [extTransportValue, ShiftedHom.map_comp, hS.mapShiftedHom_singleδ J, extTransportValue]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  let T := shiftFunctorAdd' (DerivedCategory B) (1 : ℤ) n (1 + n) rfl
  have h := T.inv.naturality (b.hom.app S.X₁)
  change (CategoryTheory.shiftFunctor _ n).map ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map (b.hom.app S.X₁)) ≫
    T.inv.app ((SB).obj (J.obj S.X₁)) =
      T.inv.app (L.obj ((SA).obj S.X₁)) ≫ (CategoryTheory.shiftFunctor _ (1 + n)).map (b.hom.app S.X₁) at h
  rw [← h]
  have hcancel : (CategoryTheory.shiftFunctor _ n).map ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map (b.inv.app S.X₁)) ≫
      (CategoryTheory.shiftFunctor _ n).map ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map (b.hom.app S.X₁)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  dsimp only [b] at hcancel
  rw [reassoc_of% hcancel]
  rfl

end

private theorem abelianUnit_at
    (X : TopCat.{u}) (W : Opens (liftedSpace.{max a u r} X)) (D : IntegerOpenData.{a,u,r} X W)
    (V : Opens X) (h : opensEquiv X W = V) :
    let Q := originalAbelianUnit.{a,u,r} X W D
    let G := abelianSectionsValue.{a,u,r} X V
    let t : G.obj Q := Eq.ndrec (motive := fun V ↦ ↥((abelianSectionsValue.{a,u,r} X V).obj Q))
      (originalAbelianUnitSection.{a,u,r} X W D) h
    ∃ e : preadditiveCoyoneda.obj (op Q) ≅ G, ∀ N f, e.hom.app N f = G.map f t := by
  subst V
  exact abelianUnit.{a,u,r} X W D

private theorem abelianExt_at
    (X : TopCat.{u}) (W : Opens (liftedSpace.{max a u r} X)) (D : IntegerOpenData.{a,u,r} X W)
    (V : Opens X) (h : opensEquiv X W = V) [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)] :
    let Q := originalAbelianUnit.{a,u,r} X W D
    let G := abelianSectionsValue.{a,u,r} X V
    let t : G.obj Q := Eq.ndrec (motive := fun V ↦ ↥((abelianSectionsValue.{a,u,r} X V).obj Q))
      (originalAbelianUnitSection.{a,u,r} X W D) h
    ∃ E : ∀ (N : OriginalAbelianSheaves.{a,u,r} X) (n : ℕ), (rightValue G n).obj N ≃+ Ext Q N (n : ℤ),
      (∀ N (f : Q ⟶ N), E N 0 ((rightDegreeZeroUnit G).app N (G.map f t)) = zeroHom f) ∧
      (∀ (S : ShortComplex (OriginalAbelianSheaves.{a,u,r} X)) (hS : S.ShortExact) (n : ℕ)
        (x : (rightValue G n).obj S.X₃), E S.X₁ (n + 1) (rightBoundary G hS n x) =
          ShiftedHom.comp (E S.X₃ n x) hS.singleδ (by omega)) ∧
      IsSectionsExtModelComparison G Q t E := by
  subst V
  obtain ⟨E, _, h0, hd, hI⟩ := abelianExt.{a,u,r} X W D
  exact ⟨E, h0, hd, hI⟩

set_option maxHeartbeats 1200000 in
theorem abelianAmbientExt : abelianAmbientExtType.{a,u,r,b} := by
  intro X U W hW D D' _ _
  dsimp only
  let V := opensEquiv X U
  let L := abelianCoefficientLift.{a,u,r,b} X
  let Γ := abelianSectionsValue.{a,u,r} X V
  let G := abelianSectionsValue.{max a b,u,r} X V
  let P := originalAbelianUnit.{a,u,r} X U D
  let Q := originalAbelianUnit.{max a b,u,r} X W D'
  let s := originalAbelianUnitSection.{a,u,r} X U D
  let t : G.obj Q := Eq.ndrec (motive := fun V ↦ ↥((abelianSectionsValue.{max a b,u,r} X V).obj Q))
    (originalAbelianUnitSection.{max a b,u,r} X W D') hW
  obtain ⟨hlim, hcolim⟩ := abelianLift_exact.{a,u,r,b} X
  letI := hlim
  letI := hcolim
  obtain ⟨e, he⟩ := abelianUnit.{a,u,r} X U D
  obtain ⟨e', he'⟩ := abelianUnit_at.{max a b,u,r} X W D' V hW
  obtain ⟨q, hq⟩ := abelianUnitLiftIso.{a,u,r,b} X V s t e e' he he'
  obtain ⟨c, hc, hc₀, hcδ⟩ := abelianAmbientComparisonExact.{a,u,r,b} X V
  obtain ⟨E, _, hE₀, hEδ, hE⟩ := abelianExt.{a,u,r} X U D
  obtain ⟨E', hE'₀, hE'δ, hE'⟩ := abelianExt_at.{max a b,u,r} X W D' V hW
  refine ⟨hlim, hcolim, q, c, E, E', hq, hc, hE, hE', ?_⟩
  letI : PreservesFiniteLimits Γ := comp_preservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max a u r})
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max a u r}).obj (op V))
  letI : IsIso (rightDegreeZeroUnit Γ) := ClassicalDerivedValues.rightZero _ _ Γ
  intro M n
  induction n generalizing M with
  | zero =>
    intro x
    have hf := (e.app M).addCommGroupIsoToAddEquiv.surjective
    change Function.Surjective (fun f : P ⟶ M ↦ e.hom.app M f) at hf
    simp only [he] at hf
    have hx := (asIso ((rightDegreeZeroUnit Γ).app M)).addCommGroupIsoToAddEquiv.surjective.comp hf
    obtain ⟨f, rfl⟩ := hx x
    have h := congr($(NatTrans.congr_app hc₀ M) (ULift.up (Γ.map f s)))
    change (c 0).hom.app M (ULift.up ((rightDegreeZeroUnit Γ).app M (Γ.map f s))) =
      (rightDegreeZeroUnit G).app (L.obj M) (ULift.up (Γ.map f s)) at h
    change E' (L.obj M) 0 ((c 0).hom.app M (ULift.up ((rightDegreeZeroUnit Γ).app M (Γ.map f s)))) =
      extTransportValue L q.hom (E M 0 ((rightDegreeZeroUnit Γ).app M (Γ.map f s)))
    have hg : G.map (q.hom ≫ L.map f) t = ULift.up (Γ.map f s) := by
      rw [G.map_comp, ConcreteCategory.comp_apply, hq]
      rfl
    rw [h, ← hg, hE'₀, hE₀, extTransportValue_zero]
  | succ n ih =>
    intro x
    let S := UniversalDeltaFunctors.injectiveSequence M
    have hS := UniversalDeltaFunctors.injectiveSequence_shortExact M
    letI : Epi (rightBoundary Γ hS n) :=
      UniversalDeltaFunctors.dimensionShift_epi (rightSystem Γ)
        (UniversalDeltaFunctors.rightDelta _ _ Γ) (ClassicalDerivedValues.rightInjectiveVanishing _ _ Γ) M n
    obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (rightBoundary Γ hS n)).mp inferInstance x
    obtain ⟨hLS, hs⟩ := hcδ S hS
    have h := congr($(hs n) (ULift.up y))
    change rightBoundary G hLS n ((c n).hom.app S.X₃ (ULift.up y)) =
      (c (n + 1)).hom.app S.X₁ (ULift.up (rightBoundary Γ hS n y)) at h
    change E' (L.obj S.X₁) (n + 1) ((c (n + 1)).hom.app S.X₁ (ULift.up (rightBoundary Γ hS n y))) =
      extTransportValue L q.hom (E S.X₁ (n + 1) (rightBoundary Γ hS n y))
    rw [← h]
    have hdeg : 1 + (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by omega
    calc
      _ = ShiftedHom.comp (E' (L.obj S.X₃) n ((c n).hom.app S.X₃ (ULift.up y))) hLS.singleδ hdeg :=
        hE'δ (S.map L) hLS n ((c n).hom.app S.X₃ (ULift.up y))
      _ = ShiftedHom.comp (extTransportValue L q.hom (E S.X₃ n y)) hLS.singleδ hdeg :=
        congrArg (fun z ↦ ShiftedHom.comp z hLS.singleδ hdeg) (ih S.X₃ y)
      _ = extTransportValue L q.hom (ShiftedHom.comp (E S.X₃ n y) hS.singleδ hdeg) :=
        (extTransportValue_boundary L q.hom hS (E S.X₃ n y) hdeg).symm
      _ = _ := congrArg (extTransportValue L q.hom) (hEδ S hS n y).symm

end AbelianExtAmbientComparison


section OverSquare

variable {A D D' E E' C C' : Type*}
  [Category* A] [Category* D] [Category* D'] [Category* E] [Category* E']
  [Category* C] [Category* C']
  (S : D ≌ D') (T : E ≌ E') (P : A ⥤ D) (Q : A ⥤ E) (V : D ⥤ E)
  (F : D ⥤ C) (G : E ⥤ C') (H : C ⥤ C') (p : P ⋙ V ≅ Q)
  (s : F ⋙ H ≅ V ⋙ G)

private lemma sectionsSquareOfOver (M : A) :
    H.map ((restrictionSectionsOver P F S).inv.app M) ≫
      (subspaceSectionsOfOver T V G H F S s).hom.app ((P ⋙ S.functor).obj M) ≫
      (T.inverse ⋙ G).map ((openRestrictionComparisonOfOver T V S P Q p).hom.app M) =
    (ambientSectionsOfOver V G H P F Q p s).hom.app M ≫
      (restrictionSectionsOver Q G T).inv.app M := by
  let X := P.obj M
  let u := S.unitIso.app X
  let v := p.hom.app M
  have h₁ := s.hom.naturality u.hom
  have h₂ := T.unitIso.hom.naturality (V.map u.inv)
  have h₃ := T.unitIso.hom.naturality v
  simp only [Functor.comp_map] at h₁ h₂ h₃
  simp only [restrictionSectionsOver, subspaceSectionsOfOver, openSectionsComparisonOfOver,
    openRestrictionComparisonOfOver, ambientSectionsOfOver,
    Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app,
    Iso.symm_hom, Iso.symm_inv, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.id_comp, Category.comp_id,
    Category.assoc]
  simp only [← G.map_comp, ← T.inverse.map_comp]
  rw [show 𝟙 (T.functor.obj (V.obj X)) ≫ T.functor.map v = T.functor.map v from Category.id_comp _]
  change H.map (F.map u.hom) ≫ s.hom.app _ ≫
    G.map (T.unitIso.hom.app _ ≫ T.inverse.map (T.functor.map (V.map u.inv) ≫ T.functor.map v)) =
    s.hom.app _ ≫ G.map (v ≫ T.unitIso.hom.app _)
  rw [← Category.assoc, h₁, Category.assoc]
  rw [← G.map_comp]
  congr 2
  rw [T.inverse.map_comp]
  have h₂' := congrArg (fun f ↦ V.map u.hom ≫ f ≫ T.inverse.map (T.functor.map v)) h₂.symm
  simp only [Category.assoc, Functor.id_map] at h₂'
  refine h₂'.trans ?_
  rw [← Category.assoc, ← V.map_comp, u.hom_inv_id, V.map_id, Category.id_comp]
  exact h₃.symm

end OverSquare
section LocalitySquare

variable {A₀ A₁ B₀ B₁ C C' : Type*}
  [Category* A₀] [Category* A₁] [Category* B₀] [Category* B₁] [Category* C] [Category* C']
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁] [Abelian C] [Abelian C']
  (S : A₀ ⥤ A₁) (T : B₀ ⥤ B₁) (J : A₀ ⥤ B₀) (K : A₁ ⥤ B₁)
  [S.Additive] [T.Additive] [J.Additive] [K.Additive]
  (p : S ⋙ K ≅ J ⋙ T)
  {M : A₀} {I : CochainComplex A₀ ℤ}
  (i : (CochainComplex.singleFunctor A₀ 0).obj M ⟶ I)

private lemma mapAugmentation_square :
    mapAugmentation K (mapAugmentation S i) ≫
      (NatIso.mapHomologicalComplex p (.up ℤ)).hom.app I =
    (CochainComplex.singleFunctor B₁ 0).map (p.hom.app M) ≫
      mapAugmentation T (mapAugmentation J i) := by
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : q = 0
  · subst q
    let s := fun (X : A₀) ↦ HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
    simp only [mapAugmentation, HomologicalComplex.comp_f,
      Functor.mapCochainComplexSingleFunctor, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.map_comp, Category.assoc]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.id_comp]
    simp only [Category.assoc]
    rw [show K.map (S.map ((s M).inv ≫ i.f 0)) ≫ p.hom.app (I.X 0) =
        p.hom.app M ≫ T.map (J.map ((s M).inv ≫ i.f 0)) from
      p.hom.naturality ((s M).inv ≫ i.f 0)]
    change _ = ((HomologicalComplex.single B₁ (.up ℤ) 0).map (p.hom.app M)).f 0 ≫ _
    simp [s, HomologicalComplex.single_map_f_self]
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ _ hq).eq_of_src


variable [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives B₀] [EnoughInjectives B₁]
  (F₀ : A₀ ⥤ C) (F₁ : A₁ ⥤ C) (G₀ : B₀ ⥤ C') (G₁ : B₁ ⥤ C') (H : C ⥤ C')
  [F₀.Additive] [F₁.Additive] [G₀.Additive] [G₁.Additive] [H.Additive] [H.PreservesHomology]
  (c₀ : F₀ ⋙ H ≅ J ⋙ G₀) (c₁ : F₁ ⋙ H ≅ K ⋙ G₁)
  (v₀ : F₀ ≅ S ⋙ F₁) (v₁ : G₀ ≅ T ⋙ G₁)
  [I.IsStrictlyGE 0] (hi : QuasiIso i) (n : ℕ)

private theorem localityModelSquare
    (e₀ : rightValue F₀ n ⋙ H ≅ J ⋙ rightValue G₀ n)
    (e₁ : rightValue F₁ n ⋙ H ≅ K ⋙ rightValue G₁ n)
    (l₀ : rightValue F₀ n ≅ S ⋙ rightValue F₁ n)
    (l₁ : rightValue G₀ n ≅ T ⋙ rightValue G₁ n)
    (hiS : QuasiIso (mapAugmentation S i))
    (hiJ : QuasiIso (mapAugmentation J i))
    (hiKS : QuasiIso (mapAugmentation K (mapAugmentation S i)))
    (hiTJ : QuasiIso (mapAugmentation T (mapAugmentation J i)))
    (he₀ : H.map (resolutionModelMap F₀ i hi n) ≫ e₀.hom.app M =
      (modelComparison F₀ G₀ J H c₀ I n).hom ≫
        resolutionModelMap G₀ (mapAugmentation J i) hiJ n)
    (he₁ : H.map (resolutionModelMap F₁ (mapAugmentation S i) hiS n) ≫ e₁.hom.app (S.obj M) =
      (modelComparison F₁ G₁ K H c₁ ((S.mapHomologicalComplex (.up ℤ)).obj I) n).hom ≫
        resolutionModelMap G₁ (mapAugmentation K (mapAugmentation S i)) hiKS n)
    (hl₀ : resolutionModelMap F₀ i hi n ≫ l₀.hom.app M =
      HomologicalComplex.homologyMap ((NatIso.mapHomologicalComplex v₀ (.up ℤ)).hom.app I)
        (n : ℤ) ≫ resolutionModelMap F₁ (mapAugmentation S i) hiS n)
    (hl₁ : resolutionModelMap G₀ (mapAugmentation J i) hiJ n ≫ l₁.hom.app (J.obj M) =
      HomologicalComplex.homologyMap ((NatIso.mapHomologicalComplex v₁ (.up ℤ)).hom.app
        ((J.mapHomologicalComplex (.up ℤ)).obj I)) (n : ℤ) ≫
          resolutionModelMap G₁ (mapAugmentation T (mapAugmentation J i)) hiTJ n)
    (comm : ∀ X : A₀, H.map (v₀.hom.app X) ≫ c₁.hom.app (S.obj X) ≫ G₁.map (p.hom.app X) =
      c₀.hom.app X ≫ v₁.hom.app (J.obj X))
    [IsIso (resolutionModelMap F₀ i hi n)] :
    H.map (l₀.hom.app M) ≫ e₁.hom.app (S.obj M) ≫ (rightValue G₁ n).map (p.hom.app M) =
      e₀.hom.app M ≫ l₁.hom.app (J.obj M) := by
  let σ := ComplexShape.up ℤ
  let s := (NatIso.mapHomologicalComplex v₀ σ).hom.app I
  let t := (NatIso.mapHomologicalComplex v₁ σ).hom.app ((J.mapHomologicalComplex σ).obj I)
  let d := (NatIso.mapHomologicalComplex p σ).hom.app I
  let x := (NatIso.mapHomologicalComplex c₀ σ).hom.app I
  let y := (NatIso.mapHomologicalComplex c₁ σ).hom.app ((S.mapHomologicalComplex σ).obj I)
  let R := HomologicalComplex.homologyFunctor C' σ (n : ℤ)
  have hd := SheafCohomology.resolutionModelMap_naturality G₁ _ hiKS _ hiTJ (p.hom.app M) d
    (congrArg DerivedCategory.Q.map (mapAugmentation_square S T J K p i)) n
  have hcomm : (H.mapHomologicalComplex σ).map s ≫ y ≫
      (G₁.mapHomologicalComplex σ).map d = x ≫ t := by
    apply HomologicalComplex.Hom.ext
    funext q
    simpa only [σ, s, t, d, x, y, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex_hom_app_f] using comm (I.X q)
  have hmap : H.map (HomologicalComplex.homologyMap s (n : ℤ)) ≫
      ((((F₁.mapHomologicalComplex σ).obj ((S.mapHomologicalComplex σ).obj I)).sc (n : ℤ)).mapHomologyIso H).inv =
    ((((F₀.mapHomologicalComplex σ).obj I).sc (n : ℤ)).mapHomologyIso H).inv ≫
      R.map ((H.mapHomologicalComplex σ).map s) :=
    ShortComplex.mapHomologyIso_inv_naturality ((HomologicalComplex.shortComplexFunctor _ _ (n : ℤ)).map s) H
  apply (cancel_epi (H.map (resolutionModelMap F₀ i hi n))).mp
  rw [← H.map_comp_assoc, hl₀, H.map_comp_assoc, reassoc_of% he₁,
    hd, reassoc_of% he₀, hl₁]
  dsimp only [modelComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  change _ ≫ (_ ≫ R.map y) ≫ R.map ((G₁.mapHomologicalComplex σ).map d) ≫ _ =
    (_ ≫ R.map x) ≫ R.map t ≫ _
  simp only [Category.assoc]
  rw [reassoc_of% hmap, ← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, hcomm,
    R.map_comp_assoc]


private theorem localitySquare_of_models
    (e₀ : ∀ n : ℕ, rightValue F₀ n ⋙ H ≅ J ⋙ rightValue G₀ n)
    (e₁ : ∀ n : ℕ, rightValue F₁ n ⋙ H ≅ K ⋙ rightValue G₁ n)
    (l₀ : ∀ n : ℕ, rightValue F₀ n ≅ S ⋙ rightValue F₁ n)
    (l₁ : ∀ n : ℕ, rightValue G₀ n ≅ T ⋙ rightValue G₁ n)
    (he₀ : IsResolutionComparison F₀ G₀ J H c₀ e₀)
    (he₁ : IsResolutionComparison F₁ G₁ K H c₁ e₁)
    (hl₀ : IsLocalityComparison S F₀ F₁ v₀.symm l₀)
    (hI : ∀ q : ℤ, Injective (I.X q))
    (hl₁ : ∀ hiJ : QuasiIso (mapAugmentation J i),
      ∃ hiTJ : QuasiIso (mapAugmentation T (mapAugmentation J i)), ∀ n : ℕ,
      resolutionModelMap G₀ (mapAugmentation J i) hiJ n ≫ (l₁ n).hom.app (J.obj M) =
        HomologicalComplex.homologyMap ((NatIso.mapHomologicalComplex v₁ (.up ℤ)).hom.app
          ((J.mapHomologicalComplex (.up ℤ)).obj I)) (n : ℤ) ≫
            resolutionModelMap G₁ (mapAugmentation T (mapAugmentation J i)) hiTJ n)
    (comm : ∀ X : A₀, H.map (v₀.hom.app X) ≫ c₁.hom.app (S.obj X) ≫ G₁.map (p.hom.app X) =
      c₀.hom.app X ≫ v₁.hom.app (J.obj X))
    [IsIso (resolutionModelMap F₀ i hi n)] :
    H.map ((l₀ n).hom.app M) ≫ (e₁ n).hom.app (S.obj M) ≫ (rightValue G₁ n).map (p.hom.app M) =
      (e₀ n).hom.app M ≫ (l₁ n).hom.app (J.obj M) := by
  obtain ⟨hiJ, heI⟩ := he₀ M I i hi hI
  obtain ⟨hiS, hI', hlI⟩ := hl₀ M I i hi hI
  let SI := (S.mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨hiKS, heI'⟩ := he₁ (S.obj M) SI (mapAugmentation S i) hiS hI'
  obtain ⟨hiTJ, hlI'⟩ := hl₁ hiJ
  exact localityModelSquare S T J K p i F₀ F₁ G₀ G₁ H c₀ c₁ v₀ v₁ hi n
    (e₀ n) (e₁ n) (l₀ n) (l₁ n) hiS hiJ hiKS hiTJ (heI n) (heI' n) (hlI n) (hlI' n) comm

end LocalitySquare


section LocalityTransport

open AdvancedHomologicalAlgebra.SheafTheory (restriction sectionsRestrictionIso)

section SectionSquares
variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- The independent section-site comparison is the map from the original
open restriction and its transported restriction. -/
theorem localityRestrictionComparison_eq (U : Opens (liftedSpace.{max a u r} X)) :
    transportRestrictionTypeValue.{a} R U = transportRestriction.{a} R U := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext W x
  rfl

set_option maxHeartbeats 1400000 in
private theorem siteSectionsSquare (U : Opens (liftedSpace.{max a u r} X))
    (M : AmbientSheaves.{a} R) :
    (liftedScalars.{a} R U).map ((sectionsRestrictionValue.{a} R (opensEquiv X U)).inv.app M) ≫
      (openSiteSectionsIso.{a} R U).hom.app ((originalRestriction.{a} R (opensEquiv X U)).obj M) ≫
      (AdvancedHomologicalAlgebra.SheafTheory.openSections (liftedRing.{a} R) U).map
        ((transportRestrictionTypeValue.{a} R U).hom.app M) =
    (siteSectionsIso.{a} R U).hom.app M ≫
      (sectionsRestrictionIso (liftedRing.{a} R) U).inv.app ((transport.{a} R).obj M) := by
  let V := opensEquiv X U
  let E := V.sheafOfModulesEquivOver.{max a u r} R
  let D := U.sheafOfModulesEquivOver.{max a u r} (liftedRing.{a} R)
  let P := SheafOfModules.overFunctor.{max a u r} R V
  let Q := transport.{a} R ⋙ SheafOfModules.overFunctor (liftedRing.{a} R) U
  let T := transportOver.{a} R U
  let F := SheafOfModules.evaluation.{max a u r} (R.over V) (op (Over.mk (𝟙 V)))
  let G := SheafOfModules.evaluation.{max a u r} ((liftedRing.{a} R).over U) (op (Over.mk (𝟙 U)))
  let H := liftedScalars.{a} R U
  let p := Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.transportOverRestrictionValue.{a,u,r}
    X R U
  let s := overSiteSectionsIso.{a} R U
  have he : (siteSectionsIso.{a} R U).hom.app M =
      (ambientSectionsOfOver T G H P F Q p s).hom.app M := by
    ext x
    rfl
  rw [he]
  exact sectionsSquareOfOver E D P Q T F G H p s M

set_option maxHeartbeats 150000 in
private theorem ambientSectionsSquare (U : Opens X) (M : AmbientSheaves.{a} R) :
    (ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U))).map
      ((sectionsRestrictionValue.{a} R U).inv.app M) ≫
      (openAmbientSectionsIso.{a,u,r,b} R U).hom.app ((originalRestriction.{a} R U).obj M) ≫
      (openSectionsValue.{max a b} R U).map ((ambientRestrictionIso.{a,u,r,b} R U).hom.app M) =
    (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{b,u,r,max a u r}
      X R U).inv.app M ≫
      (sectionsRestrictionValue.{max a b} R U).inv.app
        ((liftSheafCoefficients.{b,u,r,max a u r} R).obj M) := by
  ext x
  rfl

end SectionSquares

set_option maxHeartbeats 1000000 in
private theorem openSections_acyclic_of_flasque {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (OpenModules.{a} R U)] (M : OpenModules.{a} R U)
    (hM : IsFlasque (X := TopCat.of U) (U.sheafRestrict.obj R) M) :
    letI := openModulesAbelian.{a} R U
    Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue
      (openSectionsValue.{a} R U) M := by
  let S := U.sheafRestrict.obj R
  let W := terminalSubspaceOpen U
  letI := openModulesAbelian.{a} R U
  let F := sectionsValue.{a} (X := TopCat.of U) S W
  letI : F.Additive := ⟨by intros; ext x; rfl⟩
  let G := openSectionsValue.{a} R U
  let φ := (terminalSectionRingIso R U).hom
  let H := ModuleCat.restrictScalars.{max a u r} φ.hom
  let e := RingEquiv.ofBijective φ.hom (ConcreteCategory.bijective_of_isIso φ)
  letI : H.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars.{max a u r} e.toRingHom).IsEquivalence
  letI : H.IsLeftAdjoint := H.asEquivalence.isLeftAdjoint_functor
  letI : H.IsRightAdjoint := H.asEquivalence.isRightAdjoint_functor
  letI : H.Additive := ⟨by intros; ext x; rfl⟩
  letI : PreservesFiniteLimits H := inferInstance
  letI : PreservesFiniteColimits H := inferInstance
  letI : H.PreservesHomology := inferInstance
  letI : PreservesFiniteLimits F := original_sections_left_exact.{a,u,r} (TopCat.of U) S W
  let c := openSectionsEvaluationIso.{a} R U
  letI : PreservesFiniteLimits G := preservesFiniteLimits_of_natIso c
  apply (AcyclicTermComparison.rightVanishing _ _ G M).2
  intro n
  obtain ⟨k, _⟩ := compareResolutions F G (𝟭 _) H c
    (fun N hN ↦ by letI := hN; exact AcyclicTermComparison.rightAcyclic_of_injective _ _)
  exact ((H.map_isZero (flasque.{a,u,r} (X := TopCat.of U) S W M hM n))).of_iso (((k (n + 1)).app M).symm)

private theorem compareSquare_of_scalarEquivalence {B C : Type*} [Category* B] [Category* C]
    (E : C ≌ B) {X Y : B} {P Q Z : C} (i : X ⟶ Y)
    (f : E.inverse.obj Y ⟶ P) (p : P ⟶ Z) (e : E.inverse.obj X ⟶ Q) (j : Q ⟶ Z)
    (h : E.inverse.map i ≫ f ≫ p = e ≫ j) :
    i ≫ E.counitIso.inv.app Y ≫ E.functor.map f ≫ E.functor.map p =
      (E.counitIso.inv.app X ≫ E.functor.map e) ≫ E.functor.map j := by
  rw [reassoc_of% (E.counitIso.inv.naturality i), Category.assoc]
  change E.counitIso.inv.app X ≫ E.functor.map (E.inverse.map i) ≫
    E.functor.map f ≫ E.functor.map p =
      E.counitIso.inv.app X ≫ E.functor.map e ≫ E.functor.map j
  rw [← E.functor.map_comp_assoc, ← E.functor.map_comp, Category.assoc,
    h, E.functor.map_comp]

set_option maxHeartbeats 2000000 in
theorem localitySiteCoherence : localitySiteCoherenceType.{a,u,r} := by
  intro X R U _ _
  dsimp only
  let V := opensEquiv X U
  letI := openModulesAbelian.{a} R V
  let S := originalRestriction.{a} R V
  let T := restriction (liftedRing.{a} R) U
  let J := transport.{a} R
  let K := transportOnOpen.{a} R U
  let H := liftedScalars.{a} R U
  let F := sectionsValue.{a} R V
  let F' := openSectionsValue.{a} R V
  let G := sectionsValue.{0} (liftedRing.{a} R) U
  let G' := AdvancedHomologicalAlgebra.SheafTheory.openSections (liftedRing.{a} R) U
  obtain ⟨e, he⟩ := siteComparison.{a,u,r} R U
  obtain ⟨e', he'⟩ := compareResolutions F' G' K H (openSiteSectionsIso.{a} R U)
    (fun M hM ↦ by
      letI : Injective (K.obj M) := K.asEquivalence.map_injective_iff M |>.2 hM
      exact AcyclicTermComparison.rightAcyclic_of_injective _ _)
  obtain ⟨l, _, _, hl⟩ := locality.{a,u,r} R V
  obtain ⟨l', _, _, hl'⟩ := SheafCohomology.locality (liftedRing.{a} R) U
  refine ⟨e, e', l, l', he, he', hl, hl', ?_⟩
  intro M n
  obtain ⟨I, i, _, hi, hI, hb⟩ := InjectiveComplexReplacement.replacement _
    ((CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M) 0 inferInstance
  letI := hb
  let JI := (J.mapHomologicalComplex (.up ℤ)).obj I
  have hJI : ∀ q : ℤ, Injective (JI.X q) := fun q ↦
    (transportEquivalence.{a} R).map_injective_iff (I.X q) |>.2 (hI q)
  letI := resolution.{a,u,r} R V M I i hi hI n
  have h :
      H.map ((l n).hom.app M) ≫ (e' n).hom.app (S.obj M) ≫
        (rightValue G' n).map ((transportRestrictionTypeValue.{a} R U).hom.app M) =
      (e n).hom.app M ≫ (l' n).hom.app (J.obj M) := by
    refine localitySquare_of_models S T J K (transportRestrictionTypeValue.{a} R U) i F F' G G' H
      (siteSectionsIso.{a} R U) (openSiteSectionsIso.{a} R U)
      (sectionsRestrictionValue.{a} R V).symm (sectionsRestrictionIso (liftedRing.{a} R) U).symm hi n
      e e' l l' he he' hl hI ?_ (siteSectionsSquare.{a,u,r} R U)
    intro hiJ
    obtain ⟨hiTJ, _, hlI'⟩ := hl' (J.obj M) JI (mapAugmentation J i) hiJ hJI
    exact ⟨hiTJ, hlI'⟩
  refine ⟨h, ?_⟩
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r}
    (sectionRingEquiv.{a} R U)
  have hs := compareSquare_of_scalarEquivalence E ((l n).hom.app M)
    ((e' n).hom.app (S.obj M))
    ((rightValue G' n).map ((transportRestrictionTypeValue.{a} R U).hom.app M))
    ((e n).hom.app M) ((l' n).hom.app (J.obj M)) h
  simpa only [recoverOriginalScalars, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Category.id_comp, Category.comp_id] using! hs

set_option maxHeartbeats 2800000 in
theorem localityAmbientCoherence : localityAmbientCoherenceType.{a,u,r,b} := by
  intro X R U _ _ _ _
  dsimp only
  letI := openModulesAbelian.{a} R U
  letI := openModulesAbelian.{max a b} R U
  let F := sectionsValue.{a} R U
  let F' := openSectionsValue.{a} R U
  let G := sectionsValue.{max a b} R U
  let G' := openSectionsValue.{max a b} R U
  let S := originalRestriction.{a} R U
  let T := originalRestriction.{max a b} R U
  let J := liftSheafCoefficients.{b,u,r,max a u r} R
  let K := liftOpenCoefficients.{a,u,r,b} R U
  let H := ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U))
  let c := (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{b,u,r,max a u r}
    X R U).symm
  let c' := openAmbientSectionsIso.{a,u,r,b} R U
  have hT' := original_restriction_exact.{max a b,u,r} X R U
  letI := hT'.1
  letI := hT'.2
  have hT : ∀ M, Injective M → Injective (T.obj M) := by
    obtain ⟨_, _, _, _, hT⟩ := original_open_extension.{max a b,u,r} X R U
    exact hT
  have hK' := coefficient_lift_ambient_sheaf_exact.{b,u,r,a} (TopCat.of U) (U.sheafRestrict.obj R)
  letI := hK'.1
  letI := hK'.2
  letI := original_sections_left_exact.{max a b,u,r} X R U
  have hK (M : OpenModules.{a} R U) (hM : Injective M) :
      Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue G' (K.obj M) :=
    openSections_acyclic_of_flasque.{max a b,u,r} R U (K.obj M)
      ((coefficient_lift_flasque.{b,u,r,max a u r} (TopCat.of U) (U.sheafRestrict.obj R) M).2
        (original_injectives_flasque.{a,u,r} (TopCat.of U) (U.sheafRestrict.obj R) M hM))
  have hJ (M : AmbientSheaves.{a} R) (hM : Injective M) :
      Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue G (J.obj M) := by
    apply (AcyclicTermComparison.rightVanishing _ _ G _).2
    intro n
    exact flasque.{max b a,u,r} R U (J.obj M)
      ((coefficient_lift_flasque.{b,u,r,max a u r} X R M).2
        (original_injectives_flasque.{a,u,r} X R M hM)) n
  obtain ⟨e, he⟩ := ambientComparison.{a,u,r,b} R U
  obtain ⟨e', he'⟩ := compareResolutions F' G' K H c' hK
  obtain ⟨l, _, _, hl⟩ := locality.{a,u,r} R U
  let l' := restrictionValueIso T G' G (sectionsRestrictionValue.{max a b} R U) hT
  have hl' (M : AmbientSheaves.{max a b} R) (L : CochainComplex (AmbientSheaves.{max a b} R) ℤ)
      [L.IsStrictlyGE 0]
      (i : (CochainComplex.singleFunctor (AmbientSheaves.{max a b} R) 0).obj M ⟶ L)
      (hi : QuasiIso i) (hiT : QuasiIso (mapAugmentation T i)) (n : ℕ) :
        resolutionModelMap G i hi n ≫ (l' n).hom.app M =
          HomologicalComplex.homologyMap
            ((Functor.mapHomologicalComplexCompIso (sectionsRestrictionValue.{max a b} R U)
              (.up ℤ)).inv.app L) (n : ℤ) ≫
              resolutionModelMap G' (mapAugmentation T i) hiT n :=
    restrictionValueIso_model T G' G (sectionsRestrictionValue.{max a b} R U) hT i hi hiT n
  refine ⟨e, e', l, l', he, he', hl, ?_, ?_, ?_⟩
  · intro M I _ i hi hI
    let hiT := mapAugmentation_quasiIso T i hi
    exact ⟨hiT, fun q ↦ hT _ (hI q), hl' M I i hi hiT⟩
  · intro M I _ i hi hI
    obtain ⟨hiJ, _⟩ := he M I i hi hI
    let hiTJ := mapAugmentation_quasiIso T _ hiJ
    refine ⟨hiJ, hiTJ, fun n ↦ ?_⟩
    let r := hl' (J.obj M) _ (mapAugmentation J i) hiJ hiTJ n
    letI := SheafCohomology.resolutionModelMap_isIso G _ hiJ (fun q ↦ hJ _ (hI q)) n
    exact ⟨inferInstance, IsIso.of_isIso_fac_left r.symm, r⟩
  · intro M n
    obtain ⟨I, i, _, hi, hI, hb⟩ := InjectiveComplexReplacement.replacement _
      ((CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M) 0 inferInstance
    letI := hb
    let JI := (J.mapHomologicalComplex (.up ℤ)).obj I
    letI := resolution.{a,u,r} R U M I i hi hI n
    refine localitySquare_of_models S T J K (ambientRestrictionIso.{a,u,r,b} R U) i F F' G G' H
      c c' (sectionsRestrictionValue.{a} R U).symm (sectionsRestrictionValue.{max a b} R U).symm hi n
      e e' l l' he he' hl hI ?_ (ambientSectionsSquare.{a,u,r,b} R U)
    intro hiJ
    let hiTJ := mapAugmentation_quasiIso T _ hiJ
    exact ⟨hiTJ, hl' (J.obj M) JI _ hiJ hiTJ⟩

end LocalityTransport

universe c d e f g w m v

section SectionwiseSequences

theorem sectionwiseCoefficientLongExact : sectionwiseCoefficientLongExactType.{a,u,r,b,c,d} := by
  intro X R U _ S hS
  dsimp only
  have hT := (sectionwise_short_exact.{a,u,r,b,c,d} X R S).1 hS
  have hF := longExact.{max a b c d,u,r} R U
  exact ⟨hT, fun n ↦ ⟨hF.exact₁ hT n, hF.exact₂ hT n, hF.exact₃ hT n⟩, hF.mono_zero hT⟩

theorem sectionwiseCoefficientNaturality :
    sectionwiseCoefficientNaturalityType.{a,u,r,b,c,d,e,f,g} := by
  intro X R U _ S T h hs ht
  dsimp only
  have hs' := (sectionwise_short_exact.{max a e f g,u,r,b,c,d} X R S).1 hs
  have ht' := (sectionwise_short_exact.{max a b c d,u,r,e,f,g} X R T).1 ht
  exact ⟨hs', ht', (longExact.{max a b c d e f g,u,r} R U).naturality hs' ht' h.lift.{a}⟩

theorem sectionwiseLocality : sectionwiseLocalityType.{a,u,r,b,c,d} := by
  intro X R U _ _
  dsimp only
  letI := openModulesAbelian.{max a b c d} R U
  obtain ⟨l, h₀, hδ, hmodel⟩ := locality.{max a b c d,u,r} R U
  refine ⟨l, hmodel, h₀, fun S hS ↦ ?_⟩
  have hT := (sectionwise_short_exact.{a,u,r,b,c,d} X R S).1 hS
  obtain ⟨hJT, h⟩ := hδ (S.lift.{a}) hT
  exact ⟨hT, hJT, h⟩

/-- Successive coefficient lifts preserve the given section under the canonical
identification with a single lift. -/
private def flattenCoefficientLift {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    liftSheafCoefficients.{v,u,r,m} R ⋙ liftSheafCoefficients.{w,u,r,max v m} R ≅
      liftSheafCoefficients.{max v w m,u,r,m} R :=
  NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk
        (fun V ↦ ((ULift.moduleEquiv.trans ULift.moduleEquiv).trans
          (ULift.moduleEquiv (R := R.obj.obj V) (M := M.val.obj V)).symm).toModuleIso)
        (by intros; rfl)))
    (by intro M N h; apply SheafOfModules.hom_ext; ext V s; rfl)

set_option maxHeartbeats 1800000 in
private def flattenSectionwiseLift {X : TopCat.{u}} {R : X.Sheaf RingCat.{r}}
    (S : SectionwiseShortComplex.{u,r,b,c,d} R)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a b c d w u r}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a b c d w u r}] :
    (S.lift.{a}).map (liftSheafCoefficients.{w,u,r,max a b c d u r} R) ≅ S.lift.{max a w} :=
  ShortComplex.isoMk
    (flattenCoefficientLift.{u,r,w,b,max a u r b c d} R |>.app S.first)
    (flattenCoefficientLift.{u,r,w,c,max a u r b c d} R |>.app S.middle)
    (flattenCoefficientLift.{u,r,w,d,max a u r b c d} R |>.app S.last)
    (by apply SheafOfModules.hom_ext; ext V s; rfl)
    (by apply SheafOfModules.hom_ext; ext V s; rfl)

set_option maxHeartbeats 1800000 in
theorem sectionwiseAmbientComparison : sectionwiseAmbientComparisonType.{a,u,r,b,c,d,w} := by
  intro X R U _ _
  dsimp only
  letI := sectionHasSheafify.{max a b c d r w,u} X
  letI := sectionWEqualsLocallyBijective.{max a b c d r w,u} X
  let G := sectionsValue.{max a b c d w} R U
  obtain ⟨e, he, h₀, hδ⟩ := ambientComparisonExact.{max a b c d,u,r,w} R U
  refine ⟨e, he, h₀, fun S hS ↦ ?_⟩
  have hT := (sectionwise_short_exact.{a,u,r,b,c,d} X R S).1 hS
  have hT' := (sectionwise_short_exact.{max a w,u,r,b,c,d} X R S).1 hS
  let k := flattenSectionwiseLift.{a,u,r,b,c,d,w} S
  refine ⟨k, hT, hT', fun _ _ _ _ ↦ ⟨rfl, rfl, rfl⟩, fun n ↦ ?_⟩
  obtain ⟨hJT, hb⟩ := hδ (S.lift.{a}) hT
  have hn := (longExact.{max a b c d w,u,r} R U).naturality hJT hT' k.hom n
  change (rightValue G n).map k.hom.τ₃ ≫ rightBoundary G hT' n =
    rightBoundary G hJT n ≫ (rightValue G (n + 1)).map k.hom.τ₁ at hn
  rw [hn, reassoc_of% (hb n)]

private def ambientCohomologyIso {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)] :
    ∀ n : ℕ,
      rightValue (sectionsValue.{a} R U) n ⋙
        ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U)) ≅
      liftSheafCoefficients.{b,u,r,max a u r} R ⋙ rightValue (sectionsValue.{max a b} R U) n :=
  (ambientComparisonExact.{a,u,r,b} R U).choose

private def ambientCohomologyEquiv {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (M : AmbientSheaves.{a} R) (n : ℕ) :
    (rightValue (sectionsValue.{a} R U) n).obj M ≃ₗ[R.obj.obj (op U)]
      (rightValue (sectionsValue.{max a b} R U) n).obj
        ((liftSheafCoefficients.{b,u,r,max a u r} R).obj M) :=
  ULift.moduleEquiv.symm.trans ((ambientCohomologyIso.{a,u,r,b} R U n).app M).toLinearEquiv

private theorem ambientCohomologyEquiv_zero {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (M : AmbientSheaves.{a} R) (x : M.val.obj (op U)) :
    ambientCohomologyEquiv.{a,u,r,b} R U M 0
        ((rightDegreeZeroUnit (sectionsValue.{a} R U)).app M x) =
      (rightDegreeZeroUnit (sectionsValue.{max a b} R U)).app
        ((liftSheafCoefficients.{b,u,r,max a u r} R).obj M) (ULift.up x) := by
  have h := NatTrans.congr_app (ambientComparisonExact.{a,u,r,b} R U).choose_spec.2.1 M
  exact congr($(h) (ULift.up x))

private theorem ambientCohomologyEquiv_boundary {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (S : ShortComplex (AmbientSheaves.{a} R)) (hS : S.ShortExact)
    (hJS : (S.map (liftSheafCoefficients.{b,u,r,max a u r} R)).ShortExact)
    (n : ℕ) (x : (rightValue (sectionsValue.{a} R U) n).obj S.X₃) :
    ambientCohomologyEquiv.{a,u,r,b} R U S.X₁ (n + 1) (rightBoundary (sectionsValue.{a} R U) hS n x) =
      rightBoundary (sectionsValue.{max a b} R U) hJS n (ambientCohomologyEquiv.{a,u,r,b} R U S.X₃ n x) := by
  obtain ⟨_, h⟩ := (ambientComparisonExact.{a,u,r,b} R U).choose_spec.2.2 S hS
  exact congr($(h n) (ULift.up x)).symm

private theorem ambientCohomologyEquiv_naturality {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    {M N : AmbientSheaves.{a} R} (h : M ⟶ N) (n : ℕ) (x : (rightValue (sectionsValue.{a} R U) n).obj M) :
    ambientCohomologyEquiv.{a,u,r,b} R U N n ((rightValue (sectionsValue.{a} R U) n).map h x) =
      (rightValue (sectionsValue.{max a b} R U) n).map
        ((liftSheafCoefficients.{b,u,r,max a u r} R).map h)
        (ambientCohomologyEquiv.{a,u,r,b} R U M n x) :=
  congr($((ambientCohomologyIso.{a,u,r,b} R U n).hom.naturality h) (ULift.up x))

/-- Removing a redundant universe parameter from the lift changes no original
section or scalar action. -/
private def reduceCoefficientLift {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    liftSheafCoefficients.{max v m,u,r,m} R ≅ liftSheafCoefficients.{v,u,r,m} R :=
  NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk
        (fun V ↦ (ULift.moduleEquiv.trans
          (ULift.moduleEquiv (R := R.obj.obj V) (M := M.val.obj V)).symm).toModuleIso)
        (by intros; rfl)))
    (by intro M N h; apply SheafOfModules.hom_ext; ext V x; rfl)

private def flattenAmbientLift {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    liftSheafCoefficients.{a,u,r,max b u r} R ⋙
        liftSheafCoefficients.{w,u,r,max a b u r} R ≅
      liftSheafCoefficients.{max a w,u,r,max b u r} R :=
  flattenCoefficientLift.{u,r,w,max b u r,a} R ≪≫
    reduceCoefficientLift.{u,r,max b u r,max a w} R

set_option maxHeartbeats 2800000 in
/-- The composition of the two normalized ambient comparisons is the normalized
comparison for the direct lift. The proof uses the degree-zero unit and the
surjective connecting map of an injective embedding. -/
private theorem ambientCohomologyEquiv_comp {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    [EnoughInjectives (AmbientSheaves.{max a b w} R)]
    (M : AmbientSheaves.{b} R) (n : ℕ) (x : (rightValue (sectionsValue.{b} R U) n).obj M) :
    letI := sectionHasSheafify.{max a b r w,u} X
    letI := sectionWEqualsLocallyBijective.{max a b r w,u} X
    let J := liftSheafCoefficients.{a,u,r,max b u r} R
    let G := sectionsValue.{max a b w} R U
    (rightValue G n).map ((flattenAmbientLift.{a,u,r,b,w} R).hom.app M)
        (ambientCohomologyEquiv.{max a b,u,r,w} R U (J.obj M) n
          (ambientCohomologyEquiv.{b,u,r,a} R U M n x)) =
      ambientCohomologyEquiv.{b,u,r,max a w} R U M n x := by
  dsimp only
  letI := sectionHasSheafify.{max a b r,u} X
  letI := sectionWEqualsLocallyBijective.{max a b r,u} X
  letI := sectionHasSheafify.{max a b r w,u} X
  letI := sectionWEqualsLocallyBijective.{max a b r w,u} X
  let F := sectionsValue.{b} R U
  let G := sectionsValue.{max a b w} R U
  let J := liftSheafCoefficients.{a,u,r,max b u r} R
  let J' := liftSheafCoefficients.{w,u,r,max a b u r} R
  let J'' := liftSheafCoefficients.{max a w,u,r,max b u r} R
  let k := flattenAmbientLift.{a,u,r,b,w} R
  let E := ambientCohomologyEquiv.{b,u,r,a} R U
  let E' := ambientCohomologyEquiv.{max a b,u,r,w} R U
  let E'' := ambientCohomologyEquiv.{b,u,r,max a w} R U
  change (rightValue G n).map (k.hom.app M) (E' (J.obj M) n (E M n x)) = E'' M n x
  induction n generalizing M with
  | zero =>
    letI := zero.{b,u,r} R U
    let h := (rightDegreeZeroUnit F).app M
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective h).1 inferInstance x
    have he := ambientCohomologyEquiv_zero.{b,u,r,a} R U M x
    have he' := ambientCohomologyEquiv_zero.{max a b,u,r,w} R U (J.obj M) (ULift.up x)
    have he'' := ambientCohomologyEquiv_zero.{b,u,r,max a w} R U M x
    change E M 0 (h x) = (rightDegreeZeroUnit (sectionsValue.{max a b} R U)).app (J.obj M) (ULift.up x) at he
    rw [he]
    erw [he', he'']
    exact congr($((rightDegreeZeroUnit G).naturality (k.hom.app M)) (ULift.up (ULift.up x))).symm
  | succ n ih =>
    let S := UniversalDeltaFunctors.injectiveSequence M
    let hS := UniversalDeltaFunctors.injectiveSequence_shortExact M
    haveI : Epi (rightBoundary F hS n) :=
      UniversalDeltaFunctors.dimensionShift_epi (systemValue.{b} R U)
        (longExact.{b,u,r} R U) (fun I _ j ↦ ClassicalDerivedValues.rightInjectiveVanishing _ _ F I j) M n
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (rightBoundary F hS n)).1 inferInstance x
    obtain ⟨hJS, _⟩ := (ambientComparisonExact.{b,u,r,a} R U).choose_spec.2.2 S hS
    obtain ⟨hJ'JS, _⟩ := (ambientComparisonExact.{max a b,u,r,w} R U).choose_spec.2.2 (S.map J) hJS
    obtain ⟨hJ''S, _⟩ := (ambientComparisonExact.{b,u,r,max a w} R U).choose_spec.2.2 S hS
    let p : (S.map J).map J' ≅ S.map J'' :=
      ShortComplex.isoMk (k.app S.X₁) (k.app S.X₂) (k.app S.X₃)
        ((k.hom.naturality S.f).symm) ((k.hom.naturality S.g).symm)
    have hd := (longExact.{max a b w,u,r} R U).naturality hJ'JS hJ''S p.hom n
    have he : E M (n + 1) (rightBoundary F hS n y) =
        rightBoundary (sectionsValue.{max a b} R U) hJS n (E S.X₃ n y) :=
      ambientCohomologyEquiv_boundary.{b,u,r,a} R U S hS hJS n y
    have he' : E' (J.obj M) (n + 1)
          (rightBoundary (sectionsValue.{max a b} R U) hJS n (E S.X₃ n y)) =
        rightBoundary G hJ'JS n (E' (J.obj S.X₃) n (E S.X₃ n y)) :=
      ambientCohomologyEquiv_boundary.{max a b,u,r,w} R U (S.map J) hJS hJ'JS n (E S.X₃ n y)
    have he'' : E'' M (n + 1) (rightBoundary F hS n y) =
        rightBoundary G hJ''S n (E'' S.X₃ n y) :=
      ambientCohomologyEquiv_boundary.{b,u,r,max a w} R U S hS hJ''S n y
    have hp : (rightValue G (n + 1)).map (k.hom.app M)
          (rightBoundary G hJ'JS n (E' (J.obj S.X₃) n (E S.X₃ n y))) =
        rightBoundary G hJ''S n
          ((rightValue G n).map (k.hom.app S.X₃) (E' (J.obj S.X₃) n (E S.X₃ n y))) :=
      congr($(hd) (E' (J.obj S.X₃) n (E S.X₃ n y))).symm
    rw [he, he', he'', hp, ih S.X₃ y]

/-- Compare the cohomology in the coefficient's own adequate category with
its value on the direct lift in the common category. -/
def individualCohomologyIso (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)] :
    IndividualCohomologyComparison.{a,u,r,b} X R U := fun n ↦
  let J₀ := liftSheafCoefficients.{max u r,u,r,b} R
  let J := liftSheafCoefficients.{a,u,r,max b u r} R
  let H := ModuleCat.uliftFunctor.{a,max b u r} (R.obj.obj (op U))
  let F := sectionsValue.{b} R U
  let G := sectionsValue.{max a b} R U
  let k := flattenCoefficientLift.{u,r,a,b,max u r} R
  Functor.associator J₀ (rightValue F n) H ≪≫
    isoWhiskerLeft J₀ (ambientCohomologyIso.{b,u,r,a} R U n) ≪≫
    (Functor.associator J₀ J (rightValue G n)).symm ≪≫
    isoWhiskerRight k (rightValue G n)

private theorem individualCohomologyIso_hom_app {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (M : SheafOfModules.{b} R) (n : ℕ) :
    (individualCohomologyIso.{a,u,r,b} X R U n).hom.app M =
      (ambientCohomologyIso.{b,u,r,a} R U n).hom.app
        ((liftSheafCoefficients.{max u r,u,r,b} R).obj M) ≫
      (rightValue (sectionsValue.{max a b} R U) n).map
        ((flattenCoefficientLift.{u,r,a,b,max u r} R).hom.app M) := by
  simp only [individualCohomologyIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Iso.symm_hom, Functor.associator_inv_app, isoWhiskerRight_hom, whiskerRight_app]
  erw [Category.id_comp, Category.id_comp]

theorem individualCohomologyIso_normalized (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)] :
    IsIndividualCohomologyComparison X R U (individualCohomologyIso.{a,u,r,b} X R U) := by
  obtain ⟨he, h₀, _⟩ := (ambientComparisonExact.{b,u,r,a} R U).choose_spec
  exact ⟨flattenCoefficientLift.{u,r,a,b,max u r} R, ambientCohomologyIso.{b,u,r,a} R U,
    fun _ _ _ ↦ rfl, he, h₀, individualCohomologyIso_hom_app.{a,u,r,b} R U⟩

private def individualCohomologyEquiv {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (M : SheafOfModules.{b} R) (n : ℕ) :
    (coefficientCohomologyValue.{b} X R U n).obj M ≃ₗ[R.obj.obj (op U)]
      (rightValue (sectionsValue.{max a b} R U) n).obj
        ((liftSheafCoefficients.{max a b u r,u,r,b} R).obj M) :=
  ULift.moduleEquiv.symm.trans ((individualCohomologyIso.{a,u,r,b} X R U n).app M).toLinearEquiv

private theorem individualCohomologyEquiv_apply {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (M : SheafOfModules.{b} R) (n : ℕ) (x : (coefficientCohomologyValue.{b} X R U n).obj M) :
    individualCohomologyEquiv.{a,u,r,b} R U M n x =
      (rightValue (sectionsValue.{max a b} R U) n).map
        ((flattenCoefficientLift.{u,r,a,b,max u r} R).hom.app M)
        (ambientCohomologyEquiv.{b,u,r,a} R U
          ((liftSheafCoefficients.{max u r,u,r,b} R).obj M) n x) := by
  exact congr($(individualCohomologyIso_hom_app.{a,u,r,b} R U M n) (ULift.up x))

set_option maxHeartbeats 2800000 in
private theorem individualCohomologyEquiv_comp {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    [EnoughInjectives (AmbientSheaves.{max a b w} R)]
    (M : SheafOfModules.{b} R) (n : ℕ) (x : (coefficientCohomologyValue.{b} X R U n).obj M) :
    letI := sectionHasSheafify.{max a b r w,u} X
    letI := sectionWEqualsLocallyBijective.{max a b r w,u} X
    let J := liftSheafCoefficients.{max a b u r,u,r,b} R
    let k := flattenCoefficientLift.{u,r,w,b,max a b u r} R
    (rightValue (sectionsValue.{max a b w} R U) n).map (k.hom.app M)
        (ambientCohomologyEquiv.{max a b,u,r,w} R U (J.obj M) n
          (individualCohomologyEquiv.{a,u,r,b} R U M n x)) =
      individualCohomologyEquiv.{max a w,u,r,b} R U M n x := by
  dsimp only
  letI := sectionHasSheafify.{max a b r w,u} X
  letI := sectionWEqualsLocallyBijective.{max a b r w,u} X
  let J₀ := liftSheafCoefficients.{max u r,u,r,b} R
  let J₂ := liftSheafCoefficients.{w,u,r,max a b u r} R
  let k := flattenCoefficientLift.{u,r,w,b,max a b u r} R
  let k₁ := flattenCoefficientLift.{u,r,a,b,max u r} R
  let k₂ := flattenCoefficientLift.{u,r,max a w,b,max u r} R
  let k₃ := flattenAmbientLift.{a,u,r,b,w} R
  let H := rightValue (sectionsValue.{max a b w} R U) n
  have he : J₂.map (k₁.hom.app M) ≫ k.hom.app M = k₃.hom.app (J₀.obj M) ≫ k₂.hom.app M := by
    apply SheafOfModules.hom_ext
    ext V s
    rfl
  rw [individualCohomologyEquiv_apply, individualCohomologyEquiv_apply]
  rw [ambientCohomologyEquiv_naturality]
  have hmap := congrArg H.map he
  simp only [Functor.map_comp] at hmap
  let y := ambientCohomologyEquiv.{max a b,u,r,w} R U
    ((liftSheafCoefficients.{a,u,r,max b u r} R).obj (J₀.obj M)) n
    (ambientCohomologyEquiv.{b,u,r,a} R U (J₀.obj M) n x)
  change H.map (k.hom.app M) (H.map (J₂.map (k₁.hom.app M)) y) = H.map (k₂.hom.app M) _
  refine (congr($(hmap) y)).trans ?_
  exact congrArg (H.map (k₂.hom.app M)) (ambientCohomologyEquiv_comp.{a,u,r,b,w} R U (J₀.obj M) n x)

section LinearConjugation

variable {K : Type*} [Ring K]
  {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module K A] [Module K B] [Module K C]
  {A' B' C' : ModuleCat.{v} K}

/-- Pull a map of the common section modules back to the original carriers. -/
private def conjugateLinearMap (eA : A ≃ₗ[K] A') (eB : B ≃ₗ[K] B') (f : A' ⟶ B') :
    A →ₗ[K] B :=
  eB.symm.toLinearMap.comp (f.hom.comp eA.toLinearMap)

private theorem conjugateLinearMap_apply (eA : A ≃ₗ[K] A') (eB : B ≃ₗ[K] B')
    (f : A' ⟶ B') (x : A) :
    eB (conjugateLinearMap eA eB f x) = f (eA x) :=
  eB.apply_symm_apply _

private theorem exact_conjugateLinearMap (eA : A ≃ₗ[K] A') (eB : B ≃ₗ[K] B') (eC : C ≃ₗ[K] C')
    (f : A' ⟶ B') (g : B' ⟶ C') (h : ExactPair f g) :
    Function.Exact (conjugateLinearMap eA eB f) (conjugateLinearMap eB eC g) := by
  have h' : Function.Exact f g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (ShortComplex.mk f g h.zero)).1 h.exact
  intro y
  constructor
  · intro hy
    have hy' : g (eB y) = 0 := by
      rw [← conjugateLinearMap_apply eB eC, hy, map_zero]
    obtain ⟨x, hx⟩ := (h' (eB y)).1 hy'
    refine ⟨eA.symm x, eB.injective ?_⟩
    rw [conjugateLinearMap_apply, LinearEquiv.apply_symm_apply, hx]
  · rintro ⟨x, rfl⟩
    apply eC.injective
    rw [conjugateLinearMap_apply, conjugateLinearMap_apply, map_zero]
    exact (h' _).2 ⟨eA x, rfl⟩

private theorem conjugateLinearMap_comp (eA : A ≃ₗ[K] A') (eB : B ≃ₗ[K] B') (eC : C ≃ₗ[K] C')
    (f : A' ⟶ B') (g : B' ⟶ C') :
    (conjugateLinearMap eB eC g).comp (conjugateLinearMap eA eB f) =
      conjugateLinearMap eA eC (f ≫ g) := by
  ext x
  apply eC.injective
  rw [LinearMap.comp_apply, conjugateLinearMap_apply, conjugateLinearMap_apply,
    conjugateLinearMap_apply]
  rfl

private theorem conjugateLinearMap_eq_of_commuting
    {A'' B'' : ModuleCat.{w} K} (eA : A ≃ₗ[K] A') (eB : B ≃ₗ[K] B')
    (eA' : A ≃ₗ[K] A'') (eB' : B ≃ₗ[K] B'') (f : A' ⟶ B') (f' : A'' ⟶ B'')
    (bA : A' → A'') (bB : B' → B'')
    (hA : ∀ x, bA (eA x) = eA' x) (hB : ∀ x, bB (eB x) = eB' x)
    (h : ∀ x, bB (f x) = f' (bA x)) :
    conjugateLinearMap eA eB f = conjugateLinearMap eA' eB' f' := by
  ext x
  apply eB'.injective
  rw [← hB, conjugateLinearMap_apply, conjugateLinearMap_apply, h, hA]

end LinearConjugation

/-- The cohomology map of the given sectionwise linear morphism on the
cohomologies of the two original sheaves. -/
def sectionwiseCohomologyMap {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c} R)]
    {M : SheafOfModules.{b} R} {N : SheafOfModules.{c} R} (h : SectionwiseHom M N) (n : ℕ) :
    (coefficientCohomologyValue.{b} X R U n).obj M →ₗ[R.obj.obj (op U)]
      (coefficientCohomologyValue.{c} X R U n).obj N :=
  conjugateLinearMap (individualCohomologyEquiv.{max a c,u,r,b} R U M n)
    (individualCohomologyEquiv.{max a b,u,r,c} R U N n)
    ((rightValue (sectionsValue.{max a b c} R U) n).map h.lift.{max a u r})

/-- The connecting map on the original cohomology carriers, induced by the
actual derived boundary of the common lift of the coefficient sequence. -/
def sectionwiseBoundary {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{d} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c d} R)]
    (S : SectionwiseShortComplex.{u,r,b,c,d} R) (hS : S.GermLocallyShortExact) (n : ℕ) :
    (coefficientCohomologyValue.{d} X R U n).obj S.last →ₗ[R.obj.obj (op U)]
      (coefficientCohomologyValue.{b} X R U (n + 1)).obj S.first :=
  conjugateLinearMap (individualCohomologyEquiv.{max a b c,u,r,d} R U S.last n)
    (individualCohomologyEquiv.{max a c d,u,r,b} R U S.first (n + 1))
    (rightBoundary (sectionsValue.{max a b c d} R U)
      ((sectionwise_short_exact.{a,u,r,b,c,d} X R S).1 hS) n)

set_option maxHeartbeats 3000000 in
theorem sectionwiseIndividualLongExact : sectionwiseIndividualLongExactType.{a,u,r,b,c,d} := by
  intro X R U _ _ _ _ S hS
  dsimp only
  let T := S.lift.{a}
  let F := sectionsValue.{max a b c d} R U
  let K := R.obj.obj (op U)
  let A (n : ℕ) := (coefficientCohomologyValue.{b} X R U n).obj S.first
  let B (n : ℕ) := (coefficientCohomologyValue.{c} X R U n).obj S.middle
  let D (n : ℕ) := (coefficientCohomologyValue.{d} X R U n).obj S.last
  have hT : T.ShortExact := (sectionwise_short_exact.{a,u,r,b,c,d} X R S).1 hS
  have hF := longExact.{max a b c d,u,r} R U
  let i₁ := individualCohomologyIso.{max a c d,u,r,b} X R U
  let i₂ := individualCohomologyIso.{max a b d,u,r,c} X R U
  let i₃ := individualCohomologyIso.{max a b c,u,r,d} X R U
  let e₁ (n : ℕ) : A n ≃ₗ[K] (rightValue F n).obj T.X₁ :=
    individualCohomologyEquiv.{max a c d,u,r,b} R U S.first n
  let e₂ (n : ℕ) : B n ≃ₗ[K] (rightValue F n).obj T.X₂ :=
    individualCohomologyEquiv.{max a b d,u,r,c} R U S.middle n
  let e₃ (n : ℕ) : D n ≃ₗ[K] (rightValue F n).obj T.X₃ :=
    individualCohomologyEquiv.{max a b c,u,r,d} R U S.last n
  let α := sectionwiseCohomologyMap.{max a d,u,r,b,c} R U S.f
  let β := sectionwiseCohomologyMap.{max a b,u,r,c,d} R U S.g
  let δ := sectionwiseBoundary.{a,u,r,b,c,d} R U S hS
  refine ⟨hT, i₁, i₂, i₃, α, β, δ,
    individualCohomologyIso_normalized.{max a c d,u,r,b} X R U,
    individualCohomologyIso_normalized.{max a b d,u,r,c} X R U,
    individualCohomologyIso_normalized.{max a b c,u,r,d} X R U, ?_, fun n ↦ ?_⟩
  · intro x y hxy
    apply (e₁ 0).injective
    have hf := (ModuleCat.mono_iff_injective _).1 (hF.mono_zero hT)
    apply hf
    exact (conjugateLinearMap_apply (e₁ 0) (e₂ 0) _ x).symm.trans
      ((congrArg (e₂ 0) hxy).trans (conjugateLinearMap_apply (e₁ 0) (e₂ 0) _ y))
  · exact ⟨exact_conjugateLinearMap _ _ _ _ _ (hF.exact₂ hT n),
      exact_conjugateLinearMap _ _ _ _ _ (hF.exact₃ hT n),
      exact_conjugateLinearMap _ _ _ _ _ (hF.exact₁ hT n),
      fun x ↦ (conjugateLinearMap_apply (e₁ n) (e₂ n) _ x).symm,
      fun x ↦ (conjugateLinearMap_apply (e₂ n) (e₃ n) _ x).symm,
      fun x ↦ (conjugateLinearMap_apply (e₃ n) (e₁ (n + 1)) _ x).symm⟩

set_option maxHeartbeats 2800000 in
/-- A diagram on six original coefficient sheaves gives the three commuting
squares of the long exact sequences on their individual cohomology carriers. -/
theorem sectionwiseIndividualNaturality {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
    [EnoughInjectives (AmbientSheaves.{d} R)] [EnoughInjectives (AmbientSheaves.{e} R)]
    [EnoughInjectives (AmbientSheaves.{f} R)] [EnoughInjectives (AmbientSheaves.{g} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c d e f g} R)]
    (S : SectionwiseShortComplex.{u,r,b,c,d} R) (T : SectionwiseShortComplex.{u,r,e,f,g} R)
    (h : S.Hom T) (hs : S.GermLocallyShortExact) (ht : T.GermLocallyShortExact) (n : ℕ) :
    let α := sectionwiseCohomologyMap.{max a d e f g,u,r,b,c} R U S.f n
    let β := sectionwiseCohomologyMap.{max a b e f g,u,r,c,d} R U S.g n
    let δ := sectionwiseBoundary.{max a e f g,u,r,b,c,d} R U S hs n
    let α' := sectionwiseCohomologyMap.{max a b c d g,u,r,e,f} R U T.f n
    let β' := sectionwiseCohomologyMap.{max a b c d e,u,r,f,g} R U T.g n
    let δ' := sectionwiseBoundary.{max a b c d,u,r,e,f,g} R U T ht n
    let u₁ := sectionwiseCohomologyMap.{max a c d f g,u,r,b,e} R U h.τ₁
    let u₂ := sectionwiseCohomologyMap.{max a b d e g,u,r,c,f} R U h.τ₂
    let u₃ := sectionwiseCohomologyMap.{max a b c e f,u,r,d,g} R U h.τ₃
    (u₂ n).comp α = α'.comp (u₁ n) ∧
    (u₃ n).comp β = β'.comp (u₂ n) ∧
    (u₁ (n + 1)).comp δ = δ'.comp (u₃ n) := by
  dsimp only [sectionwiseCohomologyMap, sectionwiseBoundary]
  simp only [conjugateLinearMap_comp]
  let k := h.lift.{a}
  let F := sectionsValue.{max a b c d e f g} R U
  have hs' := (sectionwise_short_exact.{max a e f g,u,r,b,c,d} X R S).1 hs
  have ht' := (sectionwise_short_exact.{max a b c d,u,r,e,f,g} X R T).1 ht
  have hδ := (longExact.{max a b c d e f g,u,r} R U).naturality hs' ht' k n
  have h₁ := congrArg (rightValue F n).map k.comm₁₂
  have h₂ := congrArg (rightValue F n).map k.comm₂₃
  simp only [Functor.map_comp] at h₁ h₂
  exact ⟨congrArg (conjugateLinearMap _ _) h₁.symm,
    congrArg (conjugateLinearMap _ _) h₂.symm,
    congrArg (conjugateLinearMap _ _) hδ.symm⟩

set_option maxHeartbeats 2600000 in
/-- Raising the auxiliary ambient level leaves the map on the original
cohomology modules unchanged. -/
theorem sectionwiseCohomologyMap_enlarge {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c w} R)]
    {M : SheafOfModules.{b} R} {N : SheafOfModules.{c} R} (h : SectionwiseHom M N) (n : ℕ) :
    sectionwiseCohomologyMap.{a,u,r,b,c} R U h n =
      sectionwiseCohomologyMap.{max a w,u,r,b,c} R U h n := by
  letI := sectionHasSheafify.{max a b c r w,u} X
  letI := sectionWEqualsLocallyBijective.{max a b c r w,u} X
  let F := rightValue (sectionsValue.{max a b c} R U) n
  let G := rightValue (sectionsValue.{max a b c w} R U) n
  let J := liftSheafCoefficients.{w,u,r,max a b c u r} R
  let kM := (flattenCoefficientLift.{u,r,w,b,max a b c u r} R).hom.app M
  let kN := (flattenCoefficientLift.{u,r,w,c,max a b c u r} R).hom.app N
  let t := h.lift.{max a u r}
  let t' := h.lift.{max a w u r}
  have hk : J.map t ≫ kN = kM ≫ t' := by
    apply SheafOfModules.hom_ext
    ext V s
    rfl
  let eM := individualCohomologyEquiv.{max a c,u,r,b} R U M n
  let eN := individualCohomologyEquiv.{max a b,u,r,c} R U N n
  let eM' := individualCohomologyEquiv.{max a c w,u,r,b} R U M n
  let eN' := individualCohomologyEquiv.{max a b w,u,r,c} R U N n
  let JM := (liftSheafCoefficients.{max a b c u r,u,r,b} R).obj M
  let JN := (liftSheafCoefficients.{max a b c u r,u,r,c} R).obj N
  let bM (x : F.obj JM) := G.map kM (ambientCohomologyEquiv.{max a b c,u,r,w} R U JM n x)
  let bN (x : F.obj JN) := G.map kN (ambientCohomologyEquiv.{max a b c,u,r,w} R U JN n x)
  change conjugateLinearMap eM eN (F.map t) = conjugateLinearMap eM' eN' (G.map t')
  apply conjugateLinearMap_eq_of_commuting eM eN eM' eN' (F.map t) (G.map t') bM bN
  · exact individualCohomologyEquiv_comp.{max a c,u,r,b,w} R U M n
  · exact individualCohomologyEquiv_comp.{max a b,u,r,c,w} R U N n
  · intro x
    change G.map kN (ambientCohomologyEquiv.{max a b c,u,r,w} R U JN n (F.map t x)) =
      G.map t' (G.map kM (ambientCohomologyEquiv.{max a b c,u,r,w} R U JM n x))
    rw [ambientCohomologyEquiv_naturality]
    have hmap := congrArg G.map hk
    simp only [Functor.map_comp] at hmap
    exact congr($(hmap) (ambientCohomologyEquiv.{max a b c,u,r,w} R U JM n x))

set_option maxHeartbeats 2600000 in
/-- The connecting map on the original cohomologies is independent of a
further enlargement, through the flattening isomorphism of the given sequence. -/
theorem sectionwiseBoundary_enlarge {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{d} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c d} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c d w} R)]
    (S : SectionwiseShortComplex.{u,r,b,c,d} R) (hS : S.GermLocallyShortExact) (n : ℕ) :
    sectionwiseBoundary.{a,u,r,b,c,d} R U S hS n =
      sectionwiseBoundary.{max a w,u,r,b,c,d} R U S hS n := by
  letI := sectionHasSheafify.{max a b c d r w,u} X
  letI := sectionWEqualsLocallyBijective.{max a b c d r w,u} X
  let T := S.lift.{a}
  let T' := S.lift.{max a w}
  let F := sectionsValue.{max a b c d} R U
  let G := sectionsValue.{max a b c d w} R U
  let k := flattenSectionwiseLift.{a,u,r,b,c,d,w} S
  have hT : T.ShortExact := (sectionwise_short_exact.{a,u,r,b,c,d} X R S).1 hS
  have hT' : T'.ShortExact := (sectionwise_short_exact.{max a w,u,r,b,c,d} X R S).1 hS
  obtain ⟨hJT, _⟩ := (ambientComparisonExact.{max a b c d,u,r,w} R U).choose_spec.2.2 T hT
  let e₃ := individualCohomologyEquiv.{max a b c,u,r,d} R U S.last n
  let e₁ := individualCohomologyEquiv.{max a c d,u,r,b} R U S.first (n + 1)
  let e₃' := individualCohomologyEquiv.{max a b c w,u,r,d} R U S.last n
  let e₁' := individualCohomologyEquiv.{max a c d w,u,r,b} R U S.first (n + 1)
  let b₃ (x : (rightValue F n).obj T.X₃) :=
    (rightValue G n).map k.hom.τ₃ (ambientCohomologyEquiv.{max a b c d,u,r,w} R U T.X₃ n x)
  let b₁ (x : (rightValue F (n + 1)).obj T.X₁) :=
    (rightValue G (n + 1)).map k.hom.τ₁ (ambientCohomologyEquiv.{max a b c d,u,r,w} R U T.X₁ (n + 1) x)
  change conjugateLinearMap e₃ e₁ (rightBoundary F hT n) =
    conjugateLinearMap e₃' e₁' (rightBoundary G hT' n)
  apply conjugateLinearMap_eq_of_commuting e₃ e₁ e₃' e₁' (rightBoundary F hT n) (rightBoundary G hT' n) b₃ b₁
  · exact individualCohomologyEquiv_comp.{max a b c,u,r,d,w} R U S.last n
  · exact individualCohomologyEquiv_comp.{max a c d,u,r,b,w} R U S.first (n + 1)
  · intro x
    change (rightValue G (n + 1)).map k.hom.τ₁
        (ambientCohomologyEquiv.{max a b c d,u,r,w} R U T.X₁ (n + 1) (rightBoundary F hT n x)) =
      rightBoundary G hT' n ((rightValue G n).map k.hom.τ₃
        (ambientCohomologyEquiv.{max a b c d,u,r,w} R U T.X₃ n x))
    rw [ambientCohomologyEquiv_boundary.{max a b c d,u,r,w} R U T hT hJT]
    have h := (longExact.{max a b c d w,u,r} R U).naturality hJT hT' k.hom n
    exact congr($(h) (ambientCohomologyEquiv.{max a b c d,u,r,w} R U T.X₃ n x)).symm

section RestrictCohomology

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U V : Opens X} (j : V ⟶ U)

private def restrictionTransformation [EnoughInjectives (AmbientSheaves.{a} R)] :
    ∀ n : ℕ, rightValue (sectionsValue.{a} R U) n ⟶
      rightValue (sectionsValue.{a} R V) n ⋙ restrictSectionScalars.{a} X R j :=
  (restrictionMap.{a,u,r} X R j).choose

private theorem restrictionTransformation_zero [EnoughInjectives (AmbientSheaves.{a} R)]
    (M : AmbientSheaves.{a} R) (x : M.val.obj (op U)) :
    (restrictionTransformation.{a,u,r} R j 0).app M
        ((rightDegreeZeroUnit (sectionsValue.{a} R U)).app M x) =
      (rightDegreeZeroUnit (sectionsValue.{a} R V)).app M (M.val.map j.op x) := by
  have h := NatTrans.congr_app (restrictionMap.{a,u,r} X R j).choose_spec.1 M
  exact congr($(h) x)

private theorem restrictionTransformation_boundary [EnoughInjectives (AmbientSheaves.{a} R)]
    (S : ShortComplex (AmbientSheaves.{a} R)) (hS : S.ShortExact) (n : ℕ)
    (x : (rightValue (sectionsValue.{a} R U) n).obj S.X₃) :
    (restrictionTransformation.{a,u,r} R j (n + 1)).app S.X₁
        (rightBoundary (sectionsValue.{a} R U) hS n x) =
      rightBoundary (sectionsValue.{a} R V) hS n ((restrictionTransformation.{a,u,r} R j n).app S.X₃ x) := by
  have h := (restrictionMap.{a,u,r} X R j).choose_spec.2.1 S hS n
  exact congr($(h) x).symm

set_option maxHeartbeats 2200000 in
private theorem ambientCohomologyEquiv_restriction
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (M : AmbientSheaves.{a} R) (n : ℕ) (x : (rightValue (sectionsValue.{a} R U) n).obj M) :
    ambientCohomologyEquiv.{a,u,r,b} R V M n ((restrictionTransformation.{a,u,r} R j n).app M x) =
      (restrictionTransformation.{max a b,u,r} R j n).app
        ((liftSheafCoefficients.{b,u,r,max a u r} R).obj M) (ambientCohomologyEquiv.{a,u,r,b} R U M n x) := by
  letI := sectionHasSheafify.{max a b r,u} X
  letI := sectionWEqualsLocallyBijective.{max a b r,u} X
  let F := sectionsValue.{a} R U
  let J := liftSheafCoefficients.{b,u,r,max a u r} R
  induction n generalizing M with
  | zero =>
    letI := zero.{a,u,r} R U
    obtain ⟨s, rfl⟩ := (ModuleCat.epi_iff_surjective ((rightDegreeZeroUnit F).app M)).1
      inferInstance x
    rw [restrictionTransformation_zero, ambientCohomologyEquiv_zero,
        ambientCohomologyEquiv_zero, restrictionTransformation_zero]
    rfl
  | succ n ih =>
    let S := UniversalDeltaFunctors.injectiveSequence M
    let hS := UniversalDeltaFunctors.injectiveSequence_shortExact M
    haveI : Epi (rightBoundary F hS n) :=
      UniversalDeltaFunctors.dimensionShift_epi (systemValue.{a} R U)
        (longExact.{a,u,r} R U) (fun I _ q ↦ ClassicalDerivedValues.rightInjectiveVanishing _ _ F I q) M n
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (rightBoundary F hS n)).1 inferInstance x
    obtain ⟨hJS, _⟩ := (ambientComparisonExact.{a,u,r,b} R U).choose_spec.2.2 S hS
    rw [restrictionTransformation_boundary.{a,u,r} R j S hS n y,
      ambientCohomologyEquiv_boundary.{a,u,r,b} R V S hS hJS n,
      ambientCohomologyEquiv_boundary.{a,u,r,b} R U S hS hJS n, ih S.X₃ y]
    exact (restrictionTransformation_boundary.{max a b,u,r} R j (S.map J) hJS n
      (ambientCohomologyEquiv.{a,u,r,b} R U S.X₃ n y)).symm

/-- Restriction on the cohomology of an original coefficient, linear over the
source section ring acting on the target by the given restriction of scalars. -/
def coefficientCohomologyRestriction [EnoughInjectives (AmbientSheaves.{a} R)]
    (M : SheafOfModules.{a} R) (n : ℕ) :
    (coefficientCohomologyValue.{a} X R U n).obj M →ₗ[R.obj.obj (op U)]
      (restrictSectionScalars.{a} X R j).obj ((coefficientCohomologyValue.{a} X R V n).obj M) :=
  ((restrictionTransformation.{a,u,r} R j n).app
    ((liftSheafCoefficients.{max u r,u,r,a} R).obj M)).hom

set_option maxHeartbeats 1800000 in
private theorem individualCohomologyEquiv_restriction
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (M : SheafOfModules.{b} R) (n : ℕ) (x : (coefficientCohomologyValue.{b} X R U n).obj M) :
    individualCohomologyEquiv.{a,u,r,b} R V M n (coefficientCohomologyRestriction.{b,u,r} R j M n x) =
      (restrictionTransformation.{max a b,u,r} R j n).app
        ((liftSheafCoefficients.{max a b u r,u,r,b} R).obj M) (individualCohomologyEquiv.{a,u,r,b} R U M n x) := by
  let A := (liftSheafCoefficients.{max u r,u,r,b} R).obj M
  let J := liftSheafCoefficients.{a,u,r,max b u r} R
  let k := (flattenCoefficientLift.{u,r,a,b,max u r} R).hom.app M
  let E := ambientCohomologyEquiv.{b,u,r,a} R U A n x
  let t := restrictionTransformation.{max a b,u,r} R j n
  rw [individualCohomologyEquiv_apply, individualCohomologyEquiv_apply]
  change (rightValue (sectionsValue.{max a b} R V) n).map k
      (ambientCohomologyEquiv.{b,u,r,a} R V A n ((restrictionTransformation.{b,u,r} R j n).app A x)) =
    t.app _ ((rightValue (sectionsValue.{max a b} R U) n).map k E)
  rw [ambientCohomologyEquiv_restriction.{b,u,r,a} R j]
  exact congr($(t.naturality k) E).symm

set_option maxHeartbeats 2200000 in
/-- Restriction between the given opens commutes with the maps of independently
sized original coefficients on their own cohomology carriers. -/
theorem sectionwiseCohomologyMap_restriction
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c} R)]
    {M : SheafOfModules.{b} R} {N : SheafOfModules.{c} R} (h : SectionwiseHom M N) (n : ℕ)
    (x : (coefficientCohomologyValue.{b} X R U n).obj M) :
    coefficientCohomologyRestriction.{c,u,r} R j N n (sectionwiseCohomologyMap.{a,u,r,b,c} R U h n x) =
      sectionwiseCohomologyMap.{a,u,r,b,c} R V h n (coefficientCohomologyRestriction.{b,u,r} R j M n x) := by
  let e := individualCohomologyEquiv.{max a b,u,r,c} R V N n
  apply e.injective
  change individualCohomologyEquiv.{max a b,u,r,c} R V N n
      (coefficientCohomologyRestriction.{c,u,r} R j N n (sectionwiseCohomologyMap.{a,u,r,b,c} R U h n x)) =
    individualCohomologyEquiv.{max a b,u,r,c} R V N n
      (sectionwiseCohomologyMap.{a,u,r,b,c} R V h n (coefficientCohomologyRestriction.{b,u,r} R j M n x))
  rw [individualCohomologyEquiv_restriction]
  simp only [sectionwiseCohomologyMap, conjugateLinearMap_apply]
  rw [individualCohomologyEquiv_restriction]
  let t := restrictionTransformation.{max a b c,u,r} R j n
  exact congr($(t.naturality h.lift.{max a u r})
    (individualCohomologyEquiv.{max a c,u,r,b} R U M n x))

set_option maxHeartbeats 2600000 in
/-- The actual open restrictions commute with the mixed coefficient boundary on
the original cohomology modules. -/
theorem sectionwiseBoundary_restriction
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{d} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c d} R)]
    (S : SectionwiseShortComplex.{u,r,b,c,d} R) (hS : S.GermLocallyShortExact) (n : ℕ)
    (x : (coefficientCohomologyValue.{d} X R U n).obj S.last) :
    coefficientCohomologyRestriction.{b,u,r} R j S.first (n + 1)
        (sectionwiseBoundary.{a,u,r,b,c,d} R U S hS n x) =
      sectionwiseBoundary.{a,u,r,b,c,d} R V S hS n
        (coefficientCohomologyRestriction.{d,u,r} R j S.last n x) := by
  apply (individualCohomologyEquiv.{max a c d,u,r,b} R V S.first (n + 1)).injective
  rw [individualCohomologyEquiv_restriction]
  simp only [sectionwiseBoundary, conjugateLinearMap_apply]
  rw [individualCohomologyEquiv_restriction]
  have hT := (sectionwise_short_exact.{a,u,r,b,c,d} X R S).1 hS
  exact restrictionTransformation_boundary.{max a b c d,u,r} R j (S.lift.{a}) hT n
    (individualCohomologyEquiv.{max a b c,u,r,d} R U S.last n x)

end RestrictCohomology

end SectionwiseSequences

end AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
