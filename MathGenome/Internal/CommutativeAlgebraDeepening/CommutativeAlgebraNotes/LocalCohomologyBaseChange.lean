import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CechGeneratorIndependence
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalCohomologyBaseChange
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.RingTheory.Localization.Ideal
import Batteries.Tactic.OpenPrivate

/-! Change of rings, flat base change, and support for local cohomology. -/

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory

namespace CommutativeAlgebraNotes

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R
private abbrev Cpx (R : Type u) [CommRing R] := CochainComplex (Mod R) ℤ

local notation "upZ" => ComplexShape.up ℤ

variable {R B : Type u} [CommRing R] [CommRing B]

private abbrev extension (f : R →+* B) : Mod R ⥤ Mod B := ModuleCat.extendScalars f
private abbrev restriction (f : R →+* B) : Mod B ⥤ Mod R := ModuleCat.restrictScalars f

private instance extension_additive (f : R →+* B) : (extension f).Additive where
  map_add := by
    intros
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    simp only [ModuleCat.ExtendScalars.map_tmul, ModuleCat.hom_add, LinearMap.add_apply,
      TensorProduct.tmul_add]

private abbrev extendComplex (f : R →+* B) : Cpx R ⥤ Cpx B :=
  (extension f).mapHomologicalComplex upZ

private abbrev restrictComplex (f : R →+* B) : Cpx B ⥤ Cpx R :=
  (restriction f).mapHomologicalComplex upZ

open private tensorCofan tensorCofanIsColimit from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AugmentedCechComplex

private abbrev Diagonal (k : ℤ) := {ij : ℤ × ℤ // ij.1 + ij.2 = k}

private def mappedTensorCofan (f : R →+* B) (K L : Cpx R) (k : ℤ) :
    Cofan (fun ij : Diagonal k => (extension f).obj (K.X ij.val.1 ⊗ L.X ij.val.2)) :=
  Cofan.mk (((extendComplex f).obj (HomologicalComplex.tensorObj K L)).X k)
    (fun ij => (extension f).map (ιTensorObj K L ij.val.1 ij.val.2 k ij.property))

private def mappedTensorCofanIsColimit (f : R →+* B) (K L : Cpx R) (k : ℤ) :
    IsColimit (mappedTensorCofan f K L k) :=
  (Cofan.isColimitMapCoconeEquiv (extension f) _ (tensorCofan K L k))
    (isColimitOfPreserves (extension f) (tensorCofanIsColimit K L k))

private def tensorDiagramIso (f : R →+* B) (K L : Cpx R) (k : ℤ) :
    Discrete.functor (fun ij : Diagonal k => (extension f).obj (K.X ij.val.1 ⊗ L.X ij.val.2)) ≅
      Discrete.functor (fun ij : Diagonal k =>
        ((extendComplex f).obj K).X ij.val.1 ⊗ ((extendComplex f).obj L).X ij.val.2) :=
  Discrete.natIso (fun ij =>
    (Functor.Monoidal.μIso (extension f) (K.X ij.as.val.1) (L.X ij.as.val.2)).symm)

private def tensorTerm (f : R →+* B) (K L : Cpx R) (k : ℤ) :
    ((extendComplex f).obj (HomologicalComplex.tensorObj K L)).X k ≅
      (HomologicalComplex.tensorObj ((extendComplex f).obj K) ((extendComplex f).obj L)).X k :=
  (mappedTensorCofanIsColimit f K L k).coconePointsIsoOfNatIso
    (tensorCofanIsColimit ((extendComplex f).obj K) ((extendComplex f).obj L) k)
    (tensorDiagramIso f K L k)

@[reassoc]
private lemma tensorTerm_hom_ι (f : R →+* B) (K L : Cpx R) (i j k : ℤ) (h : i + j = k) :
    (extension f).map (ιTensorObj K L i j k h) ≫ (tensorTerm f K L k).hom =
      Functor.OplaxMonoidal.δ (extension f) (K.X i) (L.X j) ≫
        ιTensorObj ((extendComplex f).obj K) ((extendComplex f).obj L) i j k h :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom (mappedTensorCofanIsColimit f K L k)
    (tensorCofanIsColimit ((extendComplex f).obj K) ((extendComplex f).obj L) k)
    (tensorDiagramIso f K L k) ⟨⟨(i, j), h⟩⟩

/-- Extension of scalars commutes with the signed direct-sum tensor of cochain complexes. -/
private def extendTensor (f : R →+* B) (K L : Cpx R) :
    (extendComplex f).obj (HomologicalComplex.tensorObj K L) ≅
      HomologicalComplex.tensorObj ((extendComplex f).obj K) ((extendComplex f).obj L) :=
  HomologicalComplex.Hom.isoOfComponents (tensorTerm f K L) (by
    intro k l h
    change k + 1 = l at h
    subst l
    apply (mappedTensorCofanIsColimit f K L k).hom_ext
    rintro ⟨⟨⟨i, j⟩, h⟩⟩
    dsimp only [mappedTensorCofan, Cofan.mk_ι_app]
    change (extension f).map (ιTensorObj K L i j k h) ≫ _ ≫ _ =
      (extension f).map (ιTensorObj K L i j k h) ≫ (extension f).map _ ≫ _
    subst k
    rw [tensorTerm_hom_ι_assoc, ← Functor.map_comp_assoc, Cech.tensor_d, Cech.tensor_d]
    simp only [Preadditive.comp_add, Functor.map_add, Functor.map_units_smul,
      Linear.comp_units_smul, Preadditive.add_comp, Linear.units_smul_comp,
      Functor.map_comp, Category.assoc, tensorTerm_hom_ι,
      Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_X,
      Functor.OplaxMonoidal.δ_natural_left_assoc, Functor.OplaxMonoidal.δ_natural_right_assoc])

private def extendStalk (f : R →+* B) :
    single (Mod R) upZ 0 ⋙ extendComplex f ≅
      extension f ⋙ single (Mod B) upZ 0 :=
  singleMapHomologicalComplex (extension f) upZ 0

private def extendUnit (f : R →+* B) :
    (extendComplex f).obj (tensorUnit (Mod R) upZ) ≅ tensorUnit (Mod B) upZ :=
  (extendStalk f).app (𝟙_ (Mod R)) ≪≫
    (single (Mod B) upZ 0).mapIso (Functor.Monoidal.εIso (extension f)).symm

private def extendLocalization (f : R →+* B) (r : R) :
    (extension f).obj (ModuleCat.of R (Localization.Away r)) ≅
      ModuleCat.of B (Localization.Away (f r)) :=
  letI := f.toAlgebra
  (IsLocalization.Away.tensorEquiv B (r := r) (A := Localization.Away r)).toLinearEquiv.toModuleIso

private def factorTerm (f : R →+* B) (r : R) (k : ℤ) :
    ((extendComplex f).obj (Cech.factor r)).X k ≅ (Cech.factor (f r)).X k :=
  if hk : k = 0 then by
    subst k
    change (extension f).obj (𝟙_ (Mod R)) ≅ 𝟙_ (Mod B)
    exact (Functor.Monoidal.εIso (extension f)).symm
  else if hk' : k = 1 then by
    subst k
    exact extendLocalization f r
  else
    ((extension f).map_isZero (Cech.factor_isZero r k hk hk')).iso
      (Cech.factor_isZero (f r) k hk hk')

private def extendFactor (f : R →+* B) (r : R) :
    (extendComplex f).obj (Cech.factor r) ≅ Cech.factor (f r) :=
  HomologicalComplex.Hom.isoOfComponents (factorTerm f r) (by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = 1 := hij.symm
      subst j
      simp only [factorTerm, ↓reduceDIte]
      change (Functor.OplaxMonoidal.η (extension f)) ≫
          ModuleCat.ofHom (Algebra.linearMap B (Localization.Away (f r))) =
        (extension f).map (ModuleCat.ofHom (Algebra.linearMap R (Localization.Away r))) ≫
          (extendLocalization f r).hom
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change R at x
      let := f.toAlgebra
      change algebraMap B (Localization.Away (f r)) (f x * 1) =
        IsLocalization.Away.tensorEquiv B (r := r) (A := Localization.Away r)
          ((1 : B) ⊗ₜ[R] algebraMap R (Localization.Away r) x)
      rw [mul_one, Algebra.algebraMap_eq_smul_one (A := Localization.Away r) x,
        ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      exact ((IsLocalization.Away.tensorEquiv B (r := r)
        (A := Localization.Away r)).commutes (f x)).symm
    · have hR : (Cech.factor r).d i j = 0 := by
        simp [Cech.factor, Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor, hi]
      have hB : (Cech.factor (f r)).d i j = 0 := by
        simp [Cech.factor, Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor, hi]
      change (factorTerm f r i).hom ≫ _ = (extension f).map ((Cech.factor r).d i j) ≫ _
      rw [hR, hB, Functor.map_zero, zero_comp, comp_zero])

/-- Base change of the ordered tensor product of the two-term localization complexes. -/
private def extendCech (f : R →+* B) :
    (rs : List R) → (extendComplex f).obj (CechComplex rs) ≅ CechComplex (rs.map f)
  | [] => extendUnit f
  | r :: rs => extendTensor f _ _ ≪≫ tensorIso (extendFactor f r) (extendCech f rs)

private def mapHomology {A D : Type u} [CommRing A] [CommRing D]
    (F : Mod A ⥤ Mod D) [F.PreservesZeroMorphisms] [F.PreservesHomology] (q : ℤ) :
    F.mapHomologicalComplex upZ ⋙ homologyFunctor (Mod D) upZ q ≅
      homologyFunctor (Mod A) upZ q ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc q).mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor (Mod A) upZ q).map f) F)

private lemma span_map_list (f : R →+* B) (rs : List R) :
    Ideal.span {b | b ∈ rs.map f} = (Ideal.span {a | a ∈ rs}).map f := by
  rw [Ideal.map_span]
  congr 1
  ext
  simp

private lemma exists_generating_list [IsNoetherianRing R] (I : Ideal R) :
    ∃ rs : List R, Ideal.span {r | r ∈ rs} = I := by
  classical
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).mp ‹_› I
  exact ⟨s.toList, by simpa using hs⟩

private lemma ι_tensorLeft_map {A : Type u} [CommRing A] (K : Cpx A)
    {L L' : Cpx A} (g : L ⟶ L') (i j k : ℤ) (h : i + j = k) :
    ιTensorObj K L i j k h ≫ ((tensorLeft K).map g).f k =
      (K.X i ◁ g.f j) ≫ ιTensorObj K L' i j k h := by
  change ιMapBifunctor .. ≫ (mapBifunctorMap (𝟙 K) g (curriedTensor (Mod A)) upZ).f k = _
  rw [ι_mapBifunctorMap, id_f, (curriedTensor (Mod A)).map_id, NatTrans.id_app, Category.id_comp]
  rfl

private def extendTensorLeft (f : R →+* B) (K : Cpx R) :
    tensorLeft K ⋙ extendComplex f ≅ extendComplex f ⋙ tensorLeft ((extendComplex f).obj K) :=
  NatIso.ofComponents (extendTensor f K) (by
    intro L L' g
    apply HomologicalComplex.hom_ext
    intro k
    apply (mappedTensorCofanIsColimit f K L k).hom_ext
    rintro ⟨⟨⟨i, j⟩, h⟩⟩
    change (extension f).map (ιTensorObj K L i j k h) ≫
      (extension f).map (((tensorLeft K).map g).f k) ≫ (tensorTerm f K L' k).hom =
        (extension f).map (ιTensorObj K L i j k h) ≫ (tensorTerm f K L k).hom ≫
          ((tensorLeft ((extendComplex f).obj K)).map ((extendComplex f).map g)).f k
    rw [← Functor.map_comp_assoc, ι_tensorLeft_map, Functor.map_comp, Category.assoc,
      tensorTerm_hom_ι, tensorTerm_hom_ι_assoc, ι_tensorLeft_map]
    simp only [Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_map_f,
      Functor.OplaxMonoidal.δ_natural_right_assoc])

private abbrev coefficientsFunctor {A : Type u} [CommRing A] (rs : List A) :=
  single (Mod A) upZ 0 ⋙ cechTensorFunctor rs

private def extendCoefficients (f : R →+* B) (rs : List R) :
    coefficientsFunctor rs ⋙ extendComplex f ≅ extension f ⋙ coefficientsFunctor (rs.map f) := by
  let S := single (Mod R) upZ 0
  let T := tensorLeft ((extendComplex f).obj (CechComplex rs))
  exact (Functor.associator S (tensorLeft (CechComplex rs)) (extendComplex f)) ≪≫
    Functor.isoWhiskerLeft S (extendTensorLeft f (CechComplex rs)) ≪≫
    (Functor.associator S (extendComplex f) T).symm ≪≫
    Functor.isoWhiskerRight (extendStalk f) T ≪≫
    Functor.associator (extension f) (single (Mod B) upZ 0) T ≪≫
    Functor.isoWhiskerLeft (extension f)
      (Functor.isoWhiskerLeft (single (Mod B) upZ 0)
        ((curriedTensor (Cpx B)).mapIso (extendCech f rs)))

/-- Flat extension of scalars commutes naturally with local cohomology. -/
theorem localCohomologyFlatBaseChange :
    Specs.CommutativeAlgebraNotes.LocalCohomologyBaseChange.FlatBaseChange.{u} := by
  intro R B _ _ _ _ f hf I q
  obtain ⟨rs, hrs⟩ := exists_generating_list I
  have hmap : Ideal.span {b | b ∈ rs.map f} = I.map f :=
    (span_map_list f rs).trans (congrArg (Ideal.map f) hrs)
  obtain ⟨er⟩ := localCohomologyCechComparison I rs hrs q
  obtain ⟨eb⟩ := localCohomologyCechComparison (I.map f) (rs.map f) hmap q
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let H := homologyFunctor (Mod B) upZ q
  refine ⟨?_⟩
  calc
    _ ≅ (coefficientsFunctor rs ⋙ homologyFunctor (Mod R) upZ q) ⋙ extension f :=
      Functor.isoWhiskerRight er _
    _ ≅ coefficientsFunctor rs ⋙ homologyFunctor (Mod R) upZ q ⋙ extension f :=
      Functor.associator _ _ _
    _ ≅ coefficientsFunctor rs ⋙ extendComplex f ⋙ H :=
      Functor.isoWhiskerLeft _ (mapHomology (extension f) q).symm
    _ ≅ (coefficientsFunctor rs ⋙ extendComplex f) ⋙ H :=
      (Functor.associator _ _ _).symm
    _ ≅ (extension f ⋙ coefficientsFunctor (rs.map f)) ⋙ H :=
      Functor.isoWhiskerRight (extendCoefficients f rs) H
    _ ≅ extension f ⋙ coefficientsFunctor (rs.map f) ⋙ H :=
      Functor.associator _ _ _
    _ ≅ _ := Functor.isoWhiskerLeft _ eb.symm

open private rowFunctor rowIso from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison

/-- The tensor comparison for a coefficient module already defined over the target ring. -/
private def projectionIso (f : R →+* B) (X : Mod R) (N : Mod B) :
    X ⊗ (restriction f).obj N ≅ (restriction f).obj ((extension f).obj X ⊗ N) := by
  letI : Algebra R B := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N X).symm
  let s := TensorProduct.comm B N ((extension f).obj X)
  let a : ↥(X ⊗ (restriction f).obj N) ≃+ ↥((restriction f).obj ((extension f).obj X ⊗ N)) :=
    (TensorProduct.comm R X N).toAddEquiv.trans (e.toAddEquiv.trans s.toAddEquiv)
  let e' : ↥(X ⊗ (restriction f).obj N) ≃ₗ[R]
      ↥((restriction f).obj ((extension f).obj X ⊗ N)) := { a with map_smul' := ?_ }
  · exact e'.toModuleIso
  intro r z
  change a (r • z) = r • a z
  induction z using TensorProduct.inductionOn with
  | tmul x n =>
      rw [TensorProduct.smul_tmul']
      change ((1 : B) ⊗ₜ[R] (r • x)) ⊗ₜ[B] n =
        f r • (((1 : B) ⊗ₜ[R] x) ⊗ₜ[B] n)
      rw [← TensorProduct.smul_tmul r (1 : B) x, TensorProduct.smul_tmul' (f r)]
      rfl
  | add x y hx hy => simp [smul_add, hx, hy]

private lemma projectionIso_naturality_left (f : R →+* B) {X Y : Mod R} (g : X ⟶ Y) (N : Mod B) :
    (g ▷ (restriction f).obj N) ≫ (projectionIso f Y N).hom =
      (projectionIso f X N).hom ≫ (restriction f).map ((extension f).map g ▷ N) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intros
  rfl

private lemma projectionIso_naturality_right (f : R →+* B) (X : Mod R) {N P : Mod B} (g : N ⟶ P) :
    (X ◁ (restriction f).map g) ≫ (projectionIso f X P).hom =
      (projectionIso f X N).hom ≫ (restriction f).map ((extension f).obj X ◁ g) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intros
  rfl

private def restrictRow (f : R →+* B) (K : Cpx R) :
    restriction f ⋙ rowFunctor K ≅ rowFunctor ((extendComplex f).obj K) ⋙ restrictComplex f :=
  NatIso.ofComponents
    (fun N => HomologicalComplex.Hom.isoOfComponents (fun i => projectionIso f (K.X i) N)
      (fun i j _ => (projectionIso_naturality_left f (K.d i j) N).symm))
    (fun g => HomologicalComplex.hom_ext _ _ fun i => projectionIso_naturality_right f (K.X i) g)

private def restrictCoefficients (f : R →+* B) (rs : List R) :
    restriction f ⋙ coefficientsFunctor rs ≅ coefficientsFunctor (rs.map f) ⋙ restrictComplex f := by
  let K := CechComplex rs
  let L := (extendComplex f).obj K
  let S := single (Mod B) upZ 0
  exact Functor.isoWhiskerLeft (restriction f) (rowIso K).symm ≪≫
    restrictRow f K ≪≫
    Functor.isoWhiskerRight
      (rowIso L ≪≫ Functor.isoWhiskerLeft S ((curriedTensor (Cpx B)).mapIso (extendCech f rs))) _

/-- The change-of-rings isomorphism commutes with B-scalar endomorphisms
by naturality in the B-module. -/
theorem localCohomologyChangeOfRings :
    Specs.CommutativeAlgebraNotes.LocalCohomologyBaseChange.ChangeOfRings.{u} := by
  intro R B _ _ _ _ f I q
  obtain ⟨rs, hrs⟩ := exists_generating_list I
  have hmap : Ideal.span {b | b ∈ rs.map f} = I.map f :=
    (span_map_list f rs).trans (congrArg (Ideal.map f) hrs)
  obtain ⟨er⟩ := localCohomologyCechComparison I rs hrs q
  obtain ⟨eb⟩ := localCohomologyCechComparison (I.map f) (rs.map f) hmap q
  let H := homologyFunctor (Mod R) upZ q
  refine ⟨?_⟩
  calc
    _ ≅ restriction f ⋙ coefficientsFunctor rs ⋙ H := Functor.isoWhiskerLeft _ er
    _ ≅ (restriction f ⋙ coefficientsFunctor rs) ⋙ H := (Functor.associator _ _ _).symm
    _ ≅ (coefficientsFunctor (rs.map f) ⋙ restrictComplex f) ⋙ H :=
      Functor.isoWhiskerRight (restrictCoefficients f rs) H
    _ ≅ coefficientsFunctor (rs.map f) ⋙ restrictComplex f ⋙ H := Functor.associator _ _ _
    _ ≅ coefficientsFunctor (rs.map f) ⋙ homologyFunctor (Mod B) upZ q ⋙ restriction f :=
      Functor.isoWhiskerLeft _ (mapHomology (restriction f) q)
    _ ≅ (coefficientsFunctor (rs.map f) ⋙ homologyFunctor (Mod B) upZ q) ⋙ restriction f :=
      (Functor.associator _ _ _).symm
    _ ≅ _ := Functor.isoWhiskerRight eb.symm _

private lemma localizationExtensionSubsingleton (S : Submonoid R) (M : Mod R) :
    Subsingleton ((extension (algebraMap R (Localization S))).obj M) ↔
      Subsingleton (LocalizedModule S M) := by
  let m : Module R (Localization S) := Module.compHom _ (algebraMap R (Localization S))
  have hm : m = (OreLocalization.instModuleOfIsScalarTower : Module R (Localization S)) := by
    apply Module.ext'
    intro r x
    change (algebraMap R (Localization S)) r * x = _
    exact (Algebra.smul_def r x).symm
  change Subsingleton (@TensorProduct R _ (Localization S) M _ _ m _) ↔ _
  rw [hm]
  let e := LocalizedModule.equivTensorProduct S M
  exact ⟨fun h => by let := h; exact e.injective.subsingleton,
    fun h => by let := h; exact e.symm.injective.subsingleton⟩

private lemma localCohomology_obj_isZero [IsNoetherianRing R] (I : Ideal R) (q : ℤ)
    {M : Mod R} (hM : IsZero M) : IsZero ((localCohomology I q).obj M) := by
  obtain ⟨rs, hrs⟩ := exists_generating_list I
  obtain ⟨e⟩ := localCohomologyCechComparison I rs hrs q
  have hz : IsZero ((rowFunctor (CechComplex rs)).obj M) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.hom_ext
    intro i
    exact ((tensorLeft ((CechComplex rs).X i)).map_isZero hM).eq_of_src _ _
  exact ((homologyFunctor (Mod R) upZ q).map_isZero
    (hz.of_iso ((rowIso (CechComplex rs)).app M).symm)).of_iso (e.app M)

/-- The support of local cohomology lies in the closed locus of the ideal
and in the support of the coefficient module. -/
theorem localCohomologySupportSubset :
    Specs.CommutativeAlgebraNotes.LocalCohomologyBaseChange.SupportInclusion.{u} := by
  intro R _ _ I q M p hp
  let S := p.asIdeal.primeCompl
  let f := algebraMap R (Localization S)
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)
  obtain ⟨e⟩ := localCohomologyFlatBaseChange f hf I q
  have hnonzero : ¬ IsZero ((extension f).obj ((localCohomology I q).obj M)) := by
    intro h
    exact (Module.notMem_support_iff.mpr
      ((localizationExtensionSubsingleton S _).mp (ModuleCat.subsingleton_of_isZero h))) hp
  constructor
  · change (I : Set R) ⊆ p.asIdeal
    have hn : I.map f ≠ ⊤ := by
      intro h
      apply hnonzero
      have hz : IsZero (localCohomology (I.map f) q) :=
        h.symm ▸ localCohomologyTopIsZero (R := Localization S) q
      exact ((Functor.isZero_iff _).mp hz _) |>.of_iso (e.app M)
    have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint S (Localization S) I).mp hn
    intro r hr
    by_contra hnr
    exact Set.disjoint_left.mp hd hnr hr
  · by_contra hm
    have hz : IsZero ((extension f).obj M) :=
      ModuleCat.isZero_iff_subsingleton.mpr
        ((localizationExtensionSubsingleton S M).mpr (Module.notMem_support_iff.mp hm))
    exact hnonzero ((localCohomology_obj_isZero (I.map f) q hz).of_iso (e.app M))

end

end CommutativeAlgebraNotes
