import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitLocality
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.LinearAlgebra.Dimension.Constructions
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe u

namespace RepTheorySurvey.Geometric.ConvolutionUnitLocality

open Analytic LocalSheaf ConvolutionUnitLocalitySpecs

open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

/-- The derived constant-coefficient unit in a single degree. -/
abbrev derivedConstantUnit : Expected.DerivedConstantUnitType.{u} :=
  @ConvolutionUnitLocalitySpecs.derivedConstantUnit.{u}

private abbrev sheafUnit {Y X : TopCat.{u}} (m : Y ⟶ X)
    (a : (inverseImage m).obj (rational X) ≅ rational Y) :
    rational X ⟶ (directImage m).obj (rational Y) :=
  (inverseDirectAdjunction m).unit.app (rational X) ≫ (directImage m).map a.hom

private abbrev singleMap {Y X : TopCat.{u}} (m : Y ⟶ X) (n : ℤ)
    (a : (inverseImage m).obj (rational X) ≅ rational Y) :
    coefficientComplex X n ⟶ (directImage m).mapCochainComplexPlus.obj (coefficientComplex Y n) :=
  ObjectProperty.homMk ((CochainComplex.singleFunctor (Sheaves X) n).map (sheafUnit m a) ≫
    ((HomologicalComplex.singleMapHomologicalComplex (directImage m) (.up ℤ) n).app
      (rational Y)).inv)

/-- Compare the derived value on a complex with the direct image of an injective resolution. -/
private def resolutionIso {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (R : C ⥤ D) [R.Additive] {K : CochainComplex.Plus C}
    {I : CochainComplex.Plus (InjectiveObject C)} (f : K ⟶ injectiveComplex I)
    (hf : CochainComplex.Plus.quasiIso C f) :
    R.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.Q.obj (R.mapCochainComplexPlus.obj (injectiveComplex I)) := by
  haveI := Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) f hf
  exact R.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map f)) ≪≫
    (asIso (R.rightDerivedFunctorPlusUnit.app (injectiveComplex I))).symm

private theorem resolutionIso_compat {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (R : C ⥤ D) [R.Additive] {K : CochainComplex.Plus C}
    {I : CochainComplex.Plus (InjectiveObject C)} (f : K ⟶ injectiveComplex I)
    (hf : CochainComplex.Plus.quasiIso C f) :
    R.rightDerivedFunctorPlusUnit.app K ≫ (resolutionIso R f hf).hom =
      DerivedCategory.Plus.Q.map (R.mapCochainComplexPlus.map f) := by
  have h := R.rightDerivedFunctorPlusUnit.naturality f
  change DerivedCategory.Plus.Q.map (R.mapCochainComplexPlus.map f) ≫
    R.rightDerivedFunctorPlusUnit.app (injectiveComplex I) =
    R.rightDerivedFunctorPlusUnit.app K ≫ R.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map f) at h
  simp only [resolutionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, asIso_inv]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem firstDifferentialZero {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] : (K.sc n).f = 0 := by
  change K.d ((ComplexShape.up ℤ).prev n) n = 0
  rw [CochainComplex.prev]
  exact (K.isZero_of_isStrictlyGE n (n - 1)).eq_of_src _ _

private theorem quasiIsoAt_map_firstDegree {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    {K J : CochainComplex C ℤ} (f : K ⟶ J) (n : ℤ)
    [K.IsStrictlyGE n] [J.IsStrictlyGE n] [QuasiIso f] :
    QuasiIsoAt ((R.mapHomologicalComplex (.up ℤ)).map f) n := by
  letI := R.preservesLeftHomology_of_zero_f (K.sc n) (firstDifferentialZero K n)
  letI := R.preservesLeftHomology_of_zero_f (J.sc n) (firstDifferentialZero J n)
  have h : QuasiIsoAt f n := inferInstance
  rw [quasiIsoAt_iff] at h ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology R
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f)

private theorem firstCohomologyDerivedComparison {Y X : TopCat.{u}} (m : Y ⟶ X) (n : ℤ) :
    IsIso ((cohomology X n).map
      ((directImage m).rightDerivedFunctorPlusUnit.app (coefficientComplex Y n)).hom) := by
  let K := coefficientComplex Y n
  let R := directImage m
  let H := cohomology X n
  let Q := DerivedCategory.Plus.Q (C := Sheaves X)
  let ι := DerivedCategory.Plus.ι (C := Sheaves X)
  obtain ⟨I, hI, f, hf⟩ := K.exists_quasiIso_injective n
  letI : QuasiIso f.hom := (CochainComplex.Plus.quasiIso_iff _ f).mp hf
  haveI : (injectiveComplex I).obj.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (InjectiveObject.ι (Sheaves Y)).map_isZero (I.obj.isZero_of_isStrictlyGE n i hi)
  letI : QuasiIsoAt ((R.mapHomologicalComplex (.up ℤ)).map f.hom) n :=
    quasiIsoAt_map_firstDegree R f.hom n
  have h := congrArg (fun k => (ι ⋙ H).map k) (resolutionIso_compat R f hf)
  change H.map (((R.rightDerivedFunctorPlusUnit.app K) ≫ (resolutionIso R f hf).hom).hom) =
    H.map (DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map f.hom)) at h
  haveI : IsIso (H.map (DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map f.hom))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (Sheaves X) n) _).mpr
      ((quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance)
  let b := H.map (ι.map (R.rightDerivedFunctorPlusUnit.app K))
  let e := H.map (ι.map (resolutionIso R f hf).hom)
  haveI : IsIso e := inferInstanceAs (IsIso (H.map (ι.map (resolutionIso R f hf).hom)))
  haveI : IsIso (b ≫ e) := by
    dsimp only [b, e]
    rw [← Functor.map_comp]
    exact h ▸ inferInstance
  exact IsIso.of_isIso_comp_right b e

private def constantStalkIso {X : TopCat.{u}} (x : X) (M : Coeff.{u}) :
    (stalk x).obj (constant X M) ≅ M := by
  let P : X.Presheaf Coeff.{u} := (Functor.const _).obj M
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Coeff.{u} P
  exact (asIso ((TopCat.Presheaf.stalkFunctor Coeff.{u} x).map
    (toSheafify (Opens.grothendieckTopology X) P))).symm ≪≫
    (colimit.isColimit ((Functor.const (OpenNhds x)ᵒᵖ).obj M)).coconePointUniqueUpToIso
      (isColimitConstCocone _ M)

private theorem sheafUnitStalkGerm {Y X : TopCat.{u}} (m : Y ⟶ X)
    (a : (inverseImage m).obj (rational X) ≅ rational Y) (y : Y) :
    (stalk (m y)).map (sheafUnit m a) ≫
        TopCat.Presheaf.stalkPushforward Coeff.{u} m (rational Y).obj y =
      inverseImageStalkMap m (rational X) y ≫ (stalk y).map a.hom := by
  dsimp only [sheafUnit, inverseImageStalkMap]
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact stalkPushforward_naturality m a.hom.hom y

/-- In the first degree, the map on stalks is the ordinary coefficient unit followed
by isomorphisms. A point of the fibre makes the ordinary map injective. -/
theorem stalkUnit : ConvolutionUnitLocalitySpecs.Expected.StalkUnit.{u} := by
  intro Y X m n a x hx htarget
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨eTarget⟩ := htarget
  let x := m y
  let R := directImage m
  let A := rational X
  let B := rational Y
  let T := stalk x
  let H := cohomology X n ⋙ T
  let S := CochainComplex.singleFunctor (Sheaves X) n
  let Q := DerivedCategory.Q (C := Sheaves X)
  let e : (S ⋙ Q) ⋙ H ≅ T :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft S (DerivedCategory.homologyFunctorFactors (Sheaves X) n)) ≪≫
      HomologicalComplex.homologyFunctorSingleIso (Sheaves X) (.up ℤ) n) T ≪≫ T.leftUnitor
  let f := sheafUnit m a
  haveI : Mono (T.map f) := mono_of_mono_fac (sheafUnitStalkGerm m a y)
  haveI : Mono ((e.hom.app A) ≫ T.map f) := inferInstance
  haveI : Mono (H.map (Q.map (S.map f))) := mono_of_mono_fac (e.hom.naturality f)
  let c := ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) n).app B).inv
  let b := (R.rightDerivedFunctorPlusUnit.app (coefficientComplex Y n)).hom
  haveI : IsIso ((cohomology X n).map b) := firstCohomologyDerivedComparison m n
  haveI : IsIso (H.map b) := (stalk x).map_isIso ((cohomology X n).map b)
  let unit := ConvolutionUnitLocalitySpecs.derivedConstantUnit m n a
  haveI : Mono (H.map unit) := by
    change Mono (H.map (Q.map (S.map f ≫ c) ≫ b))
    rw [Q.map_comp, H.map_comp, H.map_comp]
    infer_instance
  let M := ModuleCat.of ℚ (ULift.{u} ℚ)
  haveI : Simple M := simple_of_finrank_eq_one (k := ℚ)
    ((finrank_ulift ..).trans (Module.finrank_self ℚ))
  haveI : Simple (H.obj ((derivedDirectImage m).obj
      (DerivedCategory.Plus.Q.obj (coefficientComplex Y n))).obj) := Simple.of_iso eTarget
  haveI : Simple (H.obj (Q.obj (S.obj A))) :=
    Simple.of_iso (e.app A ≪≫ constantStalkIso x M)
  change IsIso (H.map unit)
  apply isIso_of_mono_of_nonzero
  intro h
  apply CategoryTheory.id_nonzero (H.obj (Q.obj (S.obj A)))
  apply (cancel_mono (H.map unit)).mp
  simp [h]

private def inverseImageStalkNatIso {Y X : TopCat.{u}} (m : Y ⟶ X) (y : Y) :
    stalk (m y) ≅ inverseImage m ⋙ stalk y :=
  NatIso.ofComponents (fun F => inverseImageStalkIso m F y) (by
    intro F G f
    let A := inverseDirectAdjunction m
    let S := stalk (m y)
    change S.map f ≫ (S.map (A.unit.app G) ≫
        TopCat.Presheaf.stalkPushforward Coeff.{u} m ((inverseImage m).obj G).obj y) =
      (S.map (A.unit.app F) ≫
        TopCat.Presheaf.stalkPushforward Coeff.{u} m ((inverseImage m).obj F).obj y) ≫
        (stalk y).map ((inverseImage m).map f)
    have hu : f ≫ A.unit.app G =
        A.unit.app F ≫ (directImage m).map ((inverseImage m).map f) := A.unit.naturality f
    rw [← Category.assoc, ← Functor.map_comp, hu]
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact stalkPushforward_naturality m ((inverseImage m).map f).hom y)

private theorem preimageNeighborhoods_initial {Y X : TopCat.{u}} (m : Y ⟶ X)
    (U : Opens X) (hm : IsHomeomorph (restrictToOpen m U)) (y : Y) (hy : m y ∈ U) :
    (OpenNhds.map m y).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered _ ?_
    (fun {_ V} _ _ => ⟨V, 𝟙 _, Subsingleton.elim _ _⟩)
  intro W
  let V := (Opens.map m).obj U
  let r := restrictToOpen m U
  let A : Set V := Subtype.val ⁻¹' (W.1 : Set Y)
  let B : Set U := r '' A
  let C : Opens X :=
    ⟨Subtype.val '' B, U.isOpenEmbedding.isOpenMap B (hm.isOpenMap A
      (W.1.2.preimage continuous_subtype_val))⟩
  have hC : m y ∈ C := ⟨r ⟨y, hy⟩, ⟨⟨y, hy⟩, W.2, rfl⟩, rfl⟩
  refine ⟨⟨C, hC⟩, ⟨homOfLE ?_⟩⟩
  change (Opens.map m).obj C ≤ W.1
  intro z hz
  change m z ∈ C at hz
  obtain ⟨p, ⟨w, hw, rfl⟩, hp⟩ := hz
  have hzU : m z ∈ U := hp ▸ (r w).2
  have eq : r w = r ⟨z, hzU⟩ := Subtype.ext hp
  have eq' : w = ⟨z, hzU⟩ := hm.bijective.1 eq
  have heq : w.val = z := congrArg Subtype.val eq'
  change z ∈ (W.1 : Set Y)
  rw [← heq]
  exact hw

private def directImageStalkOnOpenIso {Y X : TopCat.{u}} (m : Y ⟶ X)
    (U : Opens X) (hm : IsHomeomorph (restrictToOpen m U)) (y : Y) (hy : m y ∈ U) :
    directImage m ⋙ stalk (m y) ≅ stalk y := by
  haveI := preimageNeighborhoods_initial m U hm y hy
  let τ : directImage m ⋙ stalk (m y) ⟶ stalk y :=
    { app := fun F => TopCat.Presheaf.stalkPushforward Coeff.{u} m F.obj y
      naturality := fun {_ _} f => stalkPushforward_naturality m f.hom y }
  haveI (F : Sheaves Y) : IsIso (τ.app F) := by
    change IsIso (TopCat.Presheaf.stalkPushforward Coeff.{u} m F.obj y)
    unfold TopCat.Presheaf.stalkPushforward
    infer_instance
  exact NatIso.ofComponents (fun F => asIso (τ.app F)) (fun f => τ.naturality f)

private theorem quasiIso_map_natIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) {K J : CochainComplex C ℤ} (f : K ⟶ J) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) ↔
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f) := by
  let E := NatIso.mapHomologicalComplex e (.up ℤ)
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (E.app K) (E.app J) (E.hom.naturality f).symm)

/-- An exact restriction of a complex map is a quasi-isomorphism if it is so
on all stalks in that open. -/
private theorem quasiIso_restrict_of_stalks {X : TopCat.{u}} (U : Opens X)
    {K J : CochainComplex (Sheaves X) ℤ} (f : K ⟶ J)
    (h : ∀ x ∈ U, QuasiIso (((stalk x).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso (((inverseImage (openInclusion U)).mapHomologicalComplex (.up ℤ)).map f) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro z
  let S := inverseImage (openInclusion U)
  let T := stalk z
  let g := (S.mapHomologicalComplex (.up ℤ)).map f
  haveI : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map g) :=
    (quasiIso_map_natIso (inverseImageStalkNatIso (openInclusion U) z).symm f).mpr
      (h z.val z.property)
  let gq := (HomologicalComplex.shortComplexFunctor (Sheaves (TopCat.of U)) (.up ℤ) q).map g
  have hq : ShortComplex.QuasiIso (T.mapShortComplex.map gq) := by
    have hh : QuasiIsoAt ((T.mapHomologicalComplex (.up ℤ)).map g) q := inferInstance
    rw [quasiIsoAt_iff] at hh
    exact hh
  change IsIso ((ShortComplex.homologyFunctor _ ⋙ T).map gq)
  exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso T) gq).mp
    ((ShortComplex.quasiIso_iff _).mp hq)

/-- On an open over which the map is a homeomorphism, inverse images of
neighborhoods compute the same stalks on the source. -/
theorem openUnit : ConvolutionUnitLocalitySpecs.Expected.OpenUnit.{u} := by
  intro Y X m n a U hm
  let K := coefficientComplex Y n
  let R := directImage m
  let S := inverseImage (openInclusion U)
  let Q := DerivedCategory.Q (C := Sheaves X)
  obtain ⟨I, _, f, hf⟩ := K.exists_quasiIso_injective n
  haveI : QuasiIso f.hom := (CochainComplex.Plus.quasiIso_iff _ f).mp hf
  let g := singleMap m n a ≫ R.mapCochainComplexPlus.map f
  let e := (DerivedCategory.Plus.ι (C := Sheaves X)).mapIso (resolutionIso R f hf)
  let unit := ConvolutionUnitLocalitySpecs.derivedConstantUnit m n a
  have h : unit ≫ e.hom = Q.map g.hom := by
    change ((DerivedCategory.Plus.Q.map (singleMap m n a) ≫
      R.rightDerivedFunctorPlusUnit.app K) ≫ (resolutionIso R f hf).hom).hom = _
    rw [Category.assoc, resolutionIso_compat, ← Functor.map_comp]
    rfl
  haveI : QuasiIso ((S.mapHomologicalComplex (.up ℤ)).map g.hom) := by
    apply quasiIso_restrict_of_stalks
    intro x hx
    obtain ⟨z, hz⟩ := hm.bijective.2 ⟨x, hx⟩
    let y : Y := z.val
    have hxy : m y = x := congrArg Subtype.val hz
    subst x
    let T := stalk (m y)
    let E := directImageStalkOnOpenIso m U hm y hx
    haveI : IsIso (T.map (sheafUnit m a) ≫ E.hom.app (rational Y)) := by
      change IsIso (T.map (sheafUnit m a) ≫
        TopCat.Presheaf.stalkPushforward Coeff.{u} m (rational Y).obj y)
      rw [sheafUnitStalkGerm]
      infer_instance
    haveI : IsIso (T.map (sheafUnit m a)) :=
      IsIso.of_isIso_comp_right _ (E.hom.app (rational Y))
    haveI : IsIso ((T.mapHomologicalComplex (.up ℤ)).map
        ((CochainComplex.singleFunctor (Sheaves X) n).map (sheafUnit m a))) :=
      (NatIso.isIso_map_iff (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) n)
        (sheafUnit m a)).mpr
        ((CochainComplex.singleFunctor Coeff.{u} n).map_isIso (T.map (sheafUnit m a)))
    haveI : IsIso ((T.mapHomologicalComplex (.up ℤ)).map (singleMap m n a).hom) := by
      change IsIso ((T.mapHomologicalComplex (.up ℤ)).map
        ((CochainComplex.singleFunctor (Sheaves X) n).map (sheafUnit m a) ≫
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) n).app (rational Y)).inv))
      rw [Functor.map_comp]
      infer_instance
    haveI : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map (R.mapCochainComplexPlus.map f).hom) :=
      (quasiIso_map_natIso E f.hom).mpr inferInstance
    change QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map
      ((singleMap m n a).hom ≫ (R.mapCochainComplexPlus.map f).hom))
    rw [Functor.map_comp]
    infer_instance
  haveI : IsIso ((S.mapDerivedCategory).map (Q.map g.hom)) := by
    apply (NatIso.isIso_map_iff S.mapDerivedCategoryFactors g.hom).mpr
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (Sheaves (TopCat.of U))
      ((S.mapHomologicalComplex (.up ℤ)).map g.hom)).mpr inferInstance
  haveI : IsIso ((S.mapDerivedCategory).map unit ≫ (S.mapDerivedCategory).map e.hom) := by
    rw [← Functor.map_comp, h]
    infer_instance
  exact IsIso.of_isIso_comp_right ((S.mapDerivedCategory).map unit)
    ((S.mapDerivedCategory).map e.hom)

end RepTheorySurvey.Geometric.ConvolutionUnitLocality
