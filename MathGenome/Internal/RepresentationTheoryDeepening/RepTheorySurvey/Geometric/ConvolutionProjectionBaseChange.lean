import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionProjectionBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConstantSheafComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionAnalyticCharts
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitLocality
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Filtered.Final
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Opposite TopologicalSpace Topology
open P202Specs.CohomologyPairs

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace RepTheorySurvey.Geometric.ConvolutionProjectionBaseChange

open Analytic LocalSheaf
open Analytic.IntersectionComplex (adjointSquareMap)
open Analytic.SingularCochains
open ConvolutionUnitConeSpecs (singularCohomology)

abbrev productProjection := ConvolutionProjectionBaseChangeSpecs.productProjection
abbrev productMap := @ConvolutionProjectionBaseChangeSpecs.productMap

private theorem mate_isIso_of_adjunctions {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B} (α : E ⋙ J ≅ K ⋙ V)
    (a a' : J ⊣ S) (b b' : K ⊣ R) (F : D)
    (h : IsIso (adjointSquareMap α a b F)) :
    IsIso (adjointSquareMap α a' b' F) := by
  haveI := h
  let r := b'.rightAdjointUniq b
  let s := a.rightAdjointUniq a'
  let f := adjointSquareMap α a b F
  have eq : adjointSquareMap α a' b' F = E.map (r.hom.app F) ≫ f ≫ s.hom.app (V.obj F) := by
    apply (a'.homEquiv _ _).symm.injective
    simp only [adjointSquareMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc]
    rw [Adjunction.rightAdjointUniq_hom_app_counit]
    rw [← Adjunction.homEquiv_counit]
    simp only [f, adjointSquareMap, Equiv.symm_apply_apply]
    rw [← Functor.comp_map E J, α.hom.naturality_assoc, Functor.comp_map K V,
      ← V.map_comp, Adjunction.rightAdjointUniq_hom_app_counit]
  rw [eq]
  infer_instance

private def productOpen {T X : TopCat.{0}} (D : Opens T) (U : Opens X) :
    Opens (TopCat.of (T × X)) :=
  ⟨(D : Set T) ×ˢ (U : Set X), D.isOpen.prod U.isOpen⟩

private theorem productOpen_le {T X : TopCat.{0}} {D E : Opens T} {U V : Opens X}
    (hd : D ≤ E) (hu : U ≤ V) : productOpen D U ≤ productOpen E V :=
  Set.prod_mono hd hu

private theorem productOpen_refines {T X : TopCat.{0}} (t : T) (x : X)
    (hT : HasContractibleOpenBasis T)
    (W : Opens (TopCat.of (T × X))) (hw : (t, x) ∈ W) :
    ∃ (D : Opens T) (U : Opens X), t ∈ D ∧ x ∈ U ∧
      ContractibleSpace D ∧ productOpen D U ≤ W := by
  obtain ⟨d, u, hdo, htd, huo, hxu, hle⟩ :=
    mem_nhds_prod_iff'.mp (W.isOpen.mem_nhds hw)
  obtain ⟨D, ht, hD, hc⟩ := hT t ⟨d, hdo⟩ htd
  exact ⟨D, ⟨u, huo⟩, ht, hxu, hc, (Set.prod_mono hD Set.Subset.rfl).trans hle⟩

private def productOpenHomeomorph {T X : TopCat.{0}} (D : Opens T) (U : Opens X) :
    productOpen D U ≃ₜ D × U where
  toFun z := (⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2⟩)
  invFun z := ⟨(z.1.val, z.2.val), z.1.property, z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private theorem singularProjection_isIso (D Y : TopCat.{0}) [ContractibleSpace D] (n : ℤ) :
    IsIso ((singularCohomology n).map (productProjection D Y).op) := by
  obtain ⟨d, ⟨H⟩⟩ := id_nullhomotopic D
  let Z := TopCat.of (D × Y)
  let p := productProjection D Y
  let s : Y ⟶ Z := TopCat.ofHom ⟨fun y => (d, y), continuous_const.prodMk continuous_id⟩
  have hs : s ≫ p = 𝟙 Y := TopCat.ext fun _ => rfl
  have hp : TopCat.Homotopy (𝟙 Z) (p ≫ s) := by
    let P : C(unitInterval × Z, D) :=
      ⟨fun a => H (a.1, a.2.1), H.continuous.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))⟩
    refine ⟨⟨fun a => (P a, a.2.2), P.continuous.prodMk (continuous_snd.comp continuous_snd)⟩,
      fun z => ?_, fun z => ?_⟩
    · exact Prod.ext (H.map_zero_left z.1) rfl
    · exact Prod.ext (H.map_one_left z.1) rfl
  let F := singularCohomology n
  have h₁ : F.map p.op ≫ F.map s.op = 𝟙 _ := by
    rw [← F.map_comp, ← op_comp, hs, op_id, F.map_id]
  have h₂ : F.map s.op ≫ F.map p.op = 𝟙 _ := by
    rw [← F.map_comp, ← op_comp,
      ← (P202.CohomologyPairs.homotopy_invariant ℚ Values.{0}).1 hp n, op_id, F.map_id]
  exact ⟨⟨F.map s.op, h₁, h₂⟩⟩

private abbrev preimageMap := @ConvolutionUnitLocalitySpecs.restrictToOpen.{0}

private abbrev cochainFunctor := ordinaryCochainFunctor ℚ Values.{0}

private instance {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (TopCat.Presheaf.pushforward Coeff.{0} f).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private def presheafCochainPullback {X Y : TopCat.{0}} (f : X ⟶ Y) :
    presheafComplex Y ⟶
      ((TopCat.Presheaf.pushforward Coeff.{0} f).mapHomologicalComplex (.up ℤ)).obj
        (presheafComplex X) where
  f n :=
    { app := fun U => (cochainFunctor.map (preimageMap f U.unop).op).f n
      naturality := by
        intro U V i
        let g := (Opens.toTopCat Y).map i.unop
        let h := (Opens.toTopCat X).map ((Opens.map f).map i.unop)
        have he : h ≫ preimageMap f U.unop = preimageMap f V.unop ≫ g :=
          TopCat.ext (fun _ => rfl)
        change (cochainFunctor.map g.op).f n ≫
            (cochainFunctor.map (preimageMap f V.unop).op).f n =
          (cochainFunctor.map (preimageMap f U.unop).op).f n ≫ (cochainFunctor.map h.op).f n
        rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← cochainFunctor.map_comp,
          ← cochainFunctor.map_comp, ← op_comp, ← op_comp, he] }
  comm' n k _ := by
    apply NatTrans.ext
    funext U
    exact (cochainFunctor.map (preimageMap f U.unop).op).comm n k

private abbrev sheafForgets (X : TopCat.{0}) :=
  (TopCat.Sheaf.forget Coeff.{0} X).mapHomologicalComplex (.up ℤ)

private abbrev imageComplex {X Y : TopCat.{0}} (f : X ⟶ Y) :=
  (directImage f).mapHomologicalComplex (.up ℤ)

private abbrev imagePresheafComplex {X Y : TopCat.{0}} (f : X ⟶ Y) :=
  (TopCat.Presheaf.pushforward Coeff.{0} f).mapHomologicalComplex (.up ℤ)

private def cochainMapToSections {X Y : TopCat.{0}} (f : X ⟶ Y) :
    presheafComplex Y ⟶ (sheafForgets Y).obj ((imageComplex f).obj (sheafComplex X)) :=
  presheafCochainPullback f ≫ (imagePresheafComplex f).map (complexUnit X)

/-- The cochain pullback on the sheafifications is induced by pullback on the
presheaf cochains of opens. -/
private def sheafCochainPullback {X Y : TopCat.{0}} (f : X ⟶ Y) :
    sheafComplex Y ⟶ (imageComplex f).obj (sheafComplex X) where
  f n := ⟨sheafifyLift (Opens.grothendieckTopology Y) ((cochainMapToSections f).f n)
    (((imageComplex f).obj (sheafComplex X)).X n).property⟩
  comm' n k _ := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (Opens.grothendieckTopology Y) _ _
      (((imageComplex f).obj (sheafComplex X)).X k).property
    change unit Y n ≫ _ ≫ _ = unit Y n ≫
      sheafifyMap _ ((presheafComplex Y).d n k) ≫ _
    rw [← Category.assoc, toSheafify_sheafifyLift, ← Category.assoc, ← toSheafify_naturality,
      Category.assoc, toSheafify_sheafifyLift]
    exact (cochainMapToSections f).comm n k

private theorem sheafCochainPullback_unit {X Y : TopCat.{0}} (f : X ⟶ Y) :
    complexUnit Y ≫ (sheafForgets Y).map (sheafCochainPullback f) = cochainMapToSections f := by
  ext n : 1
  exact toSheafify_sheafifyLift _ _ _

private theorem sheafCochainPullback_sections {X Y : TopCat.{0}} (f : X ⟶ Y) (U : Opens Y) :
    sectionMap U ≫ ((sectionsOn U).mapHomologicalComplex (.up ℤ)).map (sheafCochainPullback f) =
      cochainFunctor.map (preimageMap f U).op ≫ sectionMap ((Opens.map f).obj U) := by
  ext n : 1
  exact congrArg (fun (g : presheafComplex Y ⟶ _) => (g.f n).app (op U))
    (sheafCochainPullback_unit f)

open private isIsoDerivedSectionsOfFlasque
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
open private resolutionIso resolutionIso_compat
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitLocality

private theorem quasiIso_of_stalk {X : TopCat.{0}} {K L : CochainComplex (Sheaves X) ℤ}
    (f : K ⟶ L)
    (h : ∀ x : X, QuasiIso (((stalk x).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  let T := stalk x
  let m := (HomologicalComplex.shortComplexFunctor (Sheaves X) (.up ℤ) n).map f
  change IsIso ((ShortComplex.homologyFunctor _ ⋙ T).map m)
  have hq : ShortComplex.QuasiIso (T.mapShortComplex.map m) :=
    (quasiIsoAt_iff _ _).mp ((quasiIso_iff _).mp (h x) n)
  exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso T) m).mp
    ((ShortComplex.quasiIso_iff _).mp hq)

private theorem quasiIso_of_all_sections {X : TopCat.{0}} {K L : CochainComplex (Sheaves X) ℤ}
    (f : K ⟶ L)
    (h : ∀ U : Opens X, QuasiIso (((sectionsOn U).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  haveI : QuasiIso ((sheafForgets X).map f) :=
    (HomologicalComplex.quasiIso_iff_evaluation _).mpr (fun U => h U.unop)
  apply quasiIso_of_stalk
  intro x
  let T := TopCat.Presheaf.stalkFunctor Coeff.{0} x
  haveI : T.PreservesHomology := inferInstance
  exact inferInstanceAs (QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map
    ((sheafForgets X).map f)))

/-- The right-derived unit on a bounded-below complex of flasque sheaves is
invertible. Compare it to an injective replacement on every inverse-image open. -/
private theorem directImageUnit_isIso_of_flasque {X Y : TopCat.{0}} (m : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaves Y)) (hK : ∀ n : ℤ, TopCat.Sheaf.IsFlasque (K.obj.X n)) :
    IsIso ((directImage m).rightDerivedFunctorPlusUnit.app K) := by
  let R := directImage m
  let Q := DerivedCategory.Plus.Q (C := Sheaves X)
  obtain ⟨b, hb⟩ := K.property
  obtain ⟨I, _, f, hf⟩ := K.exists_quasiIso_injective b
  haveI : QuasiIso (R.mapCochainComplexPlus.map f).hom := by
    apply quasiIso_of_all_sections
    intro U
    let S := sectionsOn ((Opens.map m).obj U)
    have hS : IsIso (S.rightDerivedFunctorPlusUnit.app K) :=
      isIsoDerivedSectionsOfFlasque _ K hK
    haveI : IsIso (DerivedCategory.Plus.Q.map (S.mapCochainComplexPlus.map f)) := by
      rw [← resolutionIso_compat S f hf]
      infer_instance
    let g := S.mapCochainComplexPlus.map f
    let e := DerivedCategory.Plus.QCompιIso Coeff.{0}
    have hQ : IsIso ((DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι).map g) := by
      exact DerivedCategory.Plus.ι.map_isIso (DerivedCategory.Plus.Q.map g)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ g.hom).mp
      ((NatIso.isIso_map_iff e g).mp hQ)
  haveI : IsIso (Q.map (R.mapCochainComplexPlus.map f)) :=
    Localization.inverts Q (CochainComplex.Plus.quasiIso _) _
      ((CochainComplex.Plus.quasiIso_iff _ _).mpr inferInstance)
  haveI : IsIso (R.rightDerivedFunctorPlusUnit.app K ≫ (resolutionIso R f hf).hom) := by
    rw [resolutionIso_compat]
    infer_instance
  exact IsIso.of_isIso_comp_right (R.rightDerivedFunctorPlusUnit.app K) (resolutionIso R f hf).hom

private abbrev ContractibleNhds {T : TopCat.{0}} (t : T) :=
  { D : OpenNhds t // ContractibleSpace D.val }

private theorem contractibleNhds_codirected {T : TopCat.{0}} (t : T)
    (hT : HasContractibleOpenBasis T) : IsCodirectedOrder (ContractibleNhds t) := by
  constructor
  intro D E
  obtain ⟨V, ht, hV, hc⟩ := hT t (D.val.val ⊓ E.val.val)
    ⟨D.val.property, E.val.property⟩
  exact ⟨⟨⟨V, ht⟩, hc⟩, hV.trans inf_le_left, hV.trans inf_le_right⟩

private structure ProductNhds {T X : TopCat.{0}} (t : T) (x : X) where
  left : ContractibleNhds t
  right : OpenNhds x

private instance {T X : TopCat.{0}} (t : T) (x : X) : Preorder (ProductNhds t x) :=
  Preorder.lift (fun i => (i.left, i.right))

private def productNhds {T X : TopCat.{0}} (t : T) (x : X) :
    ProductNhds t x → OpenNhds (X := TopCat.of (T × X)) (t, x) :=
  fun i => ⟨productOpen i.left.val.val i.right.val, i.left.val.property, i.right.property⟩

private theorem productNhds_monotone {T X : TopCat.{0}} (t : T) (x : X) :
    Monotone (productNhds t x) :=
  fun _ _ h => productOpen_le h.1 h.2

private abbrev rightImage (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X) :=
  (imageComplex (productMap T m)).obj (sheafComplex (TopCat.of (T × Y)))

private def projectionCochainMap (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X) :
    (imageComplex m).obj (sheafComplex Y) ⟶ (imageComplex (productProjection T X)).obj
      (rightImage T m) :=
  (imageComplex m).map (sheafCochainPullback (productProjection T Y))

private abbrev productOpenInProjection {T X : TopCat.{0}} (D : Opens T) (U : Opens X) :
    productOpen D U ⟶ (Opens.map (productProjection T X)).obj U :=
  homOfLE (fun _ h => h.2)

private def productOpenProjection {T X : TopCat.{0}} (D : Opens T) (U : Opens X) :
    TopCat.of (productOpen D U) ⟶ TopCat.of U :=
  (TopCat.isoOfHomeo (productOpenHomeomorph D U)).hom ≫ productProjection (TopCat.of D) (TopCat.of U)

private theorem projectionSections_quasiIso (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (D : Opens T) (U : Opens X) (hD : ContractibleSpace D)
    (hY : ∀ V : Opens Y, QuasiIso (sectionMap V))
    (hTY : ∀ W : Opens (TopCat.of (T × Y)), QuasiIso (sectionMap W)) :
    QuasiIso (((sectionsOn U).mapHomologicalComplex (.up ℤ)).map (projectionCochainMap T m) ≫
      (openSectionComplexes (rightImage T m)).map (productOpenInProjection D U).op) := by
  let V := (Opens.map m).obj U
  let q := productProjection T Y
  let j := productMap T m
  let W := (Opens.map j).obj (productOpen D U)
  let i : W ⟶ (Opens.map q).obj V := homOfLE (fun _ h => h.2)
  let k := (Opens.toTopCat (TopCat.of (T × Y))).map i
  let γ := productOpenProjection D V
  let s := ((sectionsOn V).mapHomologicalComplex (.up ℤ)).map (sheafCochainPullback q) ≫
    Analytic.SmallCochains.sectionsRestriction i
  have hs : sectionMap V ≫ s = cochainFunctor.map γ.op ≫ sectionMap W := by
    change sectionMap V ≫
        ((sectionsOn V).mapHomologicalComplex (.up ℤ)).map (sheafCochainPullback q) ≫
        Analytic.SmallCochains.sectionsRestriction i = _
    rw [← Category.assoc, sheafCochainPullback_sections, Category.assoc]
    change cochainFunctor.map (preimageMap q V).op ≫
      (sectionMap ((Opens.map q).obj V) ≫ Analytic.SmallCochains.sectionsRestriction i) = _
    rw [← SmallCochainComparison.sectionMap_naturality i]
    rw [← Category.assoc, ← cochainFunctor.map_comp, ← op_comp]
    congr 2
  letI : ContractibleSpace (TopCat.of D) := hD
  let e : TopCat.of (productOpen D V) ≅ TopCat.of (D × V) :=
    TopCat.isoOfHomeo (productOpenHomeomorph D V)
  haveI : IsIso e.hom.op := inferInstance
  haveI : QuasiIso (cochainFunctor.map γ.op) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso ((singularCohomology n).map γ.op)
    haveI := singularProjection_isIso (TopCat.of D) (TopCat.of V) n
    change IsIso ((singularCohomology n).map (e.hom ≫
      productProjection (TopCat.of D) (TopCat.of V)).op)
    rw [op_comp, Functor.map_comp]
    infer_instance
  haveI := hY V
  haveI := hTY W
  haveI : QuasiIso (sectionMap V ≫ s) := hs.symm ▸ inferInstance
  haveI : QuasiIso s := quasiIso_of_comp_left (sectionMap V) s
  exact inferInstanceAs (QuasiIso s)

open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
open private inverseImageStalkNatIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitLocality

private def stalkPushforwardNatural {X Y : TopCat.{0}} (p : X ⟶ Y) (x : X) :
    TopCat.Presheaf.pushforward Coeff.{0} p ⋙ TopCat.Presheaf.stalkFunctor Coeff.{0} (p x) ⟶
      TopCat.Presheaf.stalkFunctor Coeff.{0} x where
  app B := TopCat.Presheaf.stalkPushforward Coeff.{0} p B x
  naturality _ _ f := stalkPushforward_naturality p f x

private def presheafStalkCochainMap {X Y : TopCat.{0}} (p : X ⟶ Y) (x : X)
    {A : CochainComplex (Y.Presheaf Coeff.{0}) ℤ}
    {B : CochainComplex (X.Presheaf Coeff.{0}) ℤ}
    (u : A ⟶ (imagePresheafComplex p).obj B) :
    ((TopCat.Presheaf.stalkFunctor Coeff.{0} (p x)).mapHomologicalComplex (.up ℤ)).obj A ⟶
      ((TopCat.Presheaf.stalkFunctor Coeff.{0} x).mapHomologicalComplex (.up ℤ)).obj B :=
  ((TopCat.Presheaf.stalkFunctor Coeff.{0} (p x)).mapHomologicalComplex (.up ℤ)).map u ≫
    ((stalkPushforwardNatural p x).mapHomologicalComplex (.up ℤ)).app B

private theorem stalkOfTranspose_quasiIso {X Y : TopCat.{0}} (p : X ⟶ Y) (x : X)
    {A : CochainComplex (Sheaves Y) ℤ} {B : CochainComplex (Sheaves X) ℤ}
    (v : ((inverseImage p).mapHomologicalComplex (.up ℤ)).obj A ⟶ B)
    (u : A ⟶ (imageComplex p).obj B)
    (hu : ∀ i, (inverseDirectAdjunction p).homEquiv _ _ (v.f i) = u.f i)
    (h : QuasiIso (presheafStalkCochainMap p x (A := (sheafForgets Y).obj A)
      (B := (sheafForgets X).obj B) ((sheafForgets Y).map u))) :
    QuasiIso (((stalk x).mapHomologicalComplex (.up ℤ)).map v) := by
  let e := NatIso.mapHomologicalComplex (inverseImageStalkNatIso p x) (.up ℤ)
  have he : e.hom.app A ≫ ((stalk x).mapHomologicalComplex (.up ℤ)).map v =
      presheafStalkCochainMap p x (A := (sheafForgets Y).obj A)
      (B := (sheafForgets X).obj B) ((sheafForgets Y).map u) := by
    ext i : 1
    let a := inverseDirectAdjunction p
    change inverseImageStalkMap p (A.X i) x ≫ (stalk x).map (v.f i) =
      (stalk (p x)).map (u.f i) ≫ TopCat.Presheaf.stalkPushforward Coeff.{0} p (B.X i).obj x
    rw [← hu, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    unfold inverseImageStalkMap
    rw [Category.assoc]
    congr 1
    exact (stalkPushforward_naturality p (v.f i).hom x).symm
  haveI : QuasiIso (e.hom.app A ≫ ((stalk x).mapHomologicalComplex (.up ℤ)).map v) := he ▸ h
  exact quasiIso_of_comp_left (e.hom.app A) _

/-- Compute the map of stalk complexes by taking the filtered colimit of
the section comparisons over pairs of neighborhoods. -/
private theorem stalkProduct_quasiIso {T X : TopCat.{0}} (t : T) (x : X)
    (hT : HasContractibleOpenBasis T)
    (A : CochainComplex (X.Presheaf Coeff.{0}) ℤ)
    (B : CochainComplex ((TopCat.of (T × X)).Presheaf Coeff.{0}) ℤ)
    (u : A ⟶ (imagePresheafComplex (productProjection T X)).obj B)
    (hu : ∀ (D : ContractibleNhds t) (U : OpenNhds x),
      QuasiIso ((((evaluation (Opens X)ᵒᵖ Coeff.{0}).obj (op U.val)).mapHomologicalComplex (.up ℤ)).map u ≫
        B.asFunctor.map (productOpenInProjection D.val.val U.val).op)) :
    QuasiIso (presheafStalkCochainMap (productProjection T X) (t, x) u) := by
  letI := contractibleNhds_codirected t hT
  let I := ProductNhds t x
  letI : IsCodirectedOrder I := by
    constructor
    intro a b
    obtain ⟨d, hda, hdb⟩ := exists_le_le a.left b.left
    exact ⟨⟨d, a.right ⊓ b.right⟩, ⟨hda, inf_le_left⟩, ⟨hdb, inf_le_right⟩⟩
  let hP := productNhds_monotone t x
  let hQ : Monotone (ProductNhds.right : I → OpenNhds x) := fun _ _ h => h.2
  have hP' : hP.functor.Initial := (hP.initial_functor_iff).mpr (fun W => by
    obtain ⟨D, U, ht, hx, hc, h⟩ := productOpen_refines t x hT W.val W.property
    exact ⟨⟨⟨⟨D, ht⟩, hc⟩, ⟨U, hx⟩⟩, h⟩)
  have hQ' : hQ.functor.Initial := (hQ.initial_functor_iff).mpr (fun U => by
    obtain ⟨D, ht, _, hc⟩ := hT t ⊤ trivial
    exact ⟨⟨⟨⟨D, ht⟩, hc⟩, U⟩, le_rfl⟩)
  letI : hP.functor.op.Final := Functor.final_op_of_initial hP.functor
  letI : hQ.functor.op.Final := Functor.final_op_of_initial hQ.functor
  let P := (OpenNhds.inclusion (X := TopCat.of (T × X)) (t, x)).op
  let Q := (OpenNhds.inclusion x).op
  let F := (whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ Coeff.{0}).obj Q
  let G := (whiskeringLeft (OpenNhds (X := TopCat.of (T × X)) (t, x))ᵒᵖ
    (Opens (TopCat.of (T × X)))ᵒᵖ Coeff.{0}).obj P
  let F' := (whiskeringLeft _ _ Coeff.{0}).obj hQ.functor.op
  let G' := (whiskeringLeft _ _ Coeff.{0}).obj hP.functor.op
  let p := productProjection T X
  let l (i : I) := productOpenInProjection i.left.val.val i.right.val
  let η : ((F ⋙ F').mapHomologicalComplex (.up ℤ)).obj A ⟶
      ((G ⋙ G').mapHomologicalComplex (.up ℤ)).obj B :=
    { f := fun n =>
        { app := fun i => (u.f n).app (op i.unop.right.val) ≫ (B.X n).map (l i.unop).op
          naturality := by
            intro i j g
            have hg : j.unop ≤ i.unop := leOfHom g.unop
            let gi : j.unop.right.val ⟶ i.unop.right.val := homOfLE hg.2
            let gj : productOpen j.unop.left.val.val j.unop.right.val ⟶
                productOpen i.unop.left.val.val i.unop.right.val := homOfLE (hP hg)
            change (A.X n).map gi.op ≫ (u.f n).app (op j.unop.right.val) ≫
                (B.X n).map (l j.unop).op =
              ((u.f n).app (op i.unop.right.val) ≫ (B.X n).map (l i.unop).op) ≫ (B.X n).map gj.op
            rw [← Category.assoc, (u.f n).naturality gi.op]
            simp only [Category.assoc]
            congr 1
            change (B.X n).map (((Opens.map p).map gi).op) ≫ (B.X n).map (l j.unop).op = _
            rw [← Functor.map_comp, ← Functor.map_comp]
            congr 1 }
      comm' n m _ := by
        apply NatTrans.ext
        funext i
        change ((u.f n).app (op i.unop.right.val) ≫ (B.X n).map (l i.unop).op) ≫
            (B.d n m).app (op (productOpen i.unop.left.val.val i.unop.right.val)) =
          _ ≫ ((u.f m).app (op i.unop.right.val) ≫ (B.X m).map (l i.unop).op)
        rw [Category.assoc, (B.d n m).naturality (l i.unop).op, ← Category.assoc,
          ← Category.assoc]
        congr 1
        exact congrArg (fun g => g.app (op i.unop.right.val)) (u.comm n m) }
  haveI : QuasiIso η := (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    (fun i => hu i.unop.left i.unop.right)
  let M := colim (J := Iᵒᵖ) (C := Coeff.{0})
  haveI : Nonempty I := by
    obtain ⟨D, hd, _, hc⟩ := hT t ⊤ trivial
    exact ⟨⟨⟨⟨D, hd⟩, hc⟩, ⊤⟩⟩
  haveI : IsFiltered Iᵒᵖ := inferInstance
  haveI : PreservesFiniteLimits M := inferInstance
  haveI : QuasiIso ((M.mapHomologicalComplex (.up ℤ)).map η) := inferInstance
  let eF := NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft F (Functor.Final.colimIso hQ.functor.op)) (.up ℤ)
  let eG := NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft G (Functor.Final.colimIso hP.functor.op)) (.up ℤ)
  have eq : eF.hom.app A ≫ presheafStalkCochainMap p (t, x) u =
      (M.mapHomologicalComplex (.up ℤ)).map η ≫ eG.hom.app B := by
    ext n : 1
    apply colimit.hom_ext
    intro i
    let A' := A.X n
    let B' := B.X n
    let U := i.unop.right.val
    let W := productOpen i.unop.left.val.val U
    change colimit.ι (hQ.functor.op ⋙ Q ⋙ A') i ≫
        (Functor.Final.colimitIso hQ.functor.op (Q ⋙ A')).hom ≫
          (presheafStalkCochainMap p (t, x) u).f n =
      colimit.ι (hQ.functor.op ⋙ Q ⋙ A') i ≫ colim.map (η.f n) ≫
        (Functor.Final.colimitIso hP.functor.op (P ⋙ B')).hom
    rw [Functor.Final.ι_colimitIso_hom_assoc, colimit.ι_map_assoc]
    change A'.germ U x i.unop.right.property ≫
        ((TopCat.Presheaf.stalkFunctor Coeff.{0} x).map (u.f n) ≫
          TopCat.Presheaf.stalkPushforward Coeff.{0} p B' (t, x)) =
      ((u.f n).app (op U) ≫ B'.map (l i.unop).op) ≫
        (colimit.ι (hP.functor.op ⋙ P ⋙ B') i ≫
          (Functor.Final.colimitIso hP.functor.op (P ⋙ B')).hom)
    rw [Functor.Final.ι_colimitIso_hom, TopCat.Presheaf.stalkFunctor_map_germ_assoc]
    have hpush := TopCat.Presheaf.stalkPushforward_germ Coeff.{0}
      p B' U (t, x) i.unop.right.property
    have hres := B'.germ_res (l i.unop) (t, x)
      ⟨i.unop.left.val.property, i.unop.right.property⟩
    change (u.f n).app (op U) ≫ ((TopCat.Presheaf.pushforward Coeff.{0} p).obj B').germ
        U (p (t, x)) i.unop.right.property ≫ _ =
      ((u.f n).app (op U) ≫ B'.map (l i.unop).op) ≫
        B'.germ W (t, x) ⟨i.unop.left.val.property, i.unop.right.property⟩
    simpa only [Category.assoc] using congrArg ((u.f n).app (op U) ≫ ·) (hpush.trans hres.symm)
  haveI : QuasiIso (eF.hom.app A ≫ presheafStalkCochainMap p (t, x) u) :=
    eq.symm ▸ inferInstance
  exact quasiIso_of_comp_left (eF.hom.app A) _

private def sheafSquare (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X) :
    inverseImage (productProjection T X) ⋙ inverseImage (productMap T m) ≅
      inverseImage m ⋙ inverseImage (productProjection T Y) :=
  (inverseImageComposition (productMap T m) (productProjection T X)).symm ≪≫
    inverseImageComposition (productProjection T Y) m

/-- Transposition along the target projection identifies the ordinary mate
with the direct image of the unit for the source projection. -/
private theorem sheafMate_transpose (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (F : Sheaves Y) :
    (inverseDirectAdjunction (productProjection T X)).homEquiv _ _
        (adjointSquareMap (sheafSquare T m) (inverseDirectAdjunction (productMap T m))
          (inverseDirectAdjunction m) F) =
      (directImage m).map ((inverseDirectAdjunction (productProjection T Y)).unit.app F) := by
  let p := productProjection T X
  let q := productProjection T Y
  let j := productMap T m
  let a := inverseDirectAdjunction p
  let b := inverseDirectAdjunction j
  let c := inverseDirectAdjunction m
  let d := inverseDirectAdjunction q
  let e := inverseDirectAdjunction (j ≫ p)
  let L := inverseImage q
  let α := sheafSquare T m
  have hα (G : Sheaves X) :
      (a.comp b).unit.app G ≫ (directImage j ⋙ directImage p).map (α.hom.app G) =
        (c.comp d).unit.app G := by
    have h₁ := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) e G
    rw [← Adjunction.leftAdjointUniq_inv_app e (a.comp b)] at h₁
    have h₂ := Adjunction.unit_leftAdjointUniq_hom_app e (c.comp d) G
    calc
      _ = ((a.comp b).unit.app G ≫ (directImage j ⋙ directImage p).map
          ((inverseImageComposition j p).inv.app G)) ≫
            (directImage j ⋙ directImage p).map ((inverseImageComposition q m).hom.app G) := by
        change _ ≫ (directImage j ⋙ directImage p).map (_ ≫ _) = _
        rw [Functor.map_comp, Category.assoc]
        rfl
      _ = (e.unit.app G) ≫
          (directImage j ⋙ directImage p).map ((inverseImageComposition q m).hom.app G) :=
        congrArg (· ≫ (directImage j ⋙ directImage p).map
          ((inverseImageComposition q m).hom.app G)) h₁
      _ = _ := h₂
  change a.homEquiv _ _
    (b.homEquiv _ _ (α.hom.app ((directImage m).obj F) ≫ L.map (c.counit.app F))) = _
  let g := α.hom.app ((directImage m).obj F) ≫ L.map (c.counit.app F)
  have hg : a.homEquiv _ _ (b.homEquiv _ _ g) =
      (a.comp b).homEquiv ((directImage m).obj F) (L.obj F) g := by
    rw [Adjunction.comp_homEquiv]
    rfl
  change a.homEquiv _ _ (b.homEquiv _ _ g) = _
  rw [hg, Adjunction.homEquiv_unit]
  dsimp only [g]
  rw [Functor.map_comp, ← Category.assoc, hα, Adjunction.comp_unit_app]
  change c.unit.app ((directImage m).obj F) ≫
    (directImage m).map (d.unit.app ((inverseImage m).obj ((directImage m).obj F))) ≫
    (directImage m).map ((directImage q).map (L.map (c.counit.app F))) = _
  rw [← Functor.map_comp, ← Functor.comp_map, ← d.unit.naturality, Functor.map_comp,
    ← Category.assoc]
  simp only [Functor.id_map, Functor.id_obj, c.right_triangle_components, Category.id_comp]
  rfl

private abbrev cochainL {X Y : TopCat.{0}} (g : X ⟶ Y) :=
  (inverseImage g).mapCochainComplexPlus

private abbrev cochainR {X Y : TopCat.{0}} (g : X ⟶ Y) :=
  (directImage g).mapCochainComplexPlus

open private cochainAdjunction exactPlusFactors
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

private abbrev cochainA {X Y : TopCat.{0}} (g : X ⟶ Y) :
    cochainL g ⊣ cochainR g :=
  cochainAdjunction (inverseDirectAdjunction g)

private def cochainSquare (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X) :
    cochainL (productProjection T X) ⋙ cochainL (productMap T m) ≅
      cochainL m ⋙ cochainL (productProjection T Y) where
  hom := (sheafSquare T m).hom.mapCochainComplexPlus
  inv := (sheafSquare T m).inv.mapCochainComplexPlus
  hom_inv_id := by rw [← NatTrans.mapCochainComplexPlus_comp, Iso.hom_inv_id,
    NatTrans.mapCochainComplexPlus_id]; rfl
  inv_hom_id := by rw [← NatTrans.mapCochainComplexPlus_comp, Iso.inv_hom_id,
    NatTrans.mapCochainComplexPlus_id]; rfl

private theorem cochainTranspose_components {X Y : TopCat.{0}} (g : X ⟶ Y)
    {K : CochainComplex.Plus (Sheaves Y)} {J : CochainComplex.Plus (Sheaves X)}
    (f : (cochainL g).obj K ⟶ J) (n : ℤ) :
    (((cochainA g).homEquiv K J f).hom.f n) =
      (inverseDirectAdjunction g).homEquiv _ _ (f.hom.f n) := rfl

private theorem cochainMate_transpose (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    {K : CochainComplex.Plus (Sheaves Y)} {J : CochainComplex.Plus (Sheaves (TopCat.of (T × Y)))}
    (w : K ⟶ (cochainR (productProjection T Y)).obj J) :
    (cochainA (productProjection T X)).homEquiv _ _
      (adjointSquareMap (cochainSquare T m) (cochainA (productMap T m)) (cochainA m) K ≫
        (cochainR (productMap T m)).map
          (((cochainA (productProjection T Y)).homEquiv _ _).symm w)) =
      (cochainR m).map w := by
  let p := productProjection T X
  let q := productProjection T Y
  let j := productMap T m
  let k := ((cochainA q).homEquiv _ _).symm w
  let f := adjointSquareMap (cochainSquare T m) (cochainA j) (cochainA m) K
  apply ObjectProperty.hom_ext
  ext n : 1
  change (((cochainA p).homEquiv _ _ (f ≫ (cochainR j).map k)).hom.f n) =
    ((directImage m).map (w.hom.f n))
  rw [cochainTranspose_components]
  change (inverseDirectAdjunction p).homEquiv _ _
    (adjointSquareMap (sheafSquare T m) (inverseDirectAdjunction j)
      (inverseDirectAdjunction m) (K.obj.X n) ≫ (directImage j).map (k.hom.f n)) = _
  rw [Adjunction.homEquiv_naturality_right, sheafMate_transpose]
  have hk : (inverseDirectAdjunction q).homEquiv _ _ (k.hom.f n) = w.hom.f n := by
    rw [← cochainTranspose_components, Equiv.apply_symm_apply]
  change (directImage m).map ((inverseDirectAdjunction q).unit.app (K.obj.X n)) ≫
    (directImage m).map ((directImage q).map (k.hom.f n)) = _
  rw [← Functor.map_comp]
  exact congrArg ((directImage m).map ·) hk

open Analytic.IntersectionComplex (pullbackSquare boundedBelowPullbackComposition directImageComparison)

private abbrev derivedL {X Y : TopCat.{0}} (g : X ⟶ Y) := boundedBelowInverseImage g

private abbrev derivedR {X Y : TopCat.{0}} (g : X ⟶ Y) := derivedDirectImage g

private abbrev derivedA {X Y : TopCat.{0}} (g : X ⟶ Y) :
    derivedL g ⊣ derivedR g :=
  DerivedLocalSheaves.derivedInverseDirectAdjunctionData g

private abbrev inverseImageFactors {X Y : TopCat.{0}} (g : X ⟶ Y) :=
  exactPlusFactors (inverseImage g)

private theorem inverseImageComposition_factors {X Y Z : TopCat.{0}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : CochainComplex.Plus (Sheaves Z)) :
    (boundedBelowPullbackComposition f g).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        (derivedL f).map ((inverseImageFactors g).hom.app K) ≫
        (inverseImageFactors f).hom.app ((cochainL g).obj K) =
      (inverseImageFactors (f ≫ g)).hom.app K ≫
        DerivedCategory.Plus.Q.map ((inverseImageComposition f g).hom.mapCochainComplexPlus.app K) := by
  apply DerivedCategory.Plus.ι.map_injective
  let L := inverseImage g
  let M := inverseImage f
  let N := inverseImage (f ≫ g)
  let P := L ⋙ M
  let Q := DerivedCategory.Q (C := Sheaves X)
  let K₀ := K.obj
  let e := Functor.mapDerivedCategoryCompIso L M
  let a := N.mapDerivedCategoryFactors.app K₀
  let b := P.mapDerivedCategoryFactors.app K₀
  have hcomp {F G : BoundedBelow Y} (v : F ⟶ G) :
      ((derivedL f).map v).hom = M.mapDerivedCategory.map v.hom := rfl
  have hfac {A B : TopCat.{0}} (g' : A ⟶ B) (K' : CochainComplex.Plus (Sheaves B)) :
      ((inverseImageFactors g').hom.app K').hom =
        (inverseImage g').mapDerivedCategoryFactors.hom.app K'.obj := by
    exact Functor.map_preimage DerivedCategory.Plus.ι _
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, hcomp, hfac]
  let c := (NatIso.mapHomologicalComplex (inverseImageComposition f g) (.up ℤ)).hom.app K₀
  change (derivedInverseImageComposition f g).hom.app (DerivedCategory.Q.obj K₀) ≫
      M.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K₀) ≫
        M.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K₀) =
    a.hom ≫ Q.map c
  have he : e.hom.app (DerivedCategory.Q.obj K₀) ≫ b.hom =
      M.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K₀) ≫
        M.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K₀) := by
    rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj]
    simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.assoc]
    have hId := Q.map_id (((L ⋙ M).mapHomologicalComplex (.up ℤ)).obj K₀)
    rw [hId]
    change _ ≫ _ ≫ 𝟙 _ ≫ b.inv ≫ b.hom = _
    simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← he]
  unfold derivedInverseImageComposition
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Category.assoc]
  change a.hom ≫ Q.map c ≫ b.inv ≫ e.inv.app _ ≫ e.hom.app _ ≫ b.hom = _
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem derivedCounit_factors {X Y : TopCat.{0}} (f : X ⟶ Y)
    (K : CochainComplex.Plus (Sheaves X)) :
    (derivedL f).map ((directImage f).rightDerivedFunctorPlusUnit.app K) ≫
        (derivedA f).counit.app (DerivedCategory.Plus.Q.obj K) =
      (inverseImageFactors f).hom.app ((cochainR f).obj K) ≫
        DerivedCategory.Plus.Q.map ((cochainA f).counit.app K) := by
  let L := inverseImage f
  let R := directImage f
  let α := exactPlusFactors L
  let β := R.rightDerivedFunctorPlusUnit
  let W := CochainComplex.Plus.quasiIso (Sheaves X)
  haveI : (R.rightDerivedFunctorPlus ⋙ exactDerivedPlus L).IsRightDerivedFunctor
      (Functor.whiskerRight β (exactDerivedPlus L) ≫ (Functor.associator _ _ _).hom) W := by
    let δ := Functor.whiskerRight β (exactDerivedPlus L) ≫ (Functor.associator _ _ _).hom
    have hDerives : (CochainComplex.Plus.localizerMorphism (Sheaves X)).Derives
        ((R.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ exactDerivedPlus L) := by
      intro K M f hf
      haveI : IsIso ((R.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
          ((CochainComplex.Plus.localizerMorphism (Sheaves X)).functor.map f)) :=
        CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus R f hf
      exact Functor.map_isIso (exactDerivedPlus L) _
    exact hDerives.isRightDerivedFunctor_of_isIso δ (fun I => by
      dsimp [δ, β, CochainComplex.Plus.localizerMorphism]
      infer_instance)
  exact (cochainA f).derivedε_fac_app W α.hom β K

set_option maxHeartbeats 1000000 in
private theorem productPullback_factors (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaves X)) :
    (pullbackSquare (ConvolutionProjectionBaseChangeSpecs.productSquare T m)).hom.app
        (DerivedCategory.Plus.Q.obj K) ≫
      (derivedL (productProjection T Y)).map ((inverseImageFactors m).hom.app K) ≫
      (inverseImageFactors (productProjection T Y)).hom.app ((cochainL m).obj K) =
    (derivedL (productMap T m)).map
        ((inverseImageFactors (productProjection T X)).hom.app K) ≫
      (inverseImageFactors (productMap T m)).hom.app ((cochainL (productProjection T X)).obj K) ≫
      DerivedCategory.Plus.Q.map ((cochainSquare T m).hom.app K) := by
  let j := productMap T m
  let p := productProjection T X
  let q := productProjection T Y
  let Q := DerivedCategory.Plus.Q (C := Sheaves (TopCat.of (T × Y)))
  let d := DerivedCategory.Plus.Q.obj K
  let e := boundedBelowPullbackComposition j p
  let e' := boundedBelowPullbackComposition q m
  have he : (pullbackSquare (ConvolutionProjectionBaseChangeSpecs.productSquare T m)).hom.app d =
      e.inv.app d ≫ e'.hom.app d := by
    change (e.inv.app d ≫ (𝟙 ((derivedL (j ≫ p)).obj d) ≫ e'.hom.app d)) = _
    rw [Category.id_comp]
  let a := (derivedL q).map ((inverseImageFactors m).hom.app K)
  let b := (inverseImageFactors q).hom.app ((cochainL m).obj K)
  let c := (derivedL j).map ((inverseImageFactors p).hom.app K)
  let v := (inverseImageFactors j).hom.app ((cochainL p).obj K)
  let f := (inverseImageComposition j p).hom.mapCochainComplexPlus.app K
  let f' := (inverseImageComposition q m).hom.mapCochainComplexPlus.app K
  let u := (cochainSquare T m).hom.app K
  let s := (inverseImageFactors (j ≫ p)).hom.app K
  have h₁ : e'.hom.app d ≫ a ≫ b = s ≫ Q.map f' :=
    inverseImageComposition_factors q m K
  have h₂ : e.hom.app d ≫ c ≫ v = s ≫ Q.map f :=
    inverseImageComposition_factors j p K
  have h₃ : f ≫ u = f' := by
    apply ObjectProperty.hom_ext
    ext n : 1
    change (inverseImageComposition j p).hom.app (K.obj.X n) ≫
      (inverseImageComposition j p).inv.app (K.obj.X n) ≫
      (inverseImageComposition q m).hom.app (K.obj.X n) = _
    simp only [Iso.hom_inv_id_app_assoc]
    rfl
  change (pullbackSquare (ConvolutionProjectionBaseChangeSpecs.productSquare T m)).hom.app d ≫
    a ≫ b = c ≫ v ≫ Q.map u
  rw [he, ← cancel_epi (e.hom.app d)]
  calc
    _ = e'.hom.app d ≫ a ≫ b := by
      change e.hom.app d ≫ (e.inv.app d ≫ e'.hom.app d) ≫ a ≫ b = _
      calc
        _ = e.hom.app d ≫ e.inv.app d ≫ e'.hom.app d ≫ a ≫ b :=
          congrArg (fun z => e.hom.app d ≫ z)
            (Category.assoc (e.inv.app d) (e'.hom.app d) (a ≫ b))
        _ = _ := Iso.hom_inv_id_app_assoc e d (e'.hom.app d ≫ a ≫ b)
    _ = s ≫ Q.map f' := h₁
    _ = (s ≫ Q.map f) ≫ Q.map u := by
      rw [← h₃, Q.map_comp, Category.assoc]
    _ = _ := (congrArg (· ≫ Q.map u) h₂.symm).trans (by simp only [Category.assoc])

private abbrev imageUnit {X Y : TopCat.{0}} (f : X ⟶ Y)
    (K : CochainComplex.Plus (Sheaves X)) := (directImage f).rightDerivedFunctorPlusUnit.app K

set_option maxHeartbeats 1000000 in
/-- The actual derived comparison extends the cochain mate along the
right-derived units and the localization isomorphisms for inverse images. -/
private theorem derivedMate_factors (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaves Y)) :
    (derivedL (productProjection T X)).map (imageUnit m K) ≫
      directImageComparison (ConvolutionProjectionBaseChangeSpecs.productSquare T m)
        (derivedA (productMap T m)) (derivedA m) (DerivedCategory.Plus.Q.obj K) ≫
      (derivedR (productMap T m)).map ((inverseImageFactors (productProjection T Y)).hom.app K) =
    (inverseImageFactors (productProjection T X)).hom.app ((cochainR m).obj K) ≫
      DerivedCategory.Plus.Q.map
        (adjointSquareMap (cochainSquare T m) (cochainA (productMap T m)) (cochainA m) K) ≫
      imageUnit (productMap T m) ((cochainL (productProjection T Y)).obj K) := by
  let p := productProjection T X
  let q := productProjection T Y
  let j := productMap T m
  let α := pullbackSquare (ConvolutionProjectionBaseChangeSpecs.productSquare T m)
  let β := cochainSquare T m
  let G := (cochainR m).obj K
  let H := (cochainL q).obj K
  let d := DerivedCategory.Plus.Q.obj K
  let c := (cochainA m).counit.app K
  let f := adjointSquareMap β (cochainA j) (cochainA m) K
  let g := directImageComparison (ConvolutionProjectionBaseChangeSpecs.productSquare T m)
    (derivedA j) (derivedA m) d
  let γ := (inverseImageFactors q).hom.app K
  let ε := (derivedA j).counit
  apply ((derivedA j).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hg : (derivedL j).map g ≫ ε.app ((derivedL q).obj d) =
      α.hom.app ((derivedR m).obj d) ≫ (derivedL q).map ((derivedA m).counit.app d) := by
    change ((derivedA j).homEquiv _ _).symm g = _
    dsimp [g, directImageComparison, adjointSquareMap, α]
    exact Equiv.symm_apply_apply _ _
  have hf : (cochainL j).map f ≫ (cochainA j).counit.app H =
      β.hom.app G ≫ (cochainL q).map c := by
    change ((cochainA j).homEquiv _ _).symm f = _
    exact Equiv.symm_apply_apply _ _
  change (derivedL j).map ((derivedL p).map (imageUnit m K)) ≫
      (derivedL j).map g ≫ (derivedL j).map ((derivedR j).map γ) ≫
      ε.app (DerivedCategory.Plus.Q.obj H) =
    (derivedL j).map ((inverseImageFactors p).hom.app G) ≫
      (derivedL j).map (DerivedCategory.Plus.Q.map f) ≫
      (derivedL j).map (imageUnit j H) ≫ ε.app (DerivedCategory.Plus.Q.obj H)
  have hn := ε.naturality γ
  change (derivedL j).map ((derivedR j).map γ) ≫ ε.app _ = ε.app _ ≫ γ at hn
  erw [hn, reassoc_of% hg]
  have hα := α.hom.naturality (imageUnit m K)
  change (derivedL j).map ((derivedL p).map (imageUnit m K)) ≫ α.hom.app _ =
    α.hom.app _ ≫ (derivedL q).map ((derivedL m).map (imageUnit m K)) at hα
  erw [reassoc_of% hα, ← Functor.map_comp_assoc, derivedCounit_factors,
    Functor.map_comp, Category.assoc]
  have hγ := (inverseImageFactors q).hom.naturality c
  change (derivedL q).map (DerivedCategory.Plus.Q.map c) ≫ γ =
    (inverseImageFactors q).hom.app ((cochainL m).obj G) ≫
      DerivedCategory.Plus.Q.map ((cochainL q).map c) at hγ
  simp only [Category.assoc]
  erw [hγ]
  have hc := productPullback_factors T m G
  simp only [pullbackSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] at hc ⊢
  erw [reassoc_of% hc]
  let D := DerivedCategory.Plus.Q (C := Sheaves (TopCat.of (T × Y)))
  have hcj : (derivedL j).map (imageUnit j H) ≫ ε.app (D.obj H) =
      (inverseImageFactors j).hom.app ((cochainR j).obj H) ≫
        D.map ((cochainA j).counit.app H) := derivedCounit_factors j H
  erw [hcj]
  have hf' := (inverseImageFactors j).hom.naturality f
  change (derivedL j).map (DerivedCategory.Plus.Q.map f) ≫
      (inverseImageFactors j).hom.app ((cochainR j).obj H) =
    (inverseImageFactors j).hom.app ((cochainL p).obj G) ≫
      D.map ((cochainL j).map f) at hf'
  erw [reassoc_of% hf']
  have hmaps : D.map (β.hom.app G) ≫ D.map ((cochainL q).map c) =
      D.map ((cochainL j).map f) ≫ D.map ((cochainA j).counit.app H) := by
    exact (D.map_comp (β.hom.app G) ((cochainL q).map c)).symm.trans
      ((congrArg D.map hf.symm).trans (D.map_comp ((cochainL j).map f) ((cochainA j).counit.app H)))
  exact congrArg (fun z => (derivedL j).map ((inverseImageFactors p).hom.app G) ≫
    (inverseImageFactors j).hom.app ((cochainL p).obj G) ≫ z) hmaps

private theorem projectionCochainMate_quasiIso (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (hT : HasContractibleOpenBasis T)
    (K : CochainComplex.Plus (Sheaves Y))
    (J : CochainComplex.Plus (Sheaves (TopCat.of (T × Y))))
    (w : K ⟶ (cochainR (productProjection T Y)).obj J)
    (hlocal : ∀ (D : Opens T) (U : Opens X), ContractibleSpace D →
      QuasiIso (((sectionsOn U).mapHomologicalComplex (.up ℤ)).map ((cochainR m).map w).hom ≫
        (openSectionComplexes ((cochainR (productMap T m)).obj J).obj).map
          (productOpenInProjection D U).op)) :
    QuasiIso
      ((adjointSquareMap (cochainSquare T m) (cochainA (productMap T m)) (cochainA m) K ≫
        (cochainR (productMap T m)).map
          (((cochainA (productProjection T Y)).homEquiv _ _).symm w)).hom) := by
  let p := productProjection T X
  let j := productMap T m
  let q := productProjection T Y
  let f := adjointSquareMap (cochainSquare T m) (cochainA j) (cochainA m) K ≫
    (cochainR j).map (((cochainA q).homEquiv _ _).symm w)
  let u := (cochainR m).map w
  have e (n : ℤ) : (inverseDirectAdjunction p).homEquiv _ _ (f.hom.f n) = u.hom.f n := by
    rw [← cochainTranspose_components, cochainMate_transpose]
  apply quasiIso_of_stalk
  rintro ⟨t, x⟩
  apply stalkOfTranspose_quasiIso p (t, x) f.hom u.hom e
  apply stalkProduct_quasiIso t x hT
  intro D U
  exact hlocal D.val.val U.val D.property

private theorem projectionCochainPullback_quasiIso (T Y : TopCat.{0})
    (hT : HasContractibleOpenBasis T)
    (K : CochainComplex.Plus (Sheaves Y))
    (J : CochainComplex.Plus (Sheaves (TopCat.of (T × Y))))
    (w : K ⟶ (cochainR (productProjection T Y)).obj J)
    (hlocal : ∀ (D : Opens T) (U : Opens Y), ContractibleSpace D →
      QuasiIso (((sectionsOn U).mapHomologicalComplex (.up ℤ)).map w.hom ≫
        (openSectionComplexes J.obj).map (productOpenInProjection D U).op)) :
    QuasiIso (((cochainA (productProjection T Y)).homEquiv _ _).symm w).hom := by
  let p := productProjection T Y
  let f := ((cochainA p).homEquiv _ _).symm w
  have e (n : ℤ) : (inverseDirectAdjunction p).homEquiv _ _ (f.hom.f n) = w.hom.f n := by
    rw [← cochainTranspose_components, Equiv.apply_symm_apply]
  apply quasiIso_of_stalk
  rintro ⟨t, y⟩
  apply stalkOfTranspose_quasiIso p (t, y) f.hom w.hom e
  apply stalkProduct_quasiIso t y hT
  intro D U
  exact hlocal D.val.val U.val D.property

private def cochainProjection (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (D : Opens T) (U : Opens X)
    {K : CochainComplex.Plus (Sheaves Y)}
    {J : CochainComplex.Plus (Sheaves (TopCat.of (T × Y)))}
    (w : K ⟶ (cochainR (productProjection T Y)).obj J) :
    (openSectionComplexes ((cochainR m).obj K).obj).obj (op U) ⟶
      (openSectionComplexes ((cochainR (productMap T m)).obj J).obj).obj (op (productOpen D U)) :=
  ((sectionsOn U).mapHomologicalComplex (.up ℤ)).map ((cochainR m).map w).hom ≫
    (openSectionComplexes ((cochainR (productMap T m)).obj J).obj).map
      (productOpenInProjection D U).op

private def shiftPlus {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex.Plus C) (n : ℤ) : CochainComplex.Plus C :=
  ⟨(CochainComplex.shiftFunctor C n).obj K.obj, by
    obtain ⟨k, hk⟩ := K.property
    exact ⟨k - n, K.obj.isStrictlyGE_shift k n _ (by omega)⟩⟩

private def shiftCochains {X Y : TopCat.{0}} {K : CochainComplex.Plus (Sheaves Y)}
    {J : CochainComplex.Plus (Sheaves X)} (q : X ⟶ Y)
    (w : K ⟶ (cochainR q).obj J) (n : ℤ) :
    shiftPlus K n ⟶ (cochainR q).obj (shiftPlus J n) :=
  ObjectProperty.homMk ((CochainComplex.shiftFunctor _ n).map w.hom ≫
    ((directImage q).mapCochainComplexShiftIso n).inv.app J.obj)

private theorem shiftedProjection_quasiIso (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (D : Opens T) (U : Opens X)
    {K : CochainComplex.Plus (Sheaves Y)}
    {J : CochainComplex.Plus (Sheaves (TopCat.of (T × Y)))}
    (w : K ⟶ (cochainR (productProjection T Y)).obj J) (n : ℤ)
    (h : QuasiIso (cochainProjection T m D U w)) :
    QuasiIso (cochainProjection T m D U (shiftCochains (productProjection T Y) w n)) := by
  let A := sectionsOn ((Opens.map m).obj U)
  let B := sectionsOn (X := TopCat.of (T × Y)) ((Opens.map (productMap T m)).obj (productOpen D U))
  haveI : B.Additive := ⟨by intros; rfl⟩
  let eA := (A.mapCochainComplexShiftIso n).app K.obj
  let eB := (B.mapCochainComplexShiftIso n).app J.obj
  have he : cochainProjection T m D U (shiftCochains (productProjection T Y) w n) ≫ eB.hom =
      eA.hom ≫ (CochainComplex.shiftFunctor Coeff.{0} n).map (cochainProjection T m D U w) := by
    ext i : 1
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    have hcomp : (shiftCochains (productProjection T Y) w n).hom.f i =
        w.hom.f (i + n) := by
      change w.hom.f (i + n) ≫ 𝟙 _ = _
      exact Category.comp_id _
    change (((cochainR m).map (shiftCochains (productProjection T Y) w n)).hom.f i).hom.app
        (op U) ≫ _ = (((cochainR m).map w).hom.f (i + n)).hom.app (op U) ≫ _
    congr 1
  haveI : QuasiIso ((CochainComplex.shiftFunctor Coeff.{0} n).map (cochainProjection T m D U w)) :=
    (CochainComplex.quasiIso_shift_iff _ n).mpr h
  haveI : QuasiIso
      (cochainProjection T m D U (shiftCochains (productProjection T Y) w n) ≫ eB.hom) :=
    he.symm ▸ inferInstance
  exact quasiIso_of_comp_right _ eB.hom

set_option maxHeartbeats 1000000 in
private theorem derivedProjection_of_cochains (T : TopCat.{0}) {X Y : TopCat.{0}} (m : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaves Y))
    (J : CochainComplex.Plus (Sheaves (TopCat.of (T × Y))))
    (w : K ⟶ (cochainR (productProjection T Y)).obj J)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.obj.X n))
    (hJ : ∀ n, TopCat.Sheaf.IsFlasque (J.obj.X n))
    (hq : QuasiIso (((cochainA (productProjection T Y)).homEquiv _ _).symm w).hom)
    (hφ : QuasiIso ((adjointSquareMap (cochainSquare T m) (cochainA (productMap T m))
      (cochainA m) K) ≫ (cochainR (productMap T m)).map
        (((cochainA (productProjection T Y)).homEquiv _ _).symm w)).hom) :
    IsIso (directImageComparison (ConvolutionProjectionBaseChangeSpecs.productSquare T m)
      (derivedA (productMap T m)) (derivedA m) (DerivedCategory.Plus.Q.obj K)) := by
  let p := productProjection T X
  let q := productProjection T Y
  let j := productMap T m
  let v := ((cochainA q).homEquiv _ _).symm w
  let f := adjointSquareMap (cochainSquare T m) (cochainA j) (cochainA m) K
  let g := directImageComparison (ConvolutionProjectionBaseChangeSpecs.productSquare T m)
    (derivedA j) (derivedA m) (DerivedCategory.Plus.Q.obj K)
  let Q := DerivedCategory.Plus.Q (C := Sheaves (TopCat.of (T × X)))
  let e := (inverseImageFactors q).hom.app K
  let QY := DerivedCategory.Plus.Q (C := Sheaves (TopCat.of (T × Y)))
  let u := (derivedR j).map (e ≫ QY.map v)
  let l := (derivedL p).map (imageUnit m K)
  let r := (inverseImageFactors p).hom.app ((cochainR m).obj K)
  haveI : IsIso (imageUnit m K) := directImageUnit_isIso_of_flasque m K hK
  haveI : IsIso (imageUnit j J) := directImageUnit_isIso_of_flasque j J hJ
  haveI : IsIso l := Functor.map_isIso _ _
  haveI : IsIso (QY.map v) :=
    Localization.inverts QY (CochainComplex.Plus.quasiIso _) v hq
  haveI : IsIso (Q.map (f ≫ (cochainR j).map v)) :=
    Localization.inverts Q (CochainComplex.Plus.quasiIso _) _ hφ
  haveI : IsIso u := by dsimp [u]; infer_instance
  have he : l ≫ g ≫ u = r ≫ Q.map (f ≫ (cochainR j).map v) ≫ imageUnit j J := by
    dsimp only [u]
    have hg : l ≫ g ≫ (derivedR j).map e = r ≫ Q.map f ≫
        imageUnit j ((cochainL q).obj K) := derivedMate_factors T m K
    rw [Functor.map_comp, reassoc_of% hg]
    have h := ((directImage j).rightDerivedFunctorPlusUnit).naturality v
    change Q.map ((cochainR j).map v) ≫ imageUnit j J =
      imageUnit j ((cochainL q).obj K) ≫ (derivedR j).map (QY.map v) at h
    rw [← h]
    exact congrArg (fun z => r ≫ z)
      ((reassoc_of% (Q.map_comp f ((cochainR j).map v)).symm) (imageUnit j J))
  haveI : IsIso (l ≫ g ≫ u) := he.symm ▸ inferInstance
  haveI : IsIso (g ≫ u) := IsIso.of_isIso_comp_left l _
  exact IsIso.of_isIso_comp_right g u

open private sheafComplex_flasque from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConstantSheafComparison

private abbrev singularSheafResolution (Y : TopCat.{0}) : CochainComplex.Plus (Sheaves Y) :=
  ⟨sheafComplex Y, 0, SingularCochainSheaves.nonnegativeSupport Y⟩

set_option maxHeartbeats 1000000 in
/-- Projection along the parameter space commutes with derived direct image
of the shifted rational coefficients on the ordered incidence space. -/
theorem projectionBaseChange : ConvolutionProjectionBaseChangeSpecs.Expected.ProjectionBaseChange := by
  intro T _ _ _ hT a b
  let X := ConvolutionUnitConeSpecs.surface
  let Y := ConvolutionUnitConeSpecs.ordered
  let m : Y ⟶ X := ConvolutionUnitConeSpecs.convolutionMap
  let j := productMap T m
  let q := productProjection T Y
  let Z := TopCat.of (T × Y)
  let F := ConvolutionUnitConeSpecs.orderedFactor
  obtain ⟨h₂, hL, hH, hY⟩ := ConvolutionAnalyticCharts.orderedTopology
  letI : SecondCountableTopology Y := h₂
  letI : LocallyCompactSpace Y := hL
  letI : T2Space Y := hH
  letI : SecondCountableTopology Z := inferInstanceAs (SecondCountableTopology (T × Y))
  letI : LocallyCompactSpace Z := inferInstanceAs (LocallyCompactSpace (T × Y))
  letI : T2Space Z := inferInstanceAs (T2Space (T × Y))
  let K₀ := singularSheafResolution Y
  let J₀ := singularSheafResolution Z
  let w₀ : K₀ ⟶ (cochainR q).obj J₀ := ObjectProperty.homMk (sheafCochainPullback q)
  let n : ℤ := 2
  let K := shiftPlus K₀ n
  let J := shiftPlus J₀ n
  let w := shiftCochains q w₀ n
  have hY' := SmallCochainComparison.sectionMap_quasiIso Y
  have hZ' := SmallCochainComparison.sectionMap_quasiIso Z
  have hK (i : ℤ) : TopCat.Sheaf.IsFlasque (K.obj.X i) :=
    sheafComplex_flasque Y (i + n)
  have hJ (i : ℤ) : TopCat.Sheaf.IsFlasque (J.obj.X i) :=
    sheafComplex_flasque Z (i + n)
  have hq := projectionCochainPullback_quasiIso T Y hT K J w (fun D U hD =>
    shiftedProjection_quasiIso T (𝟙 Y) D U w₀ n
      (projectionSections_quasiIso T (𝟙 Y) D U hD hY' hZ'))
  have hφ := projectionCochainMate_quasiIso T m hT K J w (fun D U hD =>
    shiftedProjection_quasiIso T m D U w₀ n
      (projectionSections_quasiIso T m D U hD hY' hZ'))
  have h := derivedProjection_of_cochains T m K J w hK hJ hq hφ
  let Q := DerivedCategory.Plus.Q (C := Sheaves Y)
  let u : Analytic.ConstantSheafCohomology.rationalComplex Y ⟶ K₀ :=
    ObjectProperty.homMk (augmentation Y)
  haveI : IsIso (Q.map u) := Localization.inverts Q (CochainComplex.Plus.quasiIso _)
    u (SingularCochainSheaves.resolution Y hY)
  let e : F ≅ Q.obj K := DerivedCategory.Plus.ι.preimageIso (by
    change (DerivedCategory.Q.obj (Analytic.ConstantSheafCohomology.rationalComplex Y).obj)⟦n⟧ ≅
      DerivedCategory.Q.obj (CochainComplex.shiftFunctor (Sheaves Y) n |>.obj K₀.obj)
    haveI : IsIso (DerivedCategory.Q.map u.hom) :=
      DerivedCategory.Plus.ι.map_isIso (Q.map u)
    exact (shiftFunctor (Derived Y) n).mapIso (asIso (DerivedCategory.Q.map u.hom)) ≪≫
      ((DerivedCategory.Q (C := Sheaves Y)).commShiftIso n).symm.app K₀.obj)
  let α := pullbackSquare (ConvolutionProjectionBaseChangeSpecs.productSquare T m)
  have hm (A : BoundedBelow Y) :
      adjointSquareMap α (derivedA j) (derivedA m) A =
        (mateEquiv (derivedA m) (derivedA j) α.hom).app A := by
    apply ((derivedA j).homEquiv _ _).symm.injective
    rw [adjointSquareMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit (derivedA m) (derivedA j) α.hom A).symm
  apply mate_isIso_of_adjunctions α (derivedA j) a (derivedA m) b F
  rw [hm]
  apply (NatTrans.isIso_app_iff_of_iso _ e).mpr
  rw [← hm]
  exact h

end RepTheorySurvey.Geometric.ConvolutionProjectionBaseChange
