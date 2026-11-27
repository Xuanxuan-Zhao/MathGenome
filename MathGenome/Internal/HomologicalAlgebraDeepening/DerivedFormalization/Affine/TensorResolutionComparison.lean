import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.TensorResolutionComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeLifting
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeFlatness
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedTensor
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits CategoryTheory.Prod

universe u v

namespace DerivedFormalization.Affine.TensorResolutionComparison

open _root_.Specs.DerivedFormalization.Affine.TensorResolutionComparison
open _root_.Specs.DerivedFormalization.Affine.Tensor (dgCat pure)
open _root_.Specs.DerivedFormalization.Affine.DerivedTensor (TensorResolution)
open _root_.Specs.DerivedFormalization.DG.Derived
  (HomotopyCategoryLaws homotopyCategory quotient)
open _root_.Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B C B' C' : NonpositiveCDGA.{u,v} k}

private abbrev coproductModel : CoproductModel (Tensor.moduleTensorModel.{u,v} k) where
  algebra f g := Tensor.algebraTensorModel f g
  formulas f g := Tensor.algebraTensorModel_formulas f g

private abbrev tensorObj (f : A ⟶ B) (g : A ⟶ C) :=
  (coproductModel (k := k)).tensor f g

private theorem resolution_exists (f : A ⟶ B) : Nonempty (Resolution f) := by
  obtain ⟨P, i, p, h, hsf, hs, hq⟩ := _root_.DerivedFormalization.semifreeResolution f
  exact ⟨⟨P, i, p, h, hsf, hs, hq⟩⟩

private theorem semifree_flat (f : A ⟶ B) (h : Semifree.IsSemifree A f) :
    Tensor.KFlat (underlying f) :=
  SemifreeFlatness.semifree_algebra_kFlat (Tensor.moduleTensorModel k) f
    (Tensor.moduleTensor_formulas (𝟙 A.toCommDGAlgebra) (underlying f)) h

private def coproductIsColimit (f : A ⟶ B) (g : A ⟶ C) :
    IsColimit ((coproductModel (k := k)).cofan f g) := by
  classical
  let S := coproductModel (k := k)
  let maps (s : BinaryCofan (Under.mk f) (Under.mk g)) :
      ∃! t : S.tensor f g ⟶ s.pt.right,
        S.inl f g ≫ t = s.inl.right ∧ S.inr f g ≫ t = s.inr.right :=
    (S.formulas f g).coproduct s.inl.right s.inr.right
      ((Under.w s.inl).trans (Under.w s.inr).symm)
  let desc (s : BinaryCofan (Under.mk f) (Under.mk g)) :
      Under.mk (S.base f g) ⟶ s.pt :=
    Under.homMk (maps s).choose (by
      change (g ≫ S.inr f g) ≫ (maps s).choose = s.pt.hom
      rw [Category.assoc, (maps s).choose_spec.1.2]
      exact Under.w s.inr)
  apply BinaryCofan.isColimitMk desc
  · intro s
    apply Under.UnderMorphism.ext
    exact (maps s).choose_spec.1.1
  · intro s
    apply Under.UnderMorphism.ext
    exact (maps s).choose_spec.1.2
  · intro s m hl hr
    apply Under.UnderMorphism.ext
    exact (maps s).choose_spec.2 m.right
      ⟨congrArg Under.Hom.right hl, congrArg Under.Hom.right hr⟩

/-- A cdga map over the base induces the same chain map on the restricted
regular modules. -/
private def underlyingMap {f : A ⟶ B} {g : A ⟶ C}
    (b : B ⟶ C) (hb : f ≫ b = g) : underlying f ⟶ underlying g where
  app _ := b.chainMap
  comm_act := by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    change b.chainMap.f n (B.mul i j n h x (f.chainMap.f j a)) =
      C.mul i j n h (b.chainMap.f i x) (g.chainMap.f j a)
    rw [b.map_mul]
    congr 1
    exact congrArg (fun t : A ⟶ C => t.chainMap.f j a) hb

private theorem underlyingMap_quasiIso {f : A ⟶ B} {g : A ⟶ C}
    (b : B ⟶ C) (hb : f ≫ b = g) (hq : NonpositiveCDGA.IsQuasiIso b) :
    RightDGModule.IsQuasiIso (underlyingMap b hb) := fun _ => hq

private def tensorMap {f : A ⟶ B} {g : A ⟶ C} {f' : A ⟶ B'} {g' : A ⟶ C'}
    (b : B ⟶ B') (c : C ⟶ C') (hb : f ≫ b = f') (hc : g ≫ c = g') :
    tensorObj f g ⟶ tensorObj f' g' :=
  Tensor.algebraMap (a := 𝟙 A.toCommDGAlgebra) f g f' g' b c
    (hb.trans (Category.id_comp f').symm) (hc.trans (Category.id_comp g').symm)

private theorem tensorMap_induced {f : A ⟶ B} {g : A ⟶ C} {f' : A ⟶ B'} {g' : A ⟶ C'}
    (b : B ⟶ B') (c : C ⟶ C') (hb : f ≫ b = f') (hc : g ≫ c = g') :
    (coproductModel (k := k)).Induced b c (tensorMap b c hb hc) where
  inl := Tensor.algebraMap_inl _ _ _ _ _ _ _ _
  inr := Tensor.algebraMap_inr _ _ _ _ _ _ _ _
  tmul := Tensor.algebraMap_pure _ _ _ _ _ _ _ _

private theorem tensorMap_over_base
    {f : A ⟶ B} {g : A ⟶ C} {f' : A ⟶ B'} {g' : A ⟶ C'}
    (b : B ⟶ B') (c : C ⟶ C') (hb : f ≫ b = f') (hc : g ≫ c = g') :
    (coproductModel (k := k)).base f g ≫ tensorMap b c hb hc =
      (coproductModel (k := k)).base f' g' := by
  change (g ≫ (coproductModel (k := k)).inr f g) ≫ tensorMap b c hb hc =
    g' ≫ (coproductModel (k := k)).inr f' g'
  rw [Category.assoc, (tensorMap_induced b c hb hc).inr, ← Category.assoc, hc]

set_option maxHeartbeats 800000 in
private theorem tensorMap_square
    {f : A ⟶ B} {g : A ⟶ C} {f' : A ⟶ B'} {g' : A ⟶ C'}
    (b : B ⟶ B') (c : C ⟶ C') (hb : f ≫ b = f') (hc : g ≫ c = g') :
    (Tensor.baseAlgebraModuleIso f g).hom ≫
        underlyingMap (tensorMap b c hb hc) (tensorMap_over_base b c hb hc) =
      (Tensor.extension (𝟙 A.toCommDGAlgebra) (underlying g)).map (underlyingMap b hb) ≫
        Tensor.mapSecond (𝟙 A.toCommDGAlgebra) (underlying f') (underlyingMap c hc) ≫
        (Tensor.baseAlgebraModuleIso f' g').hom := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Tensor.pure_ext (f := 𝟙 A.toCommDGAlgebra) (M := underlying f) (N := underlying g)
  intro i j h x y
  change (tensorMap b c hb hc).chainMap.f n
      (((Tensor.baseAlgebraModuleIso f g).hom.app ()).f n (pure (𝟙 A.toCommDGAlgebra) i j n h x y)) =
    ((Tensor.baseAlgebraModuleIso f' g').hom.app ()).f n
      (((Tensor.mapSecond (𝟙 A.toCommDGAlgebra) (underlying f') (underlyingMap c hc)).app ()).f n
        ((((Tensor.extension (𝟙 A.toCommDGAlgebra) (underlying g)).map
          (underlyingMap b hb)).app ()).f n (pure (𝟙 A.toCommDGAlgebra) i j n h x y)))
  rw [Tensor.baseAlgebraModuleIso_pure f g, Tensor.map_first_pure, Tensor.map_second_pure,
    Tensor.baseAlgebraModuleIso_pure f' g']
  exact (tensorMap_induced b c hb hc).tmul i j n h x y

private theorem tensorMap_quasiIso
    {f : A ⟶ B} {g : A ⟶ C} {f' : A ⟶ B'} {g' : A ⟶ C'}
    (b : B ⟶ B') (c : C ⟶ C') (hb : f ≫ b = f') (hc : g ≫ c = g')
    (h₁ : RightDGModule.IsQuasiIso
      ((Tensor.extension (𝟙 A.toCommDGAlgebra) (underlying g)).map (underlyingMap b hb)))
    (h₂ : RightDGModule.IsQuasiIso
      (Tensor.mapSecond (𝟙 A.toCommDGAlgebra) (underlying f') (underlyingMap c hc))) :
    NonpositiveCDGA.IsQuasiIso (tensorMap b c hb hc) := by
  let ev := RightDGModuleModel.eval (A := dgCat A.toCommDGAlgebra) ()
  let e := ev.mapIso (Tensor.baseAlgebraModuleIso f g)
  let e' := ev.mapIso (Tensor.baseAlgebraModuleIso f' g')
  let l := ev.map ((Tensor.extension (𝟙 A.toCommDGAlgebra) (underlying g)).map (underlyingMap b hb))
  let r := ev.map (Tensor.mapSecond (𝟙 A.toCommDGAlgebra) (underlying f') (underlyingMap c hc))
  let t := (tensorMap b c hb hc).chainMap
  have hs : e.hom ≫ t = l ≫ r ≫ e'.hom := by
    exact congrArg (fun a => RightDGModuleHomModel.app a ()) (tensorMap_square b c hb hc)
  have he' : QuasiIso e'.hom := quasiIso_of_isIso _
  have he : QuasiIso e.hom := quasiIso_of_isIso _
  have hr := quasiIso_comp r e'.hom (hφ := h₂ ()) (hφ' := he')
  have hl := quasiIso_comp l (r ≫ e'.hom) (hφ := h₁ ()) (hφ' := hr)
  exact quasiIso_of_comp_left e.hom t (hφ := he) (hφφ' := hs ▸ hl)

private theorem tensorMap_first_quasiIso {f : A ⟶ B} {g : A ⟶ C} {f' : A ⟶ B'}
    (b : B ⟶ B') (hb : f ≫ b = f') (h : NonpositiveCDGA.IsQuasiIso b)
    (hg : Tensor.KFlat (underlying g)) :
    NonpositiveCDGA.IsQuasiIso (tensorMap b (𝟙 C) hb (Category.comp_id g)) := by
  apply tensorMap_quasiIso
  · exact hg.map_quasiIso _ (underlyingMap_quasiIso b hb h)
  · have hid : underlyingMap (𝟙 C) (Category.comp_id g) = 𝟙 (underlying g) := rfl
    rw [hid]
    change RightDGModule.IsQuasiIso
      ((Tensor.secondFunctor (𝟙 A.toCommDGAlgebra) (underlying f')).map (𝟙 (underlying g)))
    rw [(Tensor.secondFunctor (𝟙 A.toCommDGAlgebra) (underlying f')).map_id]
    intro a
    rw [RightDGModuleModel.id_app]
    infer_instance

private theorem tensorMap_second_quasiIso {f : A ⟶ B} {g : A ⟶ C} {g' : A ⟶ C'}
    (c : C ⟶ C') (hc : g ≫ c = g') (h : NonpositiveCDGA.IsQuasiIso c)
    (hf : Tensor.KFlat (underlying f)) :
    NonpositiveCDGA.IsQuasiIso (tensorMap (𝟙 B) c (Category.comp_id f) hc) := by
  apply tensorMap_quasiIso
  · have hid : underlyingMap (𝟙 B) (Category.comp_id f) = 𝟙 (underlying f) := rfl
    rw [hid, (Tensor.extension (𝟙 A.toCommDGAlgebra) (underlying g)).map_id]
    intro a
    rw [RightDGModuleModel.id_app]
    infer_instance
  · exact Tensor.KFlat.map_quasiIso_second _ hf _ (underlyingMap_quasiIso c hc h)

private theorem augmentationComparisons :
    AugmentationComparisons (coproductModel (k := k)) := by
  intro A B C f g P Q
  exact
    ⟨⟨_, tensorMap_induced (𝟙 P.obj) Q.augmentation (Category.comp_id _) Q.commutes,
        tensorMap_second_quasiIso Q.augmentation Q.commutes Q.quasiIso
          (semifree_flat P.base P.semifree)⟩,
      ⟨_, tensorMap_induced P.augmentation (𝟙 Q.obj) P.commutes (Category.comp_id _),
        tensorMap_first_quasiIso P.augmentation P.commutes P.quasiIso
          (semifree_flat Q.base Q.semifree)⟩⟩

private theorem resolutionComparisons :
    ResolutionComparisons (coproductModel (k := k)) := by
  intro A B B' f f' b hb hqb P P'
  have hbase : P.base ≫ (P.augmentation ≫ b) = f' := by
    rw [← Category.assoc, P.commutes, hb]
  obtain ⟨p, hp, ha⟩ :=
    Semifree.exists_lift_of_surjective_quasiIso P.base P'.base f' (P.augmentation ≫ b) P'.augmentation
      P.semifree hbase P'.commutes P'.surjective P'.quasiIso
  have hcomp : QuasiIso (p.chainMap ≫ P'.augmentation.chainMap) := by
    have hc : p.chainMap ≫ P'.augmentation.chainMap = P.augmentation.chainMap ≫ b.chainMap :=
      congrArg (fun t : P.obj ⟶ B' => t.chainMap) ha
    rw [hc]
    exact quasiIso_comp _ _ (hφ := P.quasiIso) (hφ' := hqb)
  have hq : NonpositiveCDGA.IsQuasiIso p :=
    (quasiIso_iff_comp_right p.chainMap P'.augmentation.chainMap (hφ' := P'.quasiIso)).1 hcomp
  refine ⟨p, hp, ha, hq, ?_⟩
  intro C g hg
  exact
    ⟨⟨_, tensorMap_induced p (𝟙 C) hp (Category.comp_id g),
        tensorMap_first_quasiIso p hp hq hg⟩,
      ⟨_, tensorMap_induced (𝟙 C) p (Category.comp_id g) hp,
        tensorMap_second_quasiIso p hp hq hg⟩⟩

private theorem id_quasiIso (B : NonpositiveCDGA.{u,v} k) :
    NonpositiveCDGA.IsQuasiIso (𝟙 B) := by
  change QuasiIso (𝟙 B.complex)
  infer_instance

private theorem modelZigzags : ModelZigzags (coproductModel.{u,v} (k := k)) := by
  intro A B C f g
  constructor
  · intro P P' Q
    obtain ⟨a, _, ha⟩ := (augmentationComparisons P Q).1
    obtain ⟨c, _, hc⟩ := (augmentationComparisons P' Q).1
    obtain ⟨_, _, _, _, h⟩ := resolutionComparisons (𝟙 B) (Category.comp_id f)
      (id_quasiIso B) P P'
    obtain ⟨b, _, hb⟩ := (h Q.base (semifree_flat Q.base Q.semifree)).1
    exact ⟨a, b, c, ha, hb, hc⟩
  · intro P Q Q'
    obtain ⟨a, _, ha⟩ := (augmentationComparisons P Q).2
    obtain ⟨c, _, hc⟩ := (augmentationComparisons P Q').2
    obtain ⟨_, _, _, _, h⟩ := resolutionComparisons (𝟙 C) (Category.comp_id g)
      (id_quasiIso C) Q Q'
    obtain ⟨b, _, hb⟩ := (h P.base (semifree_flat P.base P.semifree)).2
    exact ⟨a, b, c, ha, hb, hc⟩

open private tensorResolution onFlatReplacements quasiIsoIso
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedTensor

set_option maxHeartbeats 800000 in
private theorem moduleComputations (A : NonpositiveCDGA.{u,v} k)
    (h : HomotopyCategoryLaws (dgCat A.toCommDGAlgebra)) :
    ∃ R : TensorResolution (Tensor.moduleTensorModel.{u,v} k) A.toCommDGAlgebra h,
      ModuleComputations (coproductModel (k := k)) h R := by
  refine ⟨tensorResolution A.toCommDGAlgebra, ?_⟩
  intro B C f g
  let _ := derivedCategoryInstance (dgCat A.toCommDGAlgebra) h
  let D := DerivedTensor.derivedTensor A.toCommDGAlgebra
  let L := RightDGModule.toHomotopyCategory (dgCat A.toCommDGAlgebra) ⋙
    RightDGModule.Q (dgCat A.toCommDGAlgebra) h
  refine ⟨?_, ?_, ?_⟩
  · intro P Q
    let p := underlyingMap P.augmentation P.commutes
    let q := underlyingMap Q.augmentation Q.commutes
    exact ⟨onFlatReplacements p q
      (semifree_flat P.base P.semifree) (semifree_flat Q.base Q.semifree)
      (underlyingMap_quasiIso _ _ P.quasiIso) (underlyingMap_quasiIso _ _ Q.quasiIso) ≪≫
      L.mapIso (Tensor.baseAlgebraModuleIso P.base Q.base)⟩
  · intro P
    let e := quasiIsoIso (underlyingMap P.augmentation P.commutes)
      (underlyingMap_quasiIso _ _ P.quasiIso)
    exact ⟨D.mapIso (e.symm.prod (Iso.refl (L.obj (underlying g)))) ≪≫
      DerivedTensor.onFlatLeft (semifree_flat P.base P.semifree) (underlying g) ≪≫
      L.mapIso (Tensor.baseAlgebraModuleIso P.base g)⟩
  · intro Q
    let e := quasiIsoIso (underlyingMap Q.augmentation Q.commutes)
      (underlyingMap_quasiIso _ _ Q.quasiIso)
    exact ⟨D.mapIso ((Iso.refl (L.obj (underlying f))).prod e.symm) ≪≫
      DerivedTensor.onFlatRight (underlying f) (semifree_flat Q.base Q.semifree) ≪≫
      L.mapIso (Tensor.baseAlgebraModuleIso f Q.base)⟩

private theorem affineDiagrams : AffineDiagrams (coproductModel.{u,v} (k := k)) := by
  intro A B C f g P
  let S := coproductModel (k := k)
  let X := _root_.DerivedFormalization.Affine.derivedSpec.{u,v} k
  have : X.IsLocalization (NonpositiveCDGA.quasiIsomorphisms.{u,v} k).op :=
    Localization.isLocalization_op
  let e := Localization.isoOfHom X (NonpositiveCDGA.quasiIsomorphisms.{u,v} k).op
    P.augmentation.op P.quasiIso
  let l := X.map (S.inl P.base g).op ≫ e.inv
  have hl : l ≫ X.map P.augmentation.op = X.map (S.inl P.base g).op := by
    change (X.map (S.inl P.base g).op ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  have ha : X.map P.augmentation.op ≫ X.map P.base.op = X.map f.op := by
    rw [← X.map_comp, ← op_comp, P.commutes]
  have ht : X.map (S.inl P.base g).op ≫ X.map P.base.op =
      X.map (S.inr P.base g).op ≫ X.map g.op := by
    rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun t : A ⟶ S.tensor P.base g => X.map t.op) (S.formulas P.base g).base
  exact ⟨l, hl, by rw [← ha, ← Category.assoc, hl, ht]⟩

/-- The strict coproduct of two semifree resolutions computes the derived
tensor. The augmentation in either factor relates it to the one-sided
model by a strict cdga quasi-isomorphism. -/
theorem tensorModels : TensorModels.{u,v} := by
  intro k _ _
  exact ⟨Tensor.moduleTensorModel k, coproductModel, resolution_exists, semifree_flat,
    fun f g => ⟨coproductIsColimit f g⟩, augmentationComparisons, resolutionComparisons,
    moduleComputations, affineDiagrams, modelZigzags⟩

end

end DerivedFormalization.Affine.TensorResolutionComparison
