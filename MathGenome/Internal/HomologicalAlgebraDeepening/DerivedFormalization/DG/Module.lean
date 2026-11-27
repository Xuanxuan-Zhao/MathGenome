import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Basic
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Module
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Linear.FunctorCategory

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v w j h

namespace DerivedFormalization

abbrev RightDGModule := @Specs.DerivedFormalization.DG.Module.rightDGModule

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

/-- Modules over any dg algebra use the same strict category via its one-object model. -/
abbrev RightDGAlgebraModule (B : DGAlgebra.{u,v} k) := RightDGModule B.toDGCategory

namespace RightDGModule

abbrev Hom (M N : RightDGModule A) := RightDGModuleHomModel M N
abbrev eval (a : A.Obj) := RightDGModuleModel.eval (A := A) a
abbrev degree (a : A.Obj) (n : ℤ) := RightDGModuleModel.degree (A := A) a n

abbrev Acyclic (M : RightDGModule A) := Specs.DerivedFormalization.DG.Module.acyclic M
abbrev IsQuasiIso {M N : RightDGModule A} (f : M ⟶ N) :=
  Specs.DerivedFormalization.DG.Module.quasiIsomorphism f
abbrev DegreewiseSurjective {M N : RightDGModule A} (f : M ⟶ N) :=
  Specs.DerivedFormalization.DG.Module.degreewiseSurjective f

/-- Evaluate a module over the one-object category at its unique object. -/
def oneObjectEquiv (B : DGAlgebra.{u,v} k) :
    RightDGAlgebraModule B ≃ RightDGAlgebraModuleModel B where
  toFun M := ⟨M.complex (), M.act (a := ()) (b := ()), M.act_id (),
    M.act_assoc (a := ()) (b := ()) (c := ()), M.leibniz (a := ()) (b := ())⟩
  invFun N :=
    { complex := fun _ => N.complex
      act := by rintro ⟨⟩ ⟨⟩; exact N.act
      act_id := by rintro ⟨⟩; exact N.act_id
      act_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩; exact N.act_assoc
      leibniz := by rintro ⟨⟩ ⟨⟩; exact N.leibniz }
  left_inv M := by
    cases M with
    | mk complex act act_id act_assoc leibniz =>
      have e : (fun _ : Unit => complex ()) = complex := by funext a; cases a; rfl
      cases e
      congr
  right_inv N := by cases N; rfl

theorem oneObject : Specs.DerivedFormalization.DG.Module.OneObject.{u,v} := by
  intro k _ B
  exact ⟨oneObjectEquiv B, fun _ => ⟨rfl, HEq.rfl⟩⟩

/-- Evaluate at the sole object of any one-object dg category. -/
def equivAtUniqueObject (a : A.Obj) (unique : ∀ b : A.Obj, b = a) :
    RightDGModule A ≃ RightDGAlgebraModuleModel (A.endAlgebra a) where
  toFun M := ⟨M.complex a, M.act (a := a) (b := a), M.act_id a,
    M.act_assoc (a := a) (b := a) (c := a), M.leibniz (a := a) (b := a)⟩
  invFun N :=
    { complex := fun _ => N.complex
      act := by
        intro b c
        have hb := unique b
        subst b
        have hc := unique c
        subst c
        exact N.act
      act_id := by
        intro b
        have hb := unique b
        subst b
        exact N.act_id
      act_assoc := by
        intro b c d
        have hb := unique b
        subst b
        have hc := unique c
        subst c
        have hd := unique d
        subst d
        exact N.act_assoc
      leibniz := by
        intro b c
        have hb := unique b
        subst b
        have hc := unique c
        subst c
        exact N.leibniz }
  left_inv M := by
    cases M with
    | mk complex act act_id act_assoc leibniz =>
      have e : (fun _ : A.Obj => complex a) = complex := by
        funext b
        rw [unique b]
      generalize hC : complex a = C at e ⊢
      cases e
      dsimp only
      congr 1
      funext b c
      have hb := unique b
      have hc := unique c
      subst b
      subst c
      rfl
  right_inv N := by
    cases N
    congr

theorem atUniqueObject : Specs.DerivedFormalization.DG.Module.AtUniqueObject.{u,v,w} := by
  intro k _ A a unique
  exact ⟨equivAtUniqueObject a unique, fun _ => ⟨rfl, HEq.rfl⟩⟩

noncomputable section

private def tensorActDegree (M : RightDGModule A) (a b : A.Obj) (n : ℤ) :
    (ModuleCochain.tensor (M.complex b) (A.hom a b)).X n ⟶ (M.complex a).X n :=
  mapBifunctorDesc fun i j h => ModuleCat.ofHom (TensorProduct.lift (M.act i j n h))

/-- The action as a map from the signed tensor complex. -/
def tensorAct (M : RightDGModule A) (a b : A.Obj) :
    ModuleCochain.tensor (M.complex b) (A.hom a b) ⟶ M.complex a where
  f := tensorActDegree M a b
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    apply mapBifunctor.hom_ext
    intro i j hij
    change i + j = n at hij
    unfold tensorActDegree
    rw [← Category.assoc, ι_mapBifunctorDesc, mapBifunctor.d_eq,
      Preadditive.add_comp, Preadditive.comp_add, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
    rw [mapBifunctor.d₁_eq _ _ _ _ (i₁' := i + 1) rfl j (n+1) (by change i+1+j=n+1; omega),
      mapBifunctor.d₂_eq _ _ _ _ i (i₂' := j + 1) rfl (n+1) (by change i+(j+1)=n+1; omega)]
    change _ = ((1 : ℤˣ) • _) ≫ _ + (i.negOnePow • _) ≫ _
    simp only [one_smul, Linear.units_smul_comp, Category.assoc, ι_mapBifunctorDesc]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro f
    exact M.leibniz i j n hij x f

@[simp] theorem tensorAct_tmul (M : RightDGModule A) (a b : A.Obj)
    (i j n : ℤ) (h : i+j = n) (x : (M.complex b).X i) (f : (A.hom a b).X j) :
    (tensorAct M a b).f n (ModuleCochain.tensorInclusion
      (M.complex b) (A.hom a b) i j n h (x ⊗ₜ[k] f)) = M.act i j n h x f := by
  change tensorActDegree M a b n _ = _
  unfold tensorActDegree
  rw [← ModuleCat.comp_apply, ι_mapBifunctorDesc]
  rfl

theorem tensorAction : Specs.DerivedFormalization.DG.Module.TensorAction.{u,v,w} := by
  intro k _ A M a b
  exact ⟨tensorAct M a b, tensorAct_tmul M a b⟩

section Diagrams

variable {J : Type j} [Category.{h} J] (F : J ⥤ RightDGModule A)

private abbrev degreeDiagram (a : A.Obj) (n : ℤ) : J ⥤ ModuleCat.{v} k := F ⋙ degree (A := A) a n

private def differential (a : A.Obj) (i j : ℤ) :
    degreeDiagram F a i ⟶ degreeDiagram F a j where
  app s := ((F.obj s).complex a).d i j
  naturality _ _ f := ((F.map f).app a).comm i j

/-- Right multiplication by a fixed homogeneous arrow is natural in the module. -/
private def multiplication {a b : A.Obj} (i j n : ℤ) (e : i+j = n) :
    (A.hom a b).X j →ₗ[k] (degreeDiagram F b i ⟶ degreeDiagram F a n) where
  toFun f :=
    { app := fun s => ModuleCat.ofHom (((F.obj s).act i j n e).flip f)
      naturality := by
        intro s t g
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => ((F.map g).comm_act i j n e x f).symm }
  map_add' f g := by
    apply NatTrans.ext
    funext s
    exact ModuleCat.hom_ext (map_add ((F.obj s).act i j n e).flip f g)
  map_smul' r f := by
    apply NatTrans.ext
    funext s
    exact ModuleCat.hom_ext (map_smul ((F.obj s).act i j n e).flip r f)

section Transport

variable (T : (J ⥤ ModuleCat.{v} k) ⥤ ModuleCat.{v} k) [T.Additive] [T.Linear k]

private def complexOfDiagram (a : A.Obj) : ModuleCochain.{u,v} k where
  X n := T.obj (degreeDiagram F a n)
  d i j := T.map (differential F a i j)
  shape i j e := by
    rw [show differential F a i j = 0 by
      apply NatTrans.ext
      funext s
      exact ((F.obj s).complex a).shape i j e, T.map_zero]
  d_comp_d' i j l _ _ := by
    rw [← T.map_comp, show differential F a i j ≫ differential F a j l = 0 by
      apply NatTrans.ext
      funext s
      exact ((F.obj s).complex a).d_comp_d i j l, T.map_zero]

/-- Apply a linear functor to the diagram of degree components and its multiplication maps. -/
private def moduleOfDiagram : RightDGModule A where
  complex := complexOfDiagram F T
  act i j n e := ((ModuleCat.homLinearEquiv (R := k) (S := k)).toLinearMap.comp
    ((T.mapLinearMap (R := k)).comp (multiplication F i j n e))).flip
  act_id a i x := by
    change T.map (multiplication F i 0 i (add_zero i) (A.id a)) x = x
    rw [show multiplication F i 0 i (add_zero i) (A.id a) = 𝟙 _ by
      apply NatTrans.ext
      funext s
      exact ModuleCat.hom_ext (LinearMap.ext ((F.obj s).act_id a i)), T.map_id]
    rfl
  act_assoc := by
    intro a b c i j l x f g
    change (T.map (multiplication F i j (i+j) rfl f) ≫
        T.map (multiplication F (i+j) l (i+j+l) rfl g)) x =
      T.map (multiplication F i (j+l) (i+j+l) (add_assoc i j l).symm
        (A.comp j l (j+l) rfl f g)) x
    rw [← T.map_comp]
    apply congrArg (fun g : T.obj (degreeDiagram F c i) ⟶ T.obj (degreeDiagram F a (i+j+l)) => g x)
    apply congrArg (fun g : degreeDiagram F c i ⟶ degreeDiagram F a (i+j+l) => T.map g)
    apply NatTrans.ext
    funext s
    exact ModuleCat.hom_ext (LinearMap.ext fun y => (F.obj s).act_assoc i j l y f g)
  leibniz := by
    intro a b i j n e x f
    change (T.map (multiplication F i j n e f) ≫ T.map (differential F a n (n+1))) x =
      ((T.map (differential F b i (i+1)) ≫ T.map (multiplication F (i+1) j (n+1) (by omega) f)) +
        i.negOnePow • T.map (multiplication F i (j+1) (n+1) (by omega)
          ((A.hom a b).d j (j+1) f))) x
    rw [← T.map_comp, ← T.map_comp, Units.smul_def, ← T.map_zsmul, ← T.map_add]
    apply congrArg (fun g : T.obj (degreeDiagram F b i) ⟶ T.obj (degreeDiagram F a (n+1)) => g x)
    apply congrArg (fun g : degreeDiagram F b i ⟶ degreeDiagram F a (n+1) => T.map g)
    apply NatTrans.ext
    funext s
    exact ModuleCat.hom_ext (LinearMap.ext fun y => (F.obj s).leibniz i j n e y f)

end Transport

section Colimits

variable [HasColimitsOfShape J (ModuleCat.{v} k)]

local instance (priority := 2000) (D : J ⥤ ModuleCat.{v} k) : HasColimit D :=
  HasColimitsOfShape.has_colimit D

local instance : (colim (J := J) (C := ModuleCat.{v} k)).Additive where
  map_add := by
    intro X Y f g
    apply colimit.hom_ext
    intro s
    change colimit.ι X s ≫ colimMap (f + g) =
      colimit.ι X s ≫ (colimMap f + colimMap g)
    simp only [ι_colimMap, Preadditive.comp_add, Preadditive.add_comp, NatTrans.app_add]

local instance : (colim (J := J) (C := ModuleCat.{v} k)).Linear k where
  map_smul f r := by
    apply colimit.hom_ext
    intro s
    change _ ≫ colimMap (r • f) = _ ≫ (r • colimMap f)
    simp only [ι_colimMap, CategoryTheory.Linear.comp_smul,
      CategoryTheory.Linear.smul_comp, NatTrans.app_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The cocone with pointwise colimit complexes and induced action on the generators. -/
def colimitCocone : Cocone F where
  pt := moduleOfDiagram F (colim (J := J) (C := ModuleCat.{v} k))
  ι :=
    { app := fun s =>
        { app := fun a =>
            { f := fun i => colimit.ι (degreeDiagram F a i) s
              comm' := fun i j _ => ι_colimMap (differential F a i j) s }
          comm_act := by
            intro a b i j n e x f
            exact congrArg
              (fun g : (degreeDiagram F b i).obj s ⟶ colimit (degreeDiagram F a n) => g x)
              (ι_colimMap (multiplication F i j n e f) s).symm }
      naturality := by
        intro s t g
        apply RightDGModuleModel.hom_ext
        intro a
        apply HomologicalComplex.Hom.ext
        funext n
        change (degreeDiagram F a n).map g ≫ colimit.ι (degreeDiagram F a n) t =
          colimit.ι (degreeDiagram F a n) s ≫ 𝟙 _
        rw [Category.comp_id, colimit.w] }

set_option backward.isDefEq.respectTransparency false in
/-- Each degree of the strict colimit has the module colimit universal property. -/
def colimitCoconeIsColimitDegree (a : A.Obj) (i : ℤ) :
    IsColimit ((degree (A := A) a i).mapCocone (colimitCocone F)) := by
  apply IsColimit.ofIsoColimit (colimit.isColimit (degreeDiagram F a i))
  exact Cocone.ext (Iso.refl (colimit (degreeDiagram F a i)))

/-- Evaluation at an object takes the strict colimit cocone to a complex colimit. -/
def colimitCoconeIsColimitEval (a : A.Obj) :
    IsColimit ((eval (A := A) a).mapCocone (colimitCocone F)) :=
  HomologicalComplex.isColimitOfEval _ _ (colimitCoconeIsColimitDegree F a)

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise colimit and its induced action give a strict colimit of dg modules. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc t :=
    { app := fun a => (colimitCoconeIsColimitEval F a).desc ((eval a).mapCocone t)
      comm_act := by
        intro a b i j n e x f
        let descend (a : A.Obj) : (colimitCocone F).pt.complex a ⟶ t.pt.complex a :=
          (colimitCoconeIsColimitEval F a).desc ((eval a).mapCocone t)
        have fac (s : J) (a : A.Obj) (m : ℤ) (y : ((F.obj s).complex a).X m) :
            (descend a).f m ((((colimitCocone F).ι.app s).app a).f m y) =
              ((t.ι.app s).app a).f m y :=
          congrArg (fun g : (F.obj s).complex a ⟶ t.pt.complex a => g.f m y)
            ((colimitCoconeIsColimitEval F a).fac ((eval a).mapCocone t) s)
        have eq : ModuleCat.ofHom (((colimitCocone F).pt.act i j n e).flip f) ≫ (descend a).f n =
            (descend b).f i ≫ ModuleCat.ofHom ((t.pt.act i j n e).flip f) := by
          apply (colimitCoconeIsColimitDegree F b i).hom_ext
          intro s
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro (y : ((F.obj s).complex b).X i)
          change (descend a).f n ((colimitCocone F).pt.act i j n e
            ((((colimitCocone F).ι.app s).app b).f i y) f) =
              t.pt.act i j n e ((descend b).f i ((((colimitCocone F).ι.app s).app b).f i y)) f
          have h := ((colimitCocone F).ι.app s).comm_act (a := a) (b := b) i j n e y f
          change (((colimitCocone F).ι.app s).app a).f n ((F.obj s).act i j n e y f) =
            (colimitCocone F).pt.act i j n e ((((colimitCocone F).ι.app s).app b).f i y) f at h
          rw [← h, fac, fac]
          exact (t.ι.app s).comm_act i j n e y f
        exact congrArg (fun g : ((colimitCocone F).pt.complex b).X i ⟶ (t.pt.complex a).X n => g x) eq }
  fac t s := RightDGModuleModel.hom_ext fun a =>
    (colimitCoconeIsColimitEval F a).fac ((eval a).mapCocone t) s
  uniq t m hm := RightDGModuleModel.hom_ext fun a =>
    (colimitCoconeIsColimitEval F a).uniq ((eval a).mapCocone t) (m.app a) fun s =>
      congrArg (fun g : F.obj s ⟶ t.pt => g.app a) (hm s)

instance hasColimitsOfShape : HasColimitsOfShape J (RightDGModule A) where
  has_colimit F := ⟨⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩

instance eval_preservesColimitsOfShape (a : A.Obj) :
    PreservesColimitsOfShape J (eval (A := A) a) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (colimitCoconeIsColimit F) (colimitCoconeIsColimitEval F a)

instance degree_preservesColimitsOfShape (a : A.Obj) (i : ℤ) :
    PreservesColimitsOfShape J (degree (A := A) a i) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (colimitCoconeIsColimit F) (colimitCoconeIsColimitDegree F a i)

end Colimits

section Limits

variable [HasLimitsOfShape J (ModuleCat.{v} k)]

local instance : (lim (J := J) (C := ModuleCat.{v} k)).Additive where
  map_add := by
    intro X Y f g
    apply limit.hom_ext
    intro s
    change limMap (f + g) ≫ limit.π Y s =
      (limMap f + limMap g) ≫ limit.π Y s
    simp only [limMap_π, Preadditive.comp_add, Preadditive.add_comp, NatTrans.app_add]

local instance : (lim (J := J) (C := ModuleCat.{v} k)).Linear k where
  map_smul f r := by
    apply limit.hom_ext
    intro s
    change limMap (r • f) ≫ _ = (r • limMap f) ≫ _
    simp only [limMap_π, CategoryTheory.Linear.comp_smul,
      CategoryTheory.Linear.smul_comp, NatTrans.app_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The cone with pointwise limit complexes and action on each component. -/
def limitCone : Cone F where
  pt := moduleOfDiagram F (lim (J := J) (C := ModuleCat.{v} k))
  π :=
    { app := fun s =>
        { app := fun a =>
            { f := fun i => limit.π (degreeDiagram F a i) s
              comm' := fun i j _ => (limMap_π (differential F a i j) s).symm }
          comm_act := by
            intro a b i j n e x f
            exact congrArg (fun g : _ ⟶ (degreeDiagram F a n).obj s => g x)
              (limMap_π (multiplication F i j n e f) s) }
      naturality := by
        intro s t g
        apply RightDGModuleModel.hom_ext
        intro a
        apply HomologicalComplex.Hom.ext
        funext n
        change 𝟙 _ ≫ limit.π (degreeDiagram F a n) t =
          limit.π (degreeDiagram F a n) s ≫ (degreeDiagram F a n).map g
        rw [Category.id_comp, limit.w] }

/-- Each degree of the strict limit has the module limit universal property. -/
def limitConeIsLimitDegree (a : A.Obj) (i : ℤ) :
    IsLimit ((degree (A := A) a i).mapCone (limitCone F)) :=
  limit.isLimit (degreeDiagram F a i)

/-- Evaluation at an object takes the strict limit cone to a complex limit. -/
def limitConeIsLimitEval (a : A.Obj) :
    IsLimit ((eval (A := A) a).mapCone (limitCone F)) :=
  HomologicalComplex.isLimitOfEval _ _ (limitConeIsLimitDegree F a)

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise limit and its componentwise action give a strict limit of dg modules. -/
def limitConeIsLimit : IsLimit (limitCone F) where
  lift t :=
    { app := fun a => (limitConeIsLimitEval F a).lift ((eval a).mapCone t)
      comm_act := by
        intro a b i j n e x f
        let lift (a : A.Obj) : t.pt.complex a ⟶ (limitCone F).pt.complex a := (limitConeIsLimitEval F a).lift ((eval a).mapCone t)
        have fac (s : J) (a : A.Obj) (m : ℤ) (y : (t.pt.complex a).X m) :
            (((limitCone F).π.app s).app a).f m ((lift a).f m y) = ((t.π.app s).app a).f m y :=
          congrArg (fun g : t.pt.complex a ⟶ (F.obj s).complex a => g.f m y)
            ((limitConeIsLimitEval F a).fac ((eval a).mapCone t) s)
        have eq : ModuleCat.ofHom ((t.pt.act i j n e).flip f) ≫ (lift a).f n =
            (lift b).f i ≫ ModuleCat.ofHom (((limitCone F).pt.act i j n e).flip f) := by
          apply (limitConeIsLimitDegree F a n).hom_ext
          intro s
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro y
          change (((limitCone F).π.app s).app a).f n ((lift a).f n (t.pt.act i j n e y f)) =
            (((limitCone F).π.app s).app a).f n ((limitCone F).pt.act i j n e ((lift b).f i y) f)
          have h := ((limitCone F).π.app s).comm_act (a := a) (b := b) i j n e ((lift b).f i y) f
          change (((limitCone F).π.app s).app a).f n
            ((limitCone F).pt.act i j n e ((lift b).f i y) f) = _ at h
          rw [h, fac, fac]
          exact (t.π.app s).comm_act i j n e y f
        exact congrArg (fun g : (t.pt.complex b).X i ⟶ ((limitCone F).pt.complex a).X n => g x) eq }
  fac t s := RightDGModuleModel.hom_ext fun a =>
    (limitConeIsLimitEval F a).fac ((eval a).mapCone t) s
  uniq t m hm := RightDGModuleModel.hom_ext fun a =>
    (limitConeIsLimitEval F a).uniq ((eval a).mapCone t) (m.app a) fun s =>
      congrArg (fun g : t.pt ⟶ F.obj s => g.app a) (hm s)

instance hasLimitsOfShape : HasLimitsOfShape J (RightDGModule A) where
  has_limit F := ⟨⟨limitCone F, limitConeIsLimit F⟩⟩

instance eval_preservesLimitsOfShape (a : A.Obj) :
    PreservesLimitsOfShape J (eval (A := A) a) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone
    (limitConeIsLimit F) (limitConeIsLimitEval F a)

instance degree_preservesLimitsOfShape (a : A.Obj) (i : ℤ) :
    PreservesLimitsOfShape J (degree (A := A) a i) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone
    (limitConeIsLimit F) (limitConeIsLimitDegree F a i)

end Limits

end Diagrams

theorem pointwiseLimits : Specs.DerivedFormalization.DG.Module.PointwiseLimits.{u,v,w,j,h} := by
  intro k _ A J _ _ F
  exact ⟨limitCone F, ⟨limitConeIsLimit F⟩, fun a => ⟨limitConeIsLimitEval F a⟩,
    fun a i => ⟨limitConeIsLimitDegree F a i⟩⟩

theorem pointwiseColimits : Specs.DerivedFormalization.DG.Module.PointwiseColimits.{u,v,w,j,h} := by
  intro k _ A J _ _ F
  exact ⟨colimitCocone F, ⟨colimitCoconeIsColimit F⟩, fun a => ⟨colimitCoconeIsColimitEval F a⟩,
    fun a i => ⟨colimitCoconeIsColimitDegree F a i⟩⟩

/-- The strict kernel is computed objectwise, with the usual inclusions of linear kernels. -/
theorem pointwiseKernels : Specs.DerivedFormalization.DG.Module.PointwiseKernels.{u,v,w} := by
  intro k _ A M N f
  let c : KernelFork f := KernelFork.ofι (kernel.ι f) (kernel.condition f)
  have hc : IsLimit c := kernelIsKernel f
  refine ⟨c, ⟨hc⟩, fun a => ⟨KernelFork.mapIsLimit c hc (eval a)⟩, ?_⟩
  intro a n
  let G := degree (A := A) a n
  let hd := KernelFork.mapIsLimit c hc G
  let he := ModuleCat.kernelIsLimit ((f.app a).f n)
  exact ⟨IsLimit.conePointUniqueUpToIso hd he,
    IsLimit.conePointUniqueUpToIso_hom_comp hd he WalkingParallelPair.zero⟩

/-- The strict cokernel is computed objectwise, with the usual quotient maps. -/
theorem pointwiseCokernels : Specs.DerivedFormalization.DG.Module.PointwiseCokernels.{u,v,w} := by
  intro k _ A M N f
  let c : CokernelCofork f := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)
  have hc : IsColimit c := cokernelIsCokernel f
  refine ⟨c, ⟨hc⟩, fun a => ⟨CokernelCofork.mapIsColimit c hc (eval a)⟩, ?_⟩
  intro a n
  let G := degree (A := A) a n
  let hd := CokernelCofork.mapIsColimit c hc G
  let he := ModuleCat.cokernelIsColimit ((f.app a).f n)
  exact ⟨IsColimit.coconePointUniqueUpToIso hd he,
    IsColimit.comp_coconePointUniqueUpToIso_hom hd he WalkingParallelPair.one⟩

theorem strictSums : Specs.DerivedFormalization.DG.Module.StrictSums.{u,v,w} := by
  intro k _ A I M
  exact pointwiseColimits (Discrete.functor M)

theorem sequentialColimits : Specs.DerivedFormalization.DG.Module.SequentialColimits.{u,v,w} := by
  intro k _ A M step
  exact pointwiseColimits (Functor.ofSequence step)

end

end RightDGModule

end DerivedFormalization
