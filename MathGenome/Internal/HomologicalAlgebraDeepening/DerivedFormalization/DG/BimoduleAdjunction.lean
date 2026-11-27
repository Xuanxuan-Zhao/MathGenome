import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BalancedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Yoneda
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLiftComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BimoduleAdjunction

open CategoryTheory CochainComplex.HomComplex

universe u v w z

namespace DerivedFormalization.DGBimodule

open RightDGModule (GradedHom homComplex dgCategory)
open Specs.DerivedFormalization.DG.BalancedTensor (Degree tmul left RightModule)
open Specs.DerivedFormalization.DG.HomComplex (ofStrict)

noncomputable section

set_option maxHeartbeats 800000


variable {k : Type u} [CommRing k]
variable {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
variable (T : DGBimodule A B)
variable {M M' : RightDGModule A} {N N' : RightDGModule B} {r : ℤ}

private abbrev tensor (T : DGBimodule A B) (M : RightDGModule A) : RightDGModule B :=
  RightModule.toOrdinary.obj (mixedTensorModule T M)

private abbrev internalHom (T : DGBimodule A B) (N : RightDGModule B) : RightDGModule A :=
  RightModule.toOrdinary.obj (mixedHomModule T N)

private theorem graded_ext {C : DGCategory k} {X Y : RightDGModule C}
    {s : ℤ} {f g : GradedHom X Y s}
    (h : ∀ a i q (e : i+s=q) (x : (X.complex a).X i), f.app a i q e x = g.app a i q e x) :
    f = g := by
  apply GradedHom.ext
  intro a i q e
  exact ModuleCat.hom_ext (LinearMap.ext (h a i q e))

private theorem app_add {C : DGCategory k} {X Y : RightDGModule C} {s : ℤ}
    (f g : GradedHom X Y s) (a : C.Obj) (i q : ℤ) (e : i+s=q) (x : (X.complex a).X i) :
    (f + g).app a i q e x = f.app a i q e x + g.app a i q e x := rfl

private theorem app_sub {C : DGCategory k} {X Y : RightDGModule C} {s : ℤ}
    (f g : GradedHom X Y s) (a : C.Obj) (i q : ℤ) (e : i+s=q) (x : (X.complex a).X i) :
    (f - g).app a i q e x = f.app a i q e x - g.app a i q e x := rfl

/-- Currying evaluated at one homogeneous element of the source module. -/
private def curryValue (f : GradedHom (tensor.{u,v,w,z} T M) N r) (a : A.Obj)
    (i s : ℤ) (e : i+r=s) (m : (M.complex a).X i) : GradedHom (T.obj a) N s :=
  GradedHom.mk (fun b j q h => ModuleCat.ofHom
    ((f.app b (i+j) q (by omega)).hom.comp (tensorPair T M b a i j (i+j) rfl m))) (by
      intro b c j p n js ns h hj hn t u
      change f.app b (i+n) ns _ (tmul T M b a i n (i+n) rfl m ((T.obj a).act j p n h t u)) =
        N.act js p ns _ (f.app c (i+j) js _ (tmul T M c a i j (i+j) rfl m t)) u
      rw [← tensorModule_act_tmul.{u,v,w,z} T M a i j (i+j) p n (i+n) rfl (by omega) h m t u]
      exact f.comm_act (i+j) p (i+n) js ns (by omega) (by omega) (by omega) _ u)

private theorem curryValue_apply (f : GradedHom (tensor.{u,v,w,z} T M) N r) (a : A.Obj)
    (b : B.Obj) (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    (curryValue.{u,v,w,z} T f a i s e m).app b j q eq t =
      f.app b n q (by omega) (tmul T M b a i j n h m t) := by
  subst n
  rfl

private def curryValueLinear (f : GradedHom (tensor.{u,v,w,z} T M) N r) (a : A.Obj)
    (i s : ℤ) (e : i+r=s) : (M.complex a).X i →ₗ[k] GradedHom (T.obj a) N s where
  toFun := curryValue.{u,v,w,z} T f a i s e
  map_add' m m' := by
    apply graded_ext
    intro b j q h t
    rw [app_add]
    simp only [curryValue_apply.{u,v,w,z} T f a b i j (i+j) s q rfl e h,
      ← tensorPair_apply, map_add, LinearMap.add_apply]
  map_smul' c m := by
    apply graded_ext
    intro b j q h t
    change (curryValue.{u,v,w,z} T f a i s e (c • m)).app b j q h t =
      (c • (curryValue.{u,v,w,z} T f a i s e m).val b).v j q h t
    simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]
    simp only [curryValue_apply.{u,v,w,z} T f a b i j (i+j) s q rfl e h,
      ← tensorPair_apply, map_smul, LinearMap.smul_apply]

/-- The degreewise forward correspondence is obtained by evaluating on pure tensors. -/
def curry (f : GradedHom (tensor.{u,v,w,z} T M) N r) : GradedHom M (internalHom.{u,v,w,z} T N) r :=
  GradedHom.mk (fun a i s e => ModuleCat.ofHom (curryValueLinear.{u,v,w,z} T f a i s e)) (by
    intro a a' i l n ir nr h hi hn m u
    apply graded_ext
    intro b j q e t
    change (curryValue.{u,v,w,z} T f a n nr hn (M.act i l n h m u)).app b j q e t =
      GradedHom.app ((internalHom.{u,v,w,z} T N).act ir l nr (by omega) (curryValue.{u,v,w,z} T f a' i ir hi m) u) b j q e t
    change _ = GradedHom.app ((dgCategory B).comp ir l nr _
        (curryValue.{u,v,w,z} T f a' i ir hi m) ((T.map a a').f l u)) b j q e t
    rw [RightDGModule.compositionFormula ir l nr _ _ _ b j (l+j) q (by omega)
      (by omega), curryValue_apply.{u,v,w,z} T f a b n j (n+j) nr q rfl hn e,
      curryValue_apply.{u,v,w,z} T f a' b i (l+j) (n+j) ir q (by omega) hi (by omega)]
    exact congrArg (f.app b (n+j) q (by omega))
      (tmul_balance T M b i l j n (l+j) (n+j) h rfl rfl m u t))

theorem curry_apply (f : GradedHom (tensor.{u,v,w,z} T M) N r) (a : A.Obj) (b : B.Obj)
    (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    GradedHom.app ((curry.{u,v,w,z} T f).app a i s e m) b j q eq t =
      f.app b n q (by omega) (tmul T M b a i j n h m t) :=
  curryValue_apply.{u,v,w,z} T f a b i j n s q h e eq m t

private theorem curry_ext {f g : GradedHom M (internalHom.{u,v,w,z} T N) r}
    (h : ∀ (a : A.Obj) (b : B.Obj) (i j s q : ℤ) (e : i+r=s) (eq : j+s=q)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j),
      GradedHom.app (f.app a i s e m) b j q eq t =
        GradedHom.app (g.app a i s e m) b j q eq t) : f = g := by
  apply graded_ext
  intro a i s e m
  apply graded_ext
  intro b j q eq t
  exact h a b i j s q e eq m t

private def uncurryPair (g : GradedHom M (internalHom.{u,v,w,z} T N) r) (b : B.Obj) (a : A.Obj)
    (i j q : ℤ) (h : i+j+r=q) :
    (M.complex a).X i →ₗ[k] ((T.obj a).complex b).X j →ₗ[k] (N.complex b).X q where
  toFun m := (GradedHom.app (g.app a i (i+r) rfl m) b j q (by omega)).hom
  map_add' m m' := by
    ext t
    change GradedHom.app (g.app a i (i+r) rfl (m + m')) b j q (by omega) t = _
    rw [map_add]
    rfl
  map_smul' c m := by
    ext t
    simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply]
    change (c • (g.app a i (i+r) rfl m).val b).v j q (by omega) t = _
    simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]

private def uncurryComponent (g : GradedHom M (internalHom.{u,v,w,z} T N) r)
    (b : B.Obj) (n q : ℤ) (e : n+r=q) : Degree T M b n →ₗ[k] (N.complex b).X q :=
  lift T M (fun a i j h => uncurryPair.{u,v,w,z} T g b a i j q (by omega)) (by
    intro a a' i l j h m u t
    have hr := g.comm_act i l (i+l) (i+r) (i+l+r) rfl rfl rfl m u
    change (g.app a (i+l) (i+l+r) rfl (M.act i l (i+l) rfl m u)) =
      (internalHom.{u,v,w,z} T N).act (i+r) l (i+l+r) _ (g.app a' i (i+r) rfl m) u at hr
    change GradedHom.app (g.app a (i+l) (i+l+r) rfl (M.act i l (i+l) rfl m u)) b j q _ t =
      GradedHom.app (g.app a' i (i+r) rfl m) b (l+j) q _ (left T b l j (l+j) rfl u t)
    rw [hr]
    change GradedHom.app ((dgCategory B).comp (i+r) l (i+l+r) _
       (g.app a' i (i+r) rfl m) ((T.map a a').f l u)) b j q _ t = _
    exact RightDGModule.compositionFormula (i+r) l (i+l+r) _ _ _ b j (l+j) q
      (by omega) (by omega) t)

private theorem uncurryComponent_tmul (g : GradedHom M (internalHom.{u,v,w,z} T N) r) (b : B.Obj) (a : A.Obj)
    (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    uncurryComponent.{u,v,w,z} T g b n q (by omega) (tmul T M b a i j n h m t) =
      GradedHom.app (g.app a i s e m) b j q eq t := by
  subst s
  exact lift_tmul T M _ _ a i j h m t

/-- A curried map descends to the balanced quotient. -/
def uncurry (g : GradedHom M (internalHom.{u,v,w,z} T N) r) : GradedHom (tensor.{u,v,w,z} T M) N r :=
  GradedHom.mk (fun b n q e => ModuleCat.ofHom (uncurryComponent.{u,v,w,z} T g b n q e)) (by
    intro b c n p np nr npr e en enp x u
    refine LinearMap.congr_fun (f := (uncurryComponent.{u,v,w,z} T g b np npr enp).comp
      (((tensor.{u,v,w,z} T M).act n p np e).flip u)) (g := ((N.act nr p npr _).flip u).comp
        (uncurryComponent.{u,v,w,z} T g c n nr en)) (linearMap_ext T M ?_) x
    intro a i j h m t
    change uncurryComponent.{u,v,w,z} T g b np npr enp
      ((tensor.{u,v,w,z} T M).act n p np e (tmul T M c a i j n h m t) u) =
      N.act nr p npr _ (uncurryComponent.{u,v,w,z} T g c n nr en (tmul T M c a i j n h m t)) u
    change uncurryComponent.{u,v,w,z} T g b np npr enp ((mixedTensorModule T M).act n p np e (tmul T M c a i j n h m t) u) = _
    rw [mixedTensorModule_act_tmul T M a i j n p (j+p) np h e rfl,
      uncurryComponent_tmul.{u,v,w,z} T g b a i (j+p) np (i+r) npr (by omega) rfl (by omega),
      uncurryComponent_tmul.{u,v,w,z} T g c a i j n (i+r) nr h rfl (by omega)]
    exact GradedHom.comm_act (g.app a i (i+r) rfl m : GradedHom (T.obj a) N (i+r))
      j p (j+p) nr npr rfl (by omega) (by omega) t u)

theorem uncurry_apply (g : GradedHom M (internalHom.{u,v,w,z} T N) r) (b : B.Obj) (a : A.Obj)
    (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    (uncurry.{u,v,w,z} T g).app b n q (by omega) (tmul T M b a i j n h m t) =
      GradedHom.app (g.app a i s e m) b j q eq t :=
  uncurryComponent_tmul.{u,v,w,z} T g b a i j n s q h e eq m t

set_option linter.unusedVariables false in
private theorem tensor_graded_ext {f g : GradedHom (tensor.{u,v,w,z} T M) N r}
    (h : ∀ (b : B.Obj) (a : A.Obj) (i j n q : ℤ) (e : i+j=n) (eq : n+r=q)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j),
      f.app b n q eq (tmul T M b a i j n e m t) =
        g.app b n q eq (tmul T M b a i j n e m t)) : f = g := by
  apply GradedHom.ext
  intro b n q eq
  apply ModuleCat.hom_ext
  exact linearMap_ext T M (fun a i j e => h b a i j n q e eq)

/-- Currying and evaluation give inverse linear maps in every homogeneous degree. -/
def curryEquiv (M : RightDGModule A) (N : RightDGModule B) (r : ℤ) :
    GradedHom (tensor.{u,v,w,z} T M) N r ≃ₗ[k] GradedHom M (internalHom.{u,v,w,z} T N) r where
  toFun := curry.{u,v,w,z} T
  invFun := uncurry.{u,v,w,z} T
  left_inv f := by
    apply tensor_graded_ext.{u,v,w,z} T
    intro b a i j n q e eq m t
    rw [uncurry_apply.{u,v,w,z} T _ b a i j n (i+r) q e rfl (by omega),
      curry_apply.{u,v,w,z} T f a b i j n (i+r) q e rfl (by omega)]
  right_inv g := by
    apply curry_ext.{u,v,w,z} T
    intro a b i j s q e eq m t
    rw [curry_apply.{u,v,w,z} T _ a b i j (i+j) s q rfl e eq,
      uncurry_apply.{u,v,w,z} T g b a i j (i+j) s q rfl e eq]
  map_add' f g := by
    apply curry_ext.{u,v,w,z} T
    intro a b i j s q e eq m t
    rw [app_add, app_add]
    simp only [curry_apply.{u,v,w,z} T _ a b i j (i+j) s q rfl e eq]
    rfl
  map_smul' c f := by
    apply curry_ext.{u,v,w,z} T
    intro a b i j s q e eq m t
    change GradedHom.app ((curry.{u,v,w,z} T (c • f)).app a i s e m) b j q eq t =
      GradedHom.app (c • (curry.{u,v,w,z} T f).app a i s e m) b j q eq t
    change _ = c • GradedHom.app ((curry.{u,v,w,z} T f).app a i s e m) b j q eq t
    rw [curry_apply.{u,v,w,z} T _ a b i j (i+j) s q rfl e eq,
      curry_apply.{u,v,w,z} T f a b i j (i+j) s q rfl e eq]
    rfl


private theorem app_smul {C : DGCategory k} {X Y : RightDGModule C} {s : ℤ}
    (c : ℤˣ) (f : GradedHom X Y s) (a : C.Obj) (i q : ℤ)
    (e : i+s=q) (x : (X.complex a).X i) :
    (c • f).app a i q e x = c • f.app a i q e x := by
  change ((c • (f.val a)).v i q e) x = _
  rw [Cochain.units_smul_v]
  rfl

private theorem differential_at {C : DGCategory k} {X Y : RightDGModule C} (f : GradedHom X Y r)
    (a : C.Obj) (i p q : ℤ) (h : i+r=p) (e : i+(r+1)=q) (x : (X.complex a).X i) :
    GradedHom.app ((homComplex X Y).d r (r+1) f) a i q e x =
      (Y.complex a).d p q (f.app a i p h x) -
        r.negOnePow • f.app a (i+1) q (by omega) ((X.complex a).d i (i+1) x) := by
  subst p
  exact RightDGModule.differentialFormula r f a i q e x

/-- Currying commutes with the signed Hom differential. -/
theorem curry_d (f : GradedHom (tensor.{u,v,w,z} T M) N r) :
    curry.{u,v,w,z} T ((homComplex (tensor.{u,v,w,z} T M) N).d r (r+1) f) =
      (homComplex M (internalHom.{u,v,w,z} T N)).d r (r+1)
        (curry.{u,v,w,z} T f) := by
  apply curry_ext.{u,v,w,z} T
  intro a b i j s q e eq m t
  let n := i+j
  rw [curry_apply.{u,v,w,z} T _ a b i j n s q rfl e eq,
    differential_at f b n (j+(i+r)) q (by dsimp [n]; omega) (by omega),
    mixedTensorComplex_d_tmul T M b a i j n rfl m t,
    RightDGModule.differentialFormula r (curry.{u,v,w,z} T f) a i s e,
    app_sub, app_smul]
  change _ = GradedHom.app
    ((homComplex (T.obj a) N).d (i+r) s ((curry.{u,v,w,z} T f).app a i (i+r) rfl m))
      b j q eq t - r.negOnePow • _
  have hs : s = (i+r)+1 := by omega
  subst hs
  rw [RightDGModule.differentialFormula (i+r) _ b j q (by omega)]
  rw [curry_apply.{u,v,w,z} T f a b i j n (i+r) (j+(i+r)) rfl rfl rfl,
    curry_apply.{u,v,w,z} T f a b i (j+1) (n+1) (i+r) q (by dsimp [n]; omega) rfl (by omega),
    curry_apply.{u,v,w,z} T f a b (i+1) j (n+1) ((i+r)+1) q
      (by dsimp [n]; omega) (by omega) (by omega)]
  simp only [map_add, Units.smul_def, map_zsmul,
    smul_add, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [mul_comm (r.negOnePow : ℤ) (i.negOnePow : ℤ)]
  abel

/-- The signed tensor–Hom adjunction at the level of complexes. -/
def curryIso (M : RightDGModule A) (N : RightDGModule B) :
    homComplex (tensor.{u,v,w,z} T M) N ≅
      homComplex M (internalHom.{u,v,w,z} T N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => (curryEquiv.{u,v,w,z} T M N r).toModuleIso) (by
      intro r s h
      change r+1=s at h
      subst s
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact fun f => (curry_d.{u,v,w,z} T f).symm)

private theorem module_hom_ext {C : DGCategory k} {X Y : RightDGModule C} {f g : X ⟶ Y}
    (h : ∀ a i (x : (X.complex a).X i), (f.app a).f i x = (g.app a).f i x) : f = g :=
  RightDGModuleModel.hom_ext fun a => HomologicalComplex.hom_ext _ _
    fun i => ModuleCat.hom_ext (LinearMap.ext (h a i))

private theorem strict_app {C : DGCategory k} {X Y : RightDGModule C} (f : X ⟶ Y)
    (a : C.Obj) (i : ℤ) (x : (X.complex a).X i) :
    GradedHom.app (ofStrict f) a i i (add_zero i) x = (f.app a).f i x := by
  change (Cochain.ofHom (f.app a)).v i i (add_zero i) x = _
  rw [Cochain.ofHom_v]

open RightDGModule (strictMap strictCycle)

private abbrev curriedCycle (f : tensor.{u,v,w,z} T M ⟶ N) :
    Specs.DerivedFormalization.DG.Basic.cyclesZero
      (homComplex M (internalHom.{u,v,w,z} T N)) :=
  ⟨curry.{u,v,w,z} T (ofStrict f), by
    change (homComplex M (internalHom.{u,v,w,z} T N)).d 0 1 (curry.{u,v,w,z} T (ofStrict f)) = 0
    rw [← curry_d.{u,v,w,z} T]
    have hf := (strictCycle f).property
    change (homComplex (tensor.{u,v,w,z} T M) N).d 0 1 (ofStrict f) = 0 at hf
    rw [hf]
    exact (curryEquiv.{u,v,w,z} T M N 1).map_zero⟩

private abbrev uncurriedCycle (g : M ⟶ internalHom.{u,v,w,z} T N) :
    Specs.DerivedFormalization.DG.Basic.cyclesZero
      (homComplex (tensor.{u,v,w,z} T M) N) :=
  ⟨uncurry.{u,v,w,z} T (ofStrict g), by
    apply (curryEquiv.{u,v,w,z} T M N 1).injective
    change curry.{u,v,w,z} T
      ((homComplex (tensor.{u,v,w,z} T M) N).d 0 1 (uncurry.{u,v,w,z} T (ofStrict g))) =
      (curryEquiv.{u,v,w,z} T M N 1) 0
    rw [curry_d.{u,v,w,z} T, (curryEquiv.{u,v,w,z} T M N 1).map_zero]
    have h := (curryEquiv.{u,v,w,z} T M N 0).apply_symm_apply (ofStrict g)
    change curry.{u,v,w,z} T (uncurry.{u,v,w,z} T (ofStrict g)) = ofStrict g at h
    rw [h]
    exact (strictCycle g).property⟩

/-- The complex isomorphism restricted to closed maps. -/
def strictCurryEquiv (M : RightDGModule A) (N : RightDGModule B) :
    (tensor.{u,v,w,z} T M ⟶ N) ≃ (M ⟶ internalHom.{u,v,w,z} T N) where
  toFun f := strictMap (curriedCycle.{u,v,w,z} T f)
  invFun g := strictMap (uncurriedCycle.{u,v,w,z} T g)
  left_inv f := by
    change strictMap (uncurriedCycle.{u,v,w,z} T (strictMap (curriedCycle.{u,v,w,z} T f))) = f
    rw [← RightDGModule.strictMap_strictCycle f]
    congr 1
    apply Subtype.ext
    have h := congrArg Subtype.val (RightDGModule.strictCycle_strictMap (curriedCycle.{u,v,w,z} T f))
    change ofStrict (strictMap (curriedCycle.{u,v,w,z} T f)) = curry.{u,v,w,z} T (ofStrict f) at h
    change uncurry.{u,v,w,z} T (ofStrict (strictMap (curriedCycle.{u,v,w,z} T f))) = ofStrict f
    rw [h]
    exact (curryEquiv.{u,v,w,z} T M N 0).symm_apply_apply _
  right_inv g := by
    change strictMap (curriedCycle.{u,v,w,z} T (strictMap (uncurriedCycle.{u,v,w,z} T g))) = g
    rw [← RightDGModule.strictMap_strictCycle g]
    congr 1
    apply Subtype.ext
    have h := congrArg Subtype.val (RightDGModule.strictCycle_strictMap (uncurriedCycle.{u,v,w,z} T g))
    change ofStrict (strictMap (uncurriedCycle.{u,v,w,z} T g)) = uncurry.{u,v,w,z} T (ofStrict g) at h
    change curry.{u,v,w,z} T (ofStrict (strictMap (uncurriedCycle.{u,v,w,z} T g))) = ofStrict g
    rw [h]
    exact (curryEquiv.{u,v,w,z} T M N 0).apply_symm_apply _

theorem strictCurryEquiv_apply (f : tensor.{u,v,w,z} T M ⟶ N)
    (a : A.Obj) (b : B.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    GradedHom.app (((strictCurryEquiv.{u,v,w,z} T M N f).app a).f i m)
      b j n (by omega) t = (f.app b).f n (tmul T M b a i j n h m t) := by
  change GradedHom.app ((curry.{u,v,w,z} T (ofStrict f)).app a i i (add_zero i) m)
    b j n (by omega) t = _
  rw [curry_apply.{u,v,w,z} T _ a b i j n i n h (add_zero i) (by omega), strict_app]

theorem strictCurryEquiv_symm_apply (g : M ⟶ internalHom.{u,v,w,z} T N)
    (a : A.Obj) (b : B.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    (((strictCurryEquiv.{u,v,w,z} T M N).symm g).app b).f n (tmul T M b a i j n h m t) =
      GradedHom.app ((g.app a).f i m) b j n (by omega) t := by
  change (uncurry.{u,v,w,z} T (ofStrict g)).app b n n (add_zero n)
    (tmul T M b a i j n h m t) = _
  rw [uncurry_apply.{u,v,w,z} T _ b a i j n i n h (add_zero i) (by omega), strict_app]

private theorem mixedHomMap_component (p : N ⟶ N') (a : A.Obj) (b : B.Obj) (s j q : ℤ)
    (e : j+s=q) (g : GradedHom (T.obj a) N s) (t : ((T.obj a).complex b).X j) :
    GradedHom.app (((mixedHomMap T p).app a).f s g) b j q e t =
      (p.app b).f q (g.app b j q e t) := by
  rw [mixedHomMap_apply, RightDGModule.compositionFormula 0 s s _ _ g b j q q e (add_zero q),
    strict_app]

/-- The ordinary adjunction on strict maps induced by the enriched correspondence. -/
def adjunction : tensorFunctor.{u,v,w,z} T ⊣ homFunctor.{u,max v w z,w,z} T :=
  Adjunction.mkOfHomEquiv
    { homEquiv := strictCurryEquiv.{u,v,w,z} T
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        change X ⟶ internalHom.{u,v,w,z} T Y at g
        apply module_hom_ext
        intro b n x
        change ((strictCurryEquiv.{u,v,w,z} T X' Y).symm (f ≫ g) |>.app b |>.f n) x =
          (((strictCurryEquiv.{u,v,w,z} T X Y).symm g |>.app b |>.f n).hom.comp
            ((mixedTensorMap T f).app b |>.f n).hom) x
        congr 1
        apply linearMap_ext T X'
        intro a i j e m t
        rw [LinearMap.comp_apply]
        change _ = (((strictCurryEquiv.{u,v,w,z} T X Y).symm g).app b).f n
          (((mixedTensorMap T f).app b).f n (tmul T X' b a i j n e m t))
        rw [mixedTensorMap_tmul, strictCurryEquiv_symm_apply.{u,v,w,z},
          strictCurryEquiv_symm_apply.{u,v,w,z}]
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f p
        change tensor.{u,v,w,z} T X ⟶ Y at f
        apply module_hom_ext
        intro a i m
        apply graded_ext
        intro b j n e t
        change GradedHom.app (((strictCurryEquiv.{u,v,w,z} T X Y' (f ≫ p)).app a).f i m)
          b j n e t =
          GradedHom.app (((mixedHomMap T p).app a).f i
            (((strictCurryEquiv.{u,v,w,z} T X Y f).app a).f i m)) b j n e t
        rw [mixedHomMap_component.{u,v,w,z} T p a b i j n e, strictCurryEquiv_apply.{u,v,w,z} T _ a b i j n (by omega),
          strictCurryEquiv_apply.{u,v,w,z} T _ a b i j n (by omega)]
        rfl }

private theorem adjunction_homEquiv :
    (adjunction.{u,v,w,z} T).homEquiv = strictCurryEquiv.{u,v,w,z} T :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- The unit sends an element to tensoring with that element. -/
theorem unit_apply (M : RightDGModule A) (a : A.Obj) (b : B.Obj)
    (i j n : ℤ) (h : i+j=n) (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    GradedHom.app ((((adjunction.{u,v,w,z} T).unit.app M).app a).f i m)
      b j n (by omega) t = tmul T M b a i j n h m t :=
  strictCurryEquiv_apply.{u,v,w,z} T (𝟙 (tensor.{u,v,w,z} T M)) a b i j n h m t

/-- The counit evaluates the first tensor factor on the second. -/
theorem counit_apply (N : RightDGModule B) (a : A.Obj) (b : B.Obj)
    (i j n : ℤ) (h : i+j=n) (g : GradedHom (T.obj a) N i) (t : ((T.obj a).complex b).X j) :
    (((adjunction.{u,v,w,z} T).counit.app N).app b).f n
      (tmul T (internalHom.{u,v,w,z} T N) b a i j n h g t) =
      g.app b j n (by omega) t :=
  strictCurryEquiv_symm_apply.{u,v,w,z} T (𝟙 (internalHom.{u,v,w,z} T N)) a b i j n h g t

end

section Representable

universe vA

variable {k : Type u} [CommRing k]

variable {A' : DGCategory.{u,vA,w} k} {B' : DGCategory.{u,v,z} k}
variable (S : DGBimodule A' B') (a : A'.Obj)

local notation "h" => RightDGModule.representable a

private theorem left_identity (b : B'.Obj) (j : ℤ) (t : ((S.obj a).complex b).X j) :
    left S b 0 j j (zero_add _) (A'.id a) t = t := by
  change GradedHom.app ((S.map a a).f 0 (A'.id a)) b j j (add_zero j) t = t
  rw [S.map_id]
  exact strict_app (𝟙 (S.obj a)) b j t

private theorem left_composition (b : B'.Obj) {c d : A'.Obj}
    (i l j n : ℤ) (e : i+l+j=n) (f : (A'.hom d a).X i) (g : (A'.hom c d).X l)
    (t : ((S.obj c).complex b).X j) :
    left S b (i+l) j n e (A'.comp i l (i+l) rfl f g) t =
      left S b i (l+j) n (by omega) f (left S b l j (l+j) rfl g t) := by
  change GradedHom.app ((S.map c a).f (i+l) (A'.comp i l (i+l) rfl f g)) b j n (by omega) t = _
  rw [S.map_comp]
  exact RightDGModule.compositionFormula i l (i+l) rfl _ _ b j (l+j) n (by omega) (by omega) t

private noncomputable def representableEvaluation (b : B'.Obj) (n : ℤ) :
    Degree S h b n →ₗ[k] ((S.obj a).complex b).X n :=
  lift S h (fun c i j e => {
        toFun := fun f => (GradedHom.app ((S.map c a).f i f) b j n (by omega)).hom
        map_add' := by
          intro f g
          apply LinearMap.ext
          intro t
          simp only [map_add, app_add, LinearMap.add_apply]
        map_smul' := by
          intro c₀ f
          apply LinearMap.ext
          intro t
          simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply]
          rfl })
    (by
      intro c d i l j e f g t
      exact left_composition S a b i l j n e f g t)

private theorem representableEvaluation_tmul (b : B'.Obj) (c : A'.Obj) (i j n : ℤ)
    (e : i+j=n) (f : (A'.hom c a).X i) (t : ((S.obj c).complex b).X j) :
    representableEvaluation S a b n (tmul S h b c i j n e f t) =
      left S b i j n e f t :=
  lift_tmul S h _ _ c i j e f t

/-- The homogeneous evaluation isomorphism on the tensor of a representable. -/
noncomputable def representableEquiv (b : B'.Obj) (n : ℤ) :
    Degree S h b n ≃ₗ[k] ((S.obj a).complex b).X n :=
  LinearEquiv.ofLinearMap (representableEvaluation S a b n)
    (tensorPair S h b a 0 n n (zero_add _) (A'.id a))
    (by
      apply LinearMap.ext
      intro t
      change representableEvaluation S a b n (tmul S h b a 0 n n (zero_add _) (A'.id a) t) = t
      rw [representableEvaluation_tmul, left_identity])
    (by
      apply linearMap_ext S h
      intro c i j e f t
      change tmul S h b a 0 n n (zero_add _) (A'.id a)
        (representableEvaluation S a b n (tmul S h b c i j n e f t)) =
          tmul S h b c i j n e f t
      rw [representableEvaluation_tmul]
      have hh := tmul_balance S h b 0 i j i n n (zero_add i) e e (A'.id a) f t
      change tmul S h b c i j n e (A'.comp 0 i i (zero_add _) (A'.id a) f) t = _ at hh
      rw [A'.toData.id_comp] at hh
      exact hh.symm)

theorem representableEquiv_apply (b : B'.Obj) (c : A'.Obj) (i j n : ℤ)
    (e : i+j=n) (f : (A'.hom c a).X i) (t : ((S.obj c).complex b).X j) :
    representableEquiv S a b n (tmul S h b c i j n e f t) =
      left S b i j n e f t :=
  representableEvaluation_tmul S a b c i j n e f t

theorem representableEquiv_symm_apply (b : B'.Obj) (n : ℤ) (t : ((S.obj a).complex b).X n) :
    (representableEquiv S a b n).symm t = tmul S h b a 0 n n (zero_add _) (A'.id a) t := rfl

theorem representableEquiv_d (b : B'.Obj) (n : ℤ) (x : Degree S h b n) :
    representableEquiv S a b (n+1) ((mixedTensorComplex S h b).d n (n+1) x) =
      ((S.obj a).complex b).d n (n+1) (representableEquiv S a b n x) := by
  refine LinearMap.congr_fun (f := (representableEquiv S a b (n+1)).toLinearMap.comp
    ((mixedTensorComplex S h b).d n (n+1)).hom)
    (g := (((S.obj a).complex b).d n (n+1)).hom.comp (representableEquiv S a b n).toLinearMap)
    (linearMap_ext S h ?_) x
  intro c i j e f t
  change representableEquiv S a b (n+1) ((mixedTensorComplex S h b).d n (n+1) _) =
    ((S.obj a).complex b).d n (n+1) (representableEquiv S a b n _)
  rw [mixedTensorComplex_d_tmul, map_add]
  simp only [Units.smul_def, map_zsmul, representableEquiv_apply]
  exact (left_leibniz S b i j n e f t).symm

theorem representableEquiv_act {b c : B'.Obj} (n l q : ℤ) (e : n+l=q)
    (x : Degree S h c n) (g : (B'.hom b c).X l) :
    representableEquiv S a b q ((mixedTensorModule S h).act n l q e x g) =
      (S.obj a).act n l q e (representableEquiv S a c n x) g := by
  refine LinearMap.congr_fun (f := (representableEquiv S a b q).toLinearMap.comp
    (((mixedTensorModule S h).act n l q e).flip g))
    (g := ((S.obj a).act n l q e).flip g |>.comp (representableEquiv S a c n).toLinearMap)
    (linearMap_ext S h ?_) x
  intro c₀ i j he f t
  change representableEquiv S a b q
      ((mixedTensorModule S h).act n l q e (tmul S h c c₀ i j n he f t) g) =
    (S.obj a).act n l q e (representableEquiv S a c n (tmul S h c c₀ i j n he f t)) g
  rw [mixedTensorModule_act_tmul S h c₀ i j n l (j+l) q he e rfl, representableEquiv_apply,
    representableEquiv_apply]
  exact (left_comm_act S i j l n (j+l) q he rfl e f t g).symm

end Representable

noncomputable section

namespace Mixed

open Specs.DerivedFormalization.DG.BimoduleAdjunction
  (asMixed MixedGradedHom mixedHomComplex mixedHomComplex_d successor_apply successor_at)

variable {k : Type u} [CommRing k]
variable {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
variable (T : DGBimodule A B)
variable {M M' : RightDGModule A} {N N' : RightDGModule B} {r : ℤ}

/-- Currying evaluated at one homogeneous element of the source module. -/
private def curryValue (f : MixedGradedHom (mixedTensorModule T M) (asMixed N) r) (a : A.Obj)
    (i s : ℤ) (e : i+r=s) (m : (M.complex a).X i) : GradedHom (T.obj a) N s :=
  GradedHom.mk (fun b j q h => ModuleCat.ofHom
    ((f.app b (i+j) q (by omega)).comp (tensorPair T M b a i j (i+j) rfl m))) (by
      intro b c j p n js ns h hj hn t u
      change f.app b (i+n) ns _ (tmul T M b a i n (i+n) rfl m ((T.obj a).act j p n h t u)) =
        N.act js p ns _ (f.app c (i+j) js _ (tmul T M c a i j (i+j) rfl m t)) u
      rw [← mixedTensorModule_act_tmul T M a i j (i+j) p n (i+n) rfl (by omega) h m t u]
      exact f.comm_act (i+j) p (i+n) js ns (by omega) (by omega) (by omega) _ u)

private theorem curryValue_apply (f : MixedGradedHom (mixedTensorModule T M) (asMixed N) r) (a : A.Obj)
    (b : B.Obj) (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    (curryValue T f a i s e m).app b j q eq t =
      f.app b n q (by omega) (tmul T M b a i j n h m t) := by
  subst n
  rfl

private def curryValueLinear (f : MixedGradedHom (mixedTensorModule T M) (asMixed N) r) (a : A.Obj)
    (i s : ℤ) (e : i+r=s) : (M.complex a).X i →ₗ[k] GradedHom (T.obj a) N s where
  toFun := curryValue T f a i s e
  map_add' m m' := by
    apply graded_ext
    intro b j q h t
    rw [app_add]
    simp only [curryValue_apply T f a b i j (i+j) s q rfl e h,
      ← tensorPair_apply, map_add, LinearMap.add_apply]
  map_smul' c m := by
    apply graded_ext
    intro b j q h t
    change (curryValue T f a i s e (c • m)).app b j q h t =
      (c • (curryValue T f a i s e m).val b).v j q h t
    simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]
    simp only [curryValue_apply T f a b i j (i+j) s q rfl e h,
      ← tensorPair_apply, map_smul, LinearMap.smul_apply]

/-- The degreewise forward correspondence is obtained by evaluating on pure tensors. -/
def curry (f : MixedGradedHom (mixedTensorModule T M) (asMixed N) r) : MixedGradedHom (asMixed M) (mixedHomModule T N) r :=
  MixedGradedHom.mk (fun a i s e => curryValueLinear T f a i s e) (by
    intro a a' i l n ir nr h hi hn m u
    apply graded_ext
    intro b j q e t
    change (curryValue T f a n nr hn (M.act i l n h m u)).app b j q e t =
      GradedHom.app ((mixedHomModule T N).act ir l nr (by omega) (curryValue T f a' i ir hi m) u) b j q e t
    change _ = GradedHom.app ((dgCategory B).comp ir l nr _
        (curryValue T f a' i ir hi m) ((T.map a a').f l u)) b j q e t
    rw [RightDGModule.compositionFormula ir l nr _ _ _ b j (l+j) q (by omega)
      (by omega), curryValue_apply T f a b n j (n+j) nr q rfl hn e,
      curryValue_apply T f a' b i (l+j) (n+j) ir q (by omega) hi (by omega)]
    exact congrArg (f.app b (n+j) q (by omega))
      (tmul_balance T M b i l j n (l+j) (n+j) h rfl rfl m u t))

theorem curry_apply (f : MixedGradedHom (mixedTensorModule T M) (asMixed N) r) (a : A.Obj) (b : B.Obj)
    (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    GradedHom.app ((curry T f).app a i s e m) b j q eq t =
      f.app b n q (by omega) (tmul T M b a i j n h m t) :=
  by
    rw [curry, MixedGradedHom.mk_app]
    exact curryValue_apply T f a b i j n s q h e eq m t

private theorem curry_ext {f g : MixedGradedHom (asMixed M) (mixedHomModule T N) r}
    (h : ∀ (a : A.Obj) (b : B.Obj) (i j s q : ℤ) (e : i+r=s) (eq : j+s=q)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j),
      GradedHom.app (f.app a i s e m) b j q eq t =
        GradedHom.app (g.app a i s e m) b j q eq t) : f = g := by
  apply MixedGradedHom.ext
  intro a i s e m
  apply graded_ext
  intro b j q eq t
  exact h a b i j s q e eq m t

private def uncurryPair (g : MixedGradedHom (asMixed M) (mixedHomModule T N) r) (b : B.Obj) (a : A.Obj)
    (i j q : ℤ) (h : i+j+r=q) :
    (M.complex a).X i →ₗ[k] ((T.obj a).complex b).X j →ₗ[k] (N.complex b).X q where
  toFun m := (GradedHom.app (g.app a i (i+r) rfl m) b j q (by omega)).hom
  map_add' m m' := by
    ext t
    change GradedHom.app (g.app a i (i+r) rfl (m + m')) b j q (by omega) t = _
    rw [map_add]
    rfl
  map_smul' c m := by
    ext t
    simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply]
    change (c • (g.app a i (i+r) rfl m).val b).v j q (by omega) t = _
    simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]

private def uncurryComponent (g : MixedGradedHom (asMixed M) (mixedHomModule T N) r)
    (b : B.Obj) (n q : ℤ) (e : n+r=q) : Degree T M b n →ₗ[k] (N.complex b).X q :=
  lift T M (fun a i j h => uncurryPair T g b a i j q (by omega)) (by
    intro a a' i l j h m u t
    have hr := g.comm_act i l (i+l) (i+r) (i+l+r) rfl rfl rfl m u
    change (g.app a (i+l) (i+l+r) rfl (M.act i l (i+l) rfl m u)) =
      (mixedHomModule T N).act (i+r) l (i+l+r) _ (g.app a' i (i+r) rfl m) u at hr
    change GradedHom.app (g.app a (i+l) (i+l+r) rfl (M.act i l (i+l) rfl m u)) b j q _ t =
      GradedHom.app (g.app a' i (i+r) rfl m) b (l+j) q _ (left T b l j (l+j) rfl u t)
    rw [hr]
    change GradedHom.app ((dgCategory B).comp (i+r) l (i+l+r) _
       (g.app a' i (i+r) rfl m) ((T.map a a').f l u)) b j q _ t = _
    exact RightDGModule.compositionFormula (i+r) l (i+l+r) _ _ _ b j (l+j) q
      (by omega) (by omega) t)

private theorem uncurryComponent_tmul (g : MixedGradedHom (asMixed M) (mixedHomModule T N) r) (b : B.Obj) (a : A.Obj)
    (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    uncurryComponent T g b n q (by omega) (tmul T M b a i j n h m t) =
      GradedHom.app (g.app a i s e m) b j q eq t := by
  subst s
  exact lift_tmul T M _ _ a i j h m t

/-- A curried map descends to the balanced quotient. -/
def uncurry (g : MixedGradedHom (asMixed M) (mixedHomModule T N) r) : MixedGradedHom (mixedTensorModule T M) (asMixed N) r :=
  MixedGradedHom.mk (fun b n q e => uncurryComponent T g b n q e) (by
    intro b c n p np nr npr e en enp x u
    refine LinearMap.congr_fun (f := (uncurryComponent T g b np npr enp).comp
      (((mixedTensorModule T M).act n p np e).flip u)) (g := ((N.act nr p npr _).flip u).comp
        (uncurryComponent T g c n nr en)) (linearMap_ext T M ?_) x
    intro a i j h m t
    change uncurryComponent T g b np npr enp
      ((mixedTensorModule T M).act n p np e (tmul T M c a i j n h m t) u) =
      N.act nr p npr _ (uncurryComponent T g c n nr en (tmul T M c a i j n h m t)) u
    rw [mixedTensorModule_act_tmul T M a i j n p (j+p) np h e rfl,
      uncurryComponent_tmul T g b a i (j+p) np (i+r) npr (by omega) rfl (by omega),
      uncurryComponent_tmul T g c a i j n (i+r) nr h rfl (by omega)]
    exact GradedHom.comm_act (g.app a i (i+r) rfl m : GradedHom (T.obj a) N (i+r))
      j p (j+p) nr npr rfl (by omega) (by omega) t u)

theorem uncurry_apply (g : MixedGradedHom (asMixed M) (mixedHomModule T N) r) (b : B.Obj) (a : A.Obj)
    (i j n s q : ℤ) (h : i+j=n) (e : i+r=s) (eq : j+s=q)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    (uncurry T g).app b n q (by omega) (tmul T M b a i j n h m t) =
      GradedHom.app (g.app a i s e m) b j q eq t :=
  by
    have hq : q = n+r := by omega
    subst hq
    exact uncurryComponent_tmul T g b a i j n s (n+r) h e eq m t

set_option linter.unusedVariables false in
private theorem tensor_graded_ext {f g : MixedGradedHom (mixedTensorModule T M) (asMixed N) r}
    (h : ∀ (b : B.Obj) (a : A.Obj) (i j n q : ℤ) (e : i+j=n) (eq : n+r=q)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j),
      f.app b n q eq (tmul T M b a i j n e m t) =
        g.app b n q eq (tmul T M b a i j n e m t)) : f = g := by
  apply MixedGradedHom.ext
  intro b n q eq x
  exact LinearMap.congr_fun (linearMap_ext T M (fun a i j e => h b a i j n q e eq)) x

/-- Currying and evaluation give inverse linear maps in every homogeneous degree. -/
def curryEquiv (M : RightDGModule A) (N : RightDGModule B) (r : ℤ) :
    MixedGradedHom (mixedTensorModule T M) (asMixed N) r ≃ₗ[k] MixedGradedHom (asMixed M) (mixedHomModule T N) r where
  toFun := curry T
  invFun := uncurry T
  left_inv f := by
    apply tensor_graded_ext T
    intro b a i j n q e eq m t
    rw [uncurry_apply T _ b a i j n (i+r) q e rfl (by omega),
      curry_apply T f a b i j n (i+r) q e rfl (by omega)]
  right_inv g := by
    apply curry_ext T
    intro a b i j s q e eq m t
    rw [curry_apply T _ a b i j (i+j) s q rfl e eq,
      uncurry_apply T g b a i j (i+j) s q rfl e eq]
  map_add' f g := by
    apply curry_ext T
    intro a b i j s q e eq m t
    rw [MixedGradedHom.add_app, LinearMap.add_apply, app_add]
    simp only [curry_apply T _ a b i j (i+j) s q rfl e eq,
      MixedGradedHom.add_app, LinearMap.add_apply]
  map_smul' c f := by
    apply curry_ext T
    intro a b i j s q e eq m t
    rw [MixedGradedHom.smul_app, LinearMap.smul_apply]
    change _ = c • GradedHom.app ((curry T f).app a i s e m) b j q eq t
    rw [curry_apply T _ a b i j (i+j) s q rfl e eq,
      curry_apply T f a b i j (i+j) s q rfl e eq]
    simp only [MixedGradedHom.smul_app, LinearMap.smul_apply]

/-- Currying commutes with the signed Hom differential. -/
theorem curry_d (f : MixedGradedHom (mixedTensorModule T M) (asMixed N) r) :
    curry T ((mixedHomComplex (mixedTensorModule T M) (asMixed N)).d r (r+1) f) =
      (mixedHomComplex (asMixed M) (mixedHomModule T N)).d r (r+1)
        (curry T f) := by
  apply curry_ext T
  intro a b i j s q e eq m t
  let n := i+j
  rw [mixedHomComplex_d, mixedHomComplex_d]
  rw [curry_apply T _ a b i j n s q rfl e eq,
    successor_at r f b n (j+(i+r)) q (by dsimp [n]; omega) (by omega),
    mixedTensorComplex_d_tmul T M b a i j n rfl m t,
    successor_apply r (curry T f) a i s e,
    app_sub, app_smul]
  change _ = GradedHom.app
    ((homComplex (T.obj a) N).d (i+r) s ((curry T f).app a i (i+r) rfl m))
      b j q eq t - r.negOnePow • _
  have hs : s = (i+r)+1 := by omega
  subst hs
  rw [RightDGModule.differentialFormula (i+r) _ b j q (by omega)]
  rw [curry_apply T f a b i j n (i+r) (j+(i+r)) rfl rfl rfl,
    curry_apply T f a b i (j+1) (n+1) (i+r) q (by dsimp [n]; omega) rfl (by omega),
    curry_apply T f a b (i+1) j (n+1) ((i+r)+1) q
      (by dsimp [n]; omega) (by omega) (by omega)]
  simp only [map_add, Units.smul_def, map_zsmul,
    smul_add, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [mul_comm (r.negOnePow : ℤ) (i.negOnePow : ℤ)]
  abel

/-- The signed tensor–Hom adjunction at the level of complexes. -/
def curryIso (M : RightDGModule A) (N : RightDGModule B) :
    mixedHomComplex (mixedTensorModule T M) (asMixed N) ≅
      mixedHomComplex (asMixed M) (mixedHomModule T N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => (curryEquiv T M N r).toModuleIso) (by
      intro r s h
      change r+1=s at h
      subst s
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact fun f => (curry_d T f).symm)

end Mixed
end

end DerivedFormalization.DGBimodule

namespace DerivedFormalization.DGBimodule

open RightDGModule (GradedHom)
open Specs.DerivedFormalization.DG.BalancedTensor (RightModule tmul)
open Specs.DerivedFormalization.DG.BimoduleAdjunction
open Specs.DerivedFormalization.DG.HomComplex (ofStrict)

noncomputable section

set_option maxHeartbeats 800000

set_option allowUnsafeReducibility true in
attribute [local reducible] mixedTensorFunctor mixedHomFunctor tensorFunctor homFunctor

variable {k : Type u} [CommRing k]

section Models

universe vA

variable {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k} (T : DGBimodule A B)

/-- The actual balanced quotient model used by the tensor functor. -/
@[reducible] def tensorModel : TensorModel T where
  functor := mixedTensorFunctor T
  degree _ _ _ := LinearEquiv.refl _ _
  d_tmul M a b i j n h m t := mixedTensorComplex_d_tmul T M b a i j n h m t
  act_tmul M a b c i j n l q h e m t f :=
    mixedTensorModule_act_tmul T M (b := b) (c := c) a i j n l (j+l) q h e rfl m t f
  map_tmul f a b i j n h m t := mixedTensorMap_tmul T f b a i j n h m t

/-- The actual precomposition model used by the internal Hom functor. -/
@[reducible] def internalHomModel : InternalHomModel T where
  functor := mixedHomFunctor T
  objectwise _ _ := Iso.refl _
  action N a a' i j n h g f := mixedHomModule_act T N (a := a) (b := a') i j n h g f
  map f a i g := mixedHomMap_apply T f a i g

theorem representableTensor : RepresentableTensor.{u,vA,w,v,z} := by
  intro k _ A B T
  refine ⟨tensorModel T, fun a => ?_⟩
  refine ⟨⟨representableEquiv T a, representableEquiv_d T a,
    fun i j n h x u => representableEquiv_act T a i j n h x u⟩, ?_, ?_⟩
  · intro b c i j n e f t
    exact representableEquiv_apply T a b c i j n e f t
  · intro b n t
    exact representableEquiv_symm_apply T a b n t

theorem mixedCurryLaws : CurryLaws (tensorModel T) (internalHomModel T) (Mixed.curryIso T) := by
  constructor
  · intro M N r F a b i j n s q e h h' m t
    exact Mixed.curry_apply T F a b i j n s q e h h' m t
  · intro M M' f N r F
    apply Mixed.curry_ext T
    intro a b i j s q e eq m t
    change GradedHom.app ((Mixed.curry T (precompose (mixedTensorMap T f) F)).app a i s e m) b j q eq t =
      GradedHom.app ((precompose (asMixedMap f) (Mixed.curry T F)).app a i s e m) b j q eq t
    rw [Mixed.curry_apply T _ a b i j (i+j) s q rfl e eq]
    rw [precompose_apply (mixedTensorMap T f) F b (i+j) q (by omega)
      (tmul T M' b a i j (i+j) rfl m t),
      precompose_apply (asMixedMap f) (Mixed.curry T F) a i s e m]
    change F.app b (i+j) q _ (((mixedTensorMap T f).app b).f (i+j) (tmul T M' b a i j (i+j) rfl m t)) =
      GradedHom.app ((Mixed.curry T F).app a i s e ((f.app a).f i m)) b j q eq t
    rw [mixedTensorMap_tmul, Mixed.curry_apply T F a b i j (i+j) s q rfl e eq]
  · intro M N N' f r F
    apply Mixed.curry_ext T
    intro a b i j s q e eq m t
    change GradedHom.app ((Mixed.curry T (postcompose (asMixedMap f) F)).app a i s e m) b j q eq t =
      GradedHom.app ((postcompose (mixedHomMap T f) (Mixed.curry T F)).app a i s e m) b j q eq t
    rw [Mixed.curry_apply T _ a b i j (i+j) s q rfl e eq]
    rw [postcompose_apply (asMixedMap f) F b (i+j) q (by omega)
      (tmul T M b a i j (i+j) rfl m t),
      postcompose_apply (mixedHomMap T f) (Mixed.curry T F) a i s e m]
    change (f.app b).f q (F.app b (i+j) q _ (tmul T M b a i j (i+j) rfl m t)) =
      GradedHom.app (((mixedHomMap T f).app a).f s ((Mixed.curry T F).app a i s e m)) b j q eq t
    rw [mixedHomMap_apply, RightDGModule.compositionFormula 0 s s _ _ _ b j q q eq (add_zero q),
      strict_app, Mixed.curry_apply T F a b i j (i+j) s q rfl e eq]

theorem signedAdjunction : SignedAdjunction.{u,vA,w,v,z} :=
  fun _ _ T => ⟨tensorModel T, internalHomModel T, Mixed.curryIso T, mixedCurryLaws T⟩

end Models

theorem strictAdjunctionLaws {A : DGCategory.{u,max v w z,w} k}
    {B : DGCategory.{u,max v w z,z} k} (T : DGBimodule A B) :
    StrictLaws.{u,v,w,z} (tensorModel T) (internalHomModel T)
      (curryIso.{u,v,w,z} T) (adjunction.{u,v,w,z} T) := by
  constructor
  · intro M N r F a b i j n s q e h h' m t
    exact curry_apply.{u,v,w,z} T F a b i j n s q e h h' m t
  · intro M N f
    rw [adjunction_homEquiv.{u,v,w,z} T]
    change ofStrict (strictCurryEquiv.{u,v,w,z} T M N f) = curry.{u,v,w,z} T (ofStrict f)
    exact congrArg Subtype.val
      (RightDGModule.strictCycle_strictMap (curriedCycle.{u,v,w,z} T f))
  · intro M a b i j n h m t
    exact unit_apply.{u,v,w,z} T M a b i j n h m t
  · intro N a b i j n h g t
    exact counit_apply.{u,v,w,z} T N a b i j n h g t

theorem underivedAdjunction : UnderivedAdjunction.{u,v,w,z} :=
  fun _ _ T => ⟨tensorModel T, internalHomModel T, curryIso.{u,v,w,z} T,
    adjunction.{u,v,w,z} T, strictAdjunctionLaws.{u,v,w,z} T⟩

end
end DerivedFormalization.DGBimodule

namespace DerivedFormalization.DGBimodule

open DG.CoefficientLift
open Specs.DerivedFormalization.DG.BalancedTensor (Degree tmul left RightModule CochainMap)
open Specs.DerivedFormalization.DG.BimoduleAdjunction
open Specs.DerivedFormalization.DG.HomComplex (ofStrict)
open RightDGModule (GradedHom homComplex dgCategory)

noncomputable section

universe vA s

variable {k : Type u} [CommRing k]
variable {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
variable (T : DGBimodule A B)

set_option maxHeartbeats 800000

/-- Lift the values of the bimodule and conjugate its homogeneous arrow maps. -/
@[reducible] def liftBimodule :
    DGBimodule (liftCategory.{u,vA,w,max v w z s} A) (liftCategory.{u,v,z,max vA w z s} B) where
  obj a := liftModule.{u,v,z,max vA w z s} (T.obj a)
  map a b :=
    { f := fun j => ((gradedEquiv.{u,v,z,max vA w z s} (T.obj a) (T.obj b) j).toLinearMap.comp
        ((T.map a b).f j)).comp ULift.moduleEquiv.toLinearMap
      comm := by
        intro i x
        change gradedEquiv _ _ (i+1) ((T.map a b).f (i+1) ((A.hom a b).d i (i+1) x.down)) =
          (homComplex _ _).d i (i+1) (gradedEquiv _ _ i ((T.map a b).f i x.down))
        rw [(T.map a b).comm, gradedEquiv_comm_d] }
  map_id a := by
    change gradedEquiv _ _ 0 ((T.map a a).f 0 (A.id a)) = _
    rw [T.map_id]
    exact (gradedEquiv_strict (𝟙 (T.obj a))).trans (congrArg ofStrict rfl)
  map_comp i j n h f g := by
    change gradedEquiv _ _ n ((T.map _ _).f n (A.comp i j n h f.down g.down)) = _
    rw [T.map_comp]
    exact gradedEquiv_comp i j n h _ _


theorem liftBimodule_left (b : B.Obj) {a a' : A.Obj} (l j n : ℤ) (h : l+j=n)
    (f : (A.hom a a').X l) (t : ((T.obj a).complex b).X j) :
    left (liftBimodule.{u,v,w,z,vA,s} T) b l j n h (ULift.up f) (ULift.up t) = ULift.up (left T b l j n h f t) :=
  ULift.ext (gradedEquiv_apply_down l _ b j n (by omega) _)

variable (M : RightDGModule A)

private def tensorUp (b : B.Obj) (n : ℤ) : Degree T M b n →ₗ[k] Degree (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b n :=
  lift T M
    (fun a i j h => (tensorPair (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b a i j n h).compl₁₂
      ULift.moduleEquiv.symm.toLinearMap ULift.moduleEquiv.symm.toLinearMap)
    (by
      intro a a' i l j h m f t
      change tmul (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b a (i+l) j n h (ULift.up (M.act i l (i+l) rfl m f)) (ULift.up t) =
        tmul (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b a' i (l+j) n _ (ULift.up m) (ULift.up (left T b l j (l+j) rfl f t))
      rw [← liftBimodule_left.{u,v,w,z,vA,s} T b l j (l+j) rfl f t]
      exact tmul_balance (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b i l j (i+l) (l+j) n rfl rfl h (ULift.up m) (ULift.up f) (ULift.up t))

private def tensorDown (b : B.Obj) (n : ℤ) : Degree (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b n →ₗ[k] Degree T M b n :=
  lift (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M)
    (fun a i j h => (tensorPair T M b a i j n h).compl₁₂
      ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.toLinearMap)
    (by
      intro a a' i l j h m f t
      change tmul T M b a (i+l) j n h (M.act i l (i+l) rfl m.down f.down) t.down =
        tmul T M b a' i (l+j) n _ m.down ((left (liftBimodule.{u,v,w,z,vA,s} T) b l j (l+j) rfl f t).down)
      rw [show (left (liftBimodule.{u,v,w,z,vA,s} T) b l j (l+j) rfl f t).down = left T b l j (l+j) rfl f.down t.down from
        congrArg ULift.down (liftBimodule_left.{u,v,w,z,vA,s} T b l j (l+j) rfl f.down t.down)]
      exact tmul_balance T M b i l j (i+l) (l+j) n rfl rfl h m.down f.down t.down)

private theorem tensorUp_tmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tensorUp.{u,v,w,z,vA,s} T M b n (tmul T M b a i j n h m t) =
      tmul (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b a i j n h (ULift.up m) (ULift.up t) := by
  unfold tensorUp
  exact lift_tmul T M _ _ a i j h m t

private theorem tensorDown_tmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : ((liftModule.{u,vA,w,max v w z s} M).complex a).X i) (t : (((liftBimodule.{u,v,w,z,vA,s} T).obj a).complex b).X j) :
    tensorDown.{u,v,w,z,vA,s} T M b n (tmul (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b a i j n h m t) =
      tmul T M b a i j n h m.down t.down := by
  unfold tensorDown
  rw [lift_tmul]
  rfl

/-- The balanced quotient comparison is induced by the coefficient lift on each factor. -/
def tensorLiftEquiv (b : B.Obj) (n : ℤ) : Degree T M b n ≃ₗ[k] Degree (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b n where
  __ := tensorUp.{u,v,w,z,vA,s} T M b n
  invFun := tensorDown.{u,v,w,z,vA,s} T M b n
  left_inv := by
    have h : (tensorDown.{u,v,w,z,vA,s} T M b n).comp (tensorUp.{u,v,w,z,vA,s} T M b n) = LinearMap.id := by
      apply linearMap_ext T M
      intro a i j e m t
      rw [LinearMap.comp_apply, tensorUp_tmul.{u,v,w,z,vA,s}]
      exact tensorDown_tmul.{u,v,w,z,vA,s} T M b a i j n e (ULift.up m) (ULift.up t)
    exact DFunLike.congr_fun h
  right_inv := by
    have h : (tensorUp.{u,v,w,z,vA,s} T M b n).comp (tensorDown.{u,v,w,z,vA,s} T M b n) = LinearMap.id := by
      apply linearMap_ext (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M)
      intro a i j e m t
      rw [LinearMap.comp_apply, tensorDown_tmul.{u,v,w,z,vA,s}, tensorUp_tmul.{u,v,w,z,vA,s}]
      rfl
    exact DFunLike.congr_fun h

@[simp] theorem tensorLiftEquiv_tmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tensorLiftEquiv.{u,v,w,z,vA,s} T M b n (tmul T M b a i j n h m t) =
      tmul (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b a i j n h (ULift.up m) (ULift.up t) :=
  tensorUp_tmul.{u,v,w,z,vA,s} T M b a i j n h m t

theorem tensorLiftEquiv_d (b : B.Obj) (n : ℤ) (x : Degree T M b n) :
    tensorLiftEquiv.{u,v,w,z,vA,s} T M b (n+1) ((mixedTensorComplex T M b).d n (n+1) x) =
      (mixedTensorComplex (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b).d n (n+1) (tensorLiftEquiv.{u,v,w,z,vA,s} T M b n x) := by
  let F := (tensorLiftEquiv.{u,v,w,z,vA,s} T M b (n+1)).toLinearMap.comp ((mixedTensorComplex T M b).d n (n+1)).hom
  let G := ((mixedTensorComplex (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b).d n (n+1)).hom.comp (tensorLiftEquiv.{u,v,w,z,vA,s} T M b n).toLinearMap
  have e : F = G := by
    apply linearMap_ext T M
    intro a i j h m t
    change tensorLiftEquiv.{u,v,w,z,vA,s} T M b (n+1) ((mixedTensorComplex T M b).d n (n+1)
      (tmul T M b a i j n h m t)) = (mixedTensorComplex (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M) b).d n (n+1)
        (tensorLiftEquiv.{u,v,w,z,vA,s} T M b n (tmul T M b a i j n h m t))
    rw [mixedTensorComplex_d_tmul]
    simp only [map_add, Units.smul_def, map_zsmul]
    rw [tensorLiftEquiv_tmul.{u,v,w,z,vA,s}, tensorLiftEquiv_tmul.{u,v,w,z,vA,s}, tensorLiftEquiv_tmul.{u,v,w,z,vA,s}]
    have hd := mixedTensorComplex_d_tmul (liftBimodule.{u,v,w,z,vA,s} T)
      (liftModule.{u,vA,w,max v w z s} M) b a i j n h (ULift.up m) (ULift.up t)
    simp only [Units.smul_def] at hd
    exact hd.symm
  exact DFunLike.congr_fun e x

theorem tensorLiftEquiv_act {b c : B.Obj} (i j n : ℤ) (h : i+j=n)
    (x : Degree T M c i) (f : (B.hom b c).X j) :
    tensorLiftEquiv.{u,v,w,z,vA,s} T M b n ((mixedTensorModule T M).act i j n h x f) =
      (mixedTensorModule (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M)).act i j n h (tensorLiftEquiv.{u,v,w,z,vA,s} T M c i x) (ULift.up f) := by
  let F := (tensorLiftEquiv.{u,v,w,z,vA,s} T M b n).toLinearMap.comp (((mixedTensorModule T M).act (a := b) (b := c) i j n h).flip f)
  let G := (((mixedTensorModule (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M)).act (a := b) (b := c) i j n h).flip (ULift.up f)).comp
    (tensorLiftEquiv.{u,v,w,z,vA,s} T M c i).toLinearMap
  have e : F = G := by
    apply linearMap_ext T M
    intro a p q e m t
    change tensorLiftEquiv.{u,v,w,z,vA,s} T M b n ((mixedTensorModule T M).act i j n h
      (tmul T M c a p q i e m t) f) = (mixedTensorModule (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M)).act i j n h
      (tensorLiftEquiv.{u,v,w,z,vA,s} T M c i (tmul T M c a p q i e m t)) (ULift.up f)
    rw [mixedTensorModule_act_tmul T M a p q i j (q+j) n e h rfl,
      tensorLiftEquiv_tmul.{u,v,w,z,vA,s}, tensorLiftEquiv_tmul.{u,v,w,z,vA,s}]
    exact (mixedTensorModule_act_tmul (liftBimodule.{u,v,w,z,vA,s} T)
      (liftModule.{u,vA,w,max v w z s} M) a p q i j (q+j) n e h rfl
      (ULift.up m) (ULift.up t) (ULift.up f)).symm
  exact DFunLike.congr_fun e x

theorem tensorLiftEquiv_map {M P : RightDGModule A} (f : M ⟶ P)
    (b : B.Obj) (n : ℤ) (x : Degree T M b n) :
    tensorLiftEquiv.{u,v,w,z,vA,s} T P b n (((mixedTensorMap T f).app b).f n x) =
      ((mixedTensorMap (liftBimodule.{u,v,w,z,vA,s} T) (liftMap.{u,vA,w,max v w z s} f)).app b).f n (tensorLiftEquiv.{u,v,w,z,vA,s} T M b n x) := by
  let F := (tensorLiftEquiv.{u,v,w,z,vA,s} T P b n).toLinearMap.comp (((mixedTensorMap T f).app b).f n).hom
  let G := (((mixedTensorMap (liftBimodule.{u,v,w,z,vA,s} T) (liftMap.{u,vA,w,max v w z s} f)).app b).f n).hom.comp
    (tensorLiftEquiv.{u,v,w,z,vA,s} T M b n).toLinearMap
  have e : F = G := by
    apply linearMap_ext T M
    intro a i j e m t
    change tensorLiftEquiv.{u,v,w,z,vA,s} T P b n (((mixedTensorMap T f).app b).f n
      (tmul T M b a i j n e m t)) =
      ((mixedTensorMap (liftBimodule.{u,v,w,z,vA,s} T) (liftMap.{u,vA,w,max v w z s} f)).app b).f n
        (tensorLiftEquiv.{u,v,w,z,vA,s} T M b n (tmul T M b a i j n e m t))
    rw [mixedTensorMap_tmul, tensorLiftEquiv_tmul.{u,v,w,z,vA,s}, tensorLiftEquiv_tmul.{u,v,w,z,vA,s}]
    exact (mixedTensorMap_tmul (liftBimodule.{u,v,w,z,vA,s} T)
      (liftMap.{u,vA,w,max v w z s} f) b a i j n e (ULift.up m) (ULift.up t)).symm
  exact DFunLike.congr_fun e x

/-- A comparison over the original arrows, using the ambient tensor terms. -/
def tensorLiftComparison :
    ModuleEquiv (mixedTensorModule T M) (restrictLifted (mixedTensorModule (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,vA,w,max v w z s} M))) where
  degree := tensorLiftEquiv.{u,v,w,z,vA,s} T M
  comm_d := tensorLiftEquiv_d.{u,v,w,z,vA,s} T M
  comm_act i j n h x f := tensorLiftEquiv_act.{u,v,w,z,vA,s} T M i j n h x f

variable (N : RightDGModule B)

/-- Internal Hom commutes with coefficient enlargement by conjugation on each component. -/
def homLiftComparison :
    ModuleEquiv (mixedHomModule T N) (restrictLifted (mixedHomModule (liftBimodule.{u,v,w,z,vA,s} T) (liftModule.{u,v,z,max vA w z s} N))) where
  degree a := gradedEquiv.{u,v,z,max vA w z s} (T.obj a) N
  comm_d _ n g := gradedEquiv_comm_d n (n+1) g
  comm_act i j n h g f := gradedEquiv_comp i j n h g ((T.map _ _).f j f)

theorem homLiftComparison_map {N P : RightDGModule B} (f : N ⟶ P)
    (a : A.Obj) (i : ℤ) (g : GradedHom (T.obj a) N i) :
    (homLiftComparison.{u,v,w,z,vA,s} T P).degree a i (((mixedHomMap T f).app a).f i g) =
      ((mixedHomMap (liftBimodule.{u,v,w,z,vA,s} T) (liftMap.{u,v,z,max vA w z s} f)).app a).f i
        ((homLiftComparison.{u,v,w,z,vA,s} T N).degree a i g) := by
  change gradedEquiv.{u,v,z,max vA w z s} (T.obj a) P i
    (dgCategory B |>.comp 0 i i (zero_add i) (ofStrict f) g) =
    (dgCategory _ |>.comp 0 i i (zero_add i) (ofStrict (liftMap.{u,v,z,max vA w z s} f))
      (gradedEquiv.{u,v,z,max vA w z s} (T.obj a) N i g))
  rw [gradedEquiv_comp, gradedEquiv_strict]

section Conjugation

open MixedGradedHom (app)

variable {C : DGCategory.{u,v,w} k}
variable {X : RightModule.{u,v,w,s} C} {Y : RightModule.{u,v,w,vA} C}
variable {X' Y' : RightDGModule (liftCategory.{u,v,w,z} C)}
variable (ex : ModuleEquiv X (restrictLifted.{u,v,w,max v z,z} (asMixed X')))
variable (ey : ModuleEquiv Y (restrictLifted.{u,v,w,max v z,z} (asMixed Y')))
variable {r : ℤ}

private theorem transport_act {a b : C.Obj} (i j n : ℤ) (h : i+j=n)
    (x : (X.complex b).X i) (f : (C.hom a b).X j) :
    ex.degree a n (X.act i j n h x f) =
      X'.act i j n h (ex.degree b i x) (ULift.up f) :=
  ex.comm_act i j n h x f

private def transportGraded (f : MixedGradedHom X Y r) : GradedHom X' Y' r :=
  GradedHom.mk (fun a i n h => ModuleCat.ofHom
    ((ey.degree a n).toLinearMap.comp ((f.app a i n h).comp (ex.degree a i).symm.toLinearMap)))
    (by
      intro a b i j n ir nr h hi hn x g
      change ey.degree a nr (f.app a n nr hn ((ex.degree a n).symm (X'.act i j n h x g))) =
        Y'.act ir j nr _ (ey.degree b ir (f.app b i ir hi ((ex.degree b i).symm x))) g
      have e := transport_act ex i j n h ((ex.degree b i).symm x) g.down
      rw [LinearEquiv.apply_symm_apply] at e
      change ex.degree a n (X.act i j n h ((ex.degree b i).symm x) g.down) =
        X'.act i j n h x g at e
      rw [← e, LinearEquiv.symm_apply_apply, f.comm_act i j n ir nr h hi hn, transport_act ey]
      rfl)

private def descendGraded (f : GradedHom X' Y' r) : MixedGradedHom X Y r :=
  MixedGradedHom.mk
    (fun a i n h => (ey.degree a n).symm.toLinearMap.comp ((f.app a i n h).hom.comp (ex.degree a i).toLinearMap))
    (by
      intro a b i j n ir nr h hi hn x g
      change (ey.degree a nr).symm (f.app a n nr hn (ex.degree a n (X.act i j n h x g))) =
        Y.act ir j nr _ ((ey.degree b ir).symm (f.app b i ir hi (ex.degree b i x))) g
      apply (ey.degree a nr).injective
      rw [LinearEquiv.apply_symm_apply, transport_act ex, transport_act ey, LinearEquiv.apply_symm_apply]
      exact f.comm_act i j n ir nr h hi hn (ex.degree b i x) (ULift.up g))

/-- Conjugation identifies all degrees of Hom after transporting both modules. -/
def transportGradedEquiv (r : ℤ) : MixedGradedHom X Y r ≃ₗ[k] GradedHom X' Y' r where
  toFun := transportGraded ex ey
  invFun := descendGraded ex ey
  left_inv f := by
    apply MixedGradedHom.ext
    intro a i n h x
    simp only [descendGraded, MixedGradedHom.mk_app, LinearMap.comp_apply, transportGraded,
      GradedHom.mk_app, ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  right_inv f := by
    apply graded_ext
    intro a i n h x
    change ey.degree a n ((descendGraded ex ey f).app a i n h ((ex.degree a i).symm x)) = _
    unfold descendGraded
    rw [MixedGradedHom.mk_app]
    change ey.degree a n ((ey.degree a n).symm (f.app a i n h
      (ex.degree a i ((ex.degree a i).symm x)))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  map_add' f g := by
    apply graded_ext
    intro a i n h x
    rw [app_add]
    change ey.degree a n ((f + g).app a i n h ((ex.degree a i).symm x)) =
      ey.degree a n (f.app a i n h ((ex.degree a i).symm x)) +
      ey.degree a n (g.app a i n h ((ex.degree a i).symm x))
    rw [MixedGradedHom.add_app, LinearMap.add_apply, map_add]
  map_smul' c f := by
    apply graded_ext
    intro a i n h x
    have hsm (F : GradedHom X' Y' r) : (c • F).app a i n h x = c • F.app a i n h x := by
      change ((c • F.val a).v i n h) x = _
      rw [Cochain.smul_v]
      rfl
    change (transportGraded ex ey (c • f)).app a i n h x =
      (c • transportGraded ex ey f).app a i n h x
    rw [hsm]
    change ey.degree a n ((c • f).app a i n h ((ex.degree a i).symm x)) =
      c • ey.degree a n (f.app a i n h ((ex.degree a i).symm x))
    rw [MixedGradedHom.smul_app, LinearMap.smul_apply, map_smul]

theorem transportGradedEquiv_apply (f : MixedGradedHom X Y r)
    (a : C.Obj) (i n : ℤ) (h : i+r=n) (x : (X.complex a).X i) :
    (transportGradedEquiv ex ey r f).app a i n h (ex.degree a i x) =
      ey.degree a n (f.app a i n h x) := by
  change ey.degree a n (f.app a i n h ((ex.degree a i).symm (ex.degree a i x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Conjugation is compatible with the signed commutator differential. -/
theorem transportGradedEquiv_d (f : MixedGradedHom X Y r) :
    transportGradedEquiv ex ey (r+1) (successor X Y r f) =
      (homComplex X' Y').d r (r+1) (transportGradedEquiv ex ey r f) := by
  apply graded_ext
  intro a i n h x'
  obtain ⟨x, rfl⟩ := (ex.degree a i).surjective x'
  rw [transportGradedEquiv_apply, successor_apply, RightDGModule.differentialFormula]
  have hx := ex.comm_d a i x
  change ex.degree a (i+1) ((X.complex a).d i (i+1) x) =
    (X'.complex a).d i (i+1) (ex.degree a i x) at hx
  rw [← hx, transportGradedEquiv_apply, transportGradedEquiv_apply]
  obtain rfl : (i+r)+1=n := by omega
  have hy := ey.comm_d a (i+r) (f.app a i (i+r) rfl x)
  change ey.degree a ((i+r)+1) ((Y.complex a).d (i+r) ((i+r)+1) (f.app a i (i+r) rfl x)) =
    (Y'.complex a).d (i+r) ((i+r)+1) (ey.degree a (i+r) (f.app a i (i+r) rfl x)) at hy
  simp only [map_sub, Units.smul_def, map_zsmul, hy]

end Conjugation

section Ambient

set_option allowUnsafeReducibility true in
attribute [local reducible] mixedTensorFunctor mixedHomFunctor tensorFunctor homFunctor

private def liftModuleComparison {C : DGCategory.{u,v,w} k} (X : RightDGModule C) :
    ModuleEquiv (asMixed X) (restrictLifted.{u,v,w,max v z,z}
      (asMixed (liftModule.{u,v,w,z} X))) where
  degree _ _ := ULift.moduleEquiv.symm
  comm_d _ _ _ := rfl
  comm_act _ _ _ _ _ _ := rfl

/-- Identify the actual tensor and Hom outputs before and after coefficient enlargement. -/
def ambientOutputComparisons :
    OutputComparisons.{u,v,w,vA,z,s}
      (fun a => liftModuleComparison.{u,v,z,max vA w z s} (T.obj a))
      (tensorModel T) (internalHomModel T)
      (tensorModel (liftBimodule.{u,v,w,z,vA,s} T))
      (internalHomModel (liftBimodule.{u,v,w,z,vA,s} T)) where
  tensor M := tensorLiftComparison.{u,v,w,z,vA,s} T M
  hom N := homLiftComparison.{u,v,w,z,vA,s} T N
  tensor_tmul M b a i j n h m x := tensorLiftEquiv_tmul.{u,v,w,z,vA,s} T M b a i j n h m x
  hom_eval _ _ b r i n h g x :=
    ULift.ext (gradedEquiv_apply_down.{u,v,z,max vA w z s} r g b i n h (ULift.up x))
  tensor_map f b n x := tensorLiftEquiv_map.{u,v,w,z,vA,s} T f b n x
  hom_map f a n x := homLiftComparison_map.{u,v,w,z,vA,s} T f a n x

/-- The adjunction for independently sized inputs, at any common adequate bound. -/
theorem ambientAdjunction : AmbientAdjunction.{u,v,w,vA,z,s} := by
  intro k _ A B T
  let S := liftBimodule.{u,v,w,z,vA,s} T
  let D := ambientOutputComparisons.{u,v,w,z,vA,s} T
  have hs := strictAdjunctionLaws.{u,max vA v s,w,z} S
  refine ⟨S, (fun a => liftModuleComparison.{u,v,z,max vA w z s} (T.obj a)),
    tensorModel T, internalHomModel T, Mixed.curryIso T, tensorModel S, internalHomModel S,
    curryIso.{u,max vA v s,w,z} S, adjunction.{u,max vA v s,w,z} S, D,
    ?_, mixedCurryLaws T, hs, ?_, ?_⟩
  · constructor
    · intro a
      rfl
    · intro a b n x
      rfl
    · intro b a a' i j n h f x
      exact (liftBimodule_left.{u,v,w,z,vA,s} T b i j n h f x).symm
  · let EM (M : RightDGModule A) := liftModuleComparison.{u,vA,w,max v w z s} M
    let EN (N : RightDGModule B) := liftModuleComparison.{u,v,z,max vA w z s} N
    let ES (M : RightDGModule A) (N : RightDGModule B) (r : ℤ) :=
      transportGradedEquiv (D.tensor M) (EN N) r
    let ET (M : RightDGModule A) (N : RightDGModule B) (r : ℤ) :=
      transportGradedEquiv (EM M) (D.hom N) r
    refine ⟨⟨ES, ET, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro M N r F b i n h x
      exact transportGradedEquiv_apply (D.tensor M) (EN N) F b i n h x
    · intro M N r F a i n h x
      exact transportGradedEquiv_apply (EM M) (D.hom N) F a i n h x
    · intro M N r F
      have h := transportGradedEquiv_d (D.tensor M) (EN N) F
      rw [← mixedHomComplex_d r F] at h
      exact h
    · intro M N r F
      have h := transportGradedEquiv_d (EM M) (D.hom N) F
      rw [← mixedHomComplex_d r F] at h
      exact h
    · intro M N r F
      apply graded_ext
      intro a i p hp m'
      obtain ⟨m, rfl⟩ := (EM M |>.degree a i).surjective m'
      apply graded_ext
      intro b j q hq x'
      obtain ⟨x, rfl⟩ :=
        ((liftModuleComparison.{u,v,z,max vA w z s} (T.obj a)).degree b j).surjective x'
      let f' := ES M N r F
      let g := Mixed.curry T F
      have htarget := transportGradedEquiv_apply (EM M) (D.hom N) g a i p hp m
      have hsource := transportGradedEquiv_apply (D.tensor M) (EN N) F b (i+j) q (by omega)
        (tmul T M b a i j (i+j) rfl m x)
      change (f'.app b (i+j) q _ ((D.tensor M).degree b (i+j)
        (tmul T M b a i j (i+j) rfl m x))) =
        ULift.up (F.app b (i+j) q _ (tmul T M b a i j (i+j) rfl m x)) at hsource
      have hgen : (D.tensor M).degree b (i+j) (tmul T M b a i j (i+j) rfl m x) =
          tmul S (liftModule.{u,vA,w,max v w z s} M) b a i j (i+j) rfl (ULift.up m) (ULift.up x) :=
        D.tensor_tmul M b a i j (i+j) rfl m x
      have h₁ := curry_apply.{u,max vA v s,w,z} S f' a b i j (i+j) p q rfl hp hq
        (ULift.up m) (ULift.up x)
      have h₂ := (congrArg (fun y => f'.app b (i+j) q (by omega) y) hgen.symm).trans hsource
      have h₃ := congrArg (ULift.up.{max vA w z s})
        (Mixed.curry_apply T F a b i j (i+j) p q rfl hp hq m x).symm
      have h₄ := (D.hom_eval N a b p j q hq (g.app a i p hp m) x).symm
      have h₅ := congrArg (fun y => GradedHom.app y b j q hq (ULift.up x)) htarget.symm
      exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  · constructor
    · intro M a b i j n h m x
      exact (hs.unit (liftModule.{u,vA,w,max v w z s} M) a b i j n h
        (ULift.up m) (ULift.up x)).trans (D.tensor_tmul M b a i j n h m x).symm
    · intro N a b i j n h g x
      exact (hs.counit (liftModule.{u,v,z,max vA w z s} N) a b i j n h
        ((D.hom N).degree a i g) (ULift.up x)).trans
          (D.hom_eval N a b i j n (by omega) g x)

end Ambient

end
end DerivedFormalization.DGBimodule
