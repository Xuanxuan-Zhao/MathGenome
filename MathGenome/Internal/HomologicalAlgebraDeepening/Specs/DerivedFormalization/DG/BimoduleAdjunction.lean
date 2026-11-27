import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BalancedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLift
import Mathlib.CategoryTheory.Adjunction.Basic

open CategoryTheory

universe u v w p q vA z

namespace Specs.DerivedFormalization.DG.BimoduleAdjunction

open _root_.DerivedFormalization
open BalancedTensor (RightModule Degree tmul left bimodule CochainMap)
open HomComplex (gradedHom homComplex component dgModuleCategory ofStrict)
open scoped Classical

variable {k : Type u} [CommRing k]

/-- View an ordinary dg module as one with independent coefficient universe. -/
@[reducible] def asMixed {C : DGCategoryModel.{u,v,w} k} (M : RightDGModuleModel C) :
    RightModule.{u,v,w,v} C :=
  ⟨M.complex, M.act, M.act_id, M.act_assoc, M.leibniz⟩

section MixedHom

variable {C : DGCategoryModel.{u,v,w} k}
variable {X : RightModule.{u,v,w,p} C} {Y : RightModule.{u,v,w,q} C}

abbrev Family (X : RightModule.{u,v,w,p} C) (Y : RightModule.{u,v,w,q} C) (r : ℤ) :=
  ∀ (a : C.Obj) (i : ℤ), (X.complex a).X i →ₗ[k] (Y.complex a).X (i+r)

private def atDegree {r : ℤ} (f : Family X Y r) (a : C.Obj) (i n : ℤ) (e : i+r=n) :
    (X.complex a).X i →ₗ[k] (Y.complex a).X n := e ▸ f a i

/-- Homogeneous right-linearity retains the sign-free convention with mixed coefficients. -/
def IsRightLinear {r : ℤ} (f : Family X Y r) : Prop :=
  ∀ {a b : C.Obj} (i j n ir nr : ℤ) (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr)
    (x : (X.complex b).X i) (u : (C.hom a b).X j),
    atDegree f a n nr hn (X.act i j n h x u) =
      Y.act ir j nr (by omega) (atDegree f b i ir hi x) u

def gradedSubmodule (X : RightModule.{u,v,w,p} C) (Y : RightModule.{u,v,w,q} C) (r : ℤ) :
    Submodule k (Family X Y r) where
  carrier := { f | IsRightLinear f }
  zero_mem' := by
    intro a b i j n ir nr h hi hn x f
    subst ir nr
    simp [atDegree]
  add_mem' := by
    intro f g hf hg a b i j n ir nr h hi hn x t
    subst ir nr
    simp only [atDegree, Pi.add_apply, LinearMap.add_apply, map_add]
    rw [show f a n (X.act i j n h x t) = _ from hf i j n (i+r) (n+r) h rfl rfl x t,
      show g a n (X.act i j n h x t) = _ from hg i j n (i+r) (n+r) h rfl rfl x t]
    rfl
  smul_mem' := by
    intro c f hf a b i j n ir nr h hi hn x t
    subst ir nr
    simp only [atDegree, Pi.smul_apply, LinearMap.smul_apply, map_smul]
    rw [show f a n (X.act i j n h x t) = _ from hf i j n (i+r) (n+r) h rfl rfl x t]
    rfl

abbrev MixedGradedHom (X : RightModule.{u,v,w,p} C) (Y : RightModule.{u,v,w,q} C) (r : ℤ) :=
  ↥(gradedSubmodule X Y r)

namespace MixedGradedHom

variable {r : ℤ}

abbrev app (f : MixedGradedHom X Y r) := atDegree f.val

/-- Build a mixed homogeneous map by giving all its components. -/
def mk (f : ∀ (a : C.Obj) (i n : ℤ) (_ : i+r=n),
      (X.complex a).X i →ₗ[k] (Y.complex a).X n)
    (hf : ∀ {a b : C.Obj} (i j n ir nr : ℤ) (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr)
      (x : (X.complex b).X i) (u : (C.hom a b).X j),
      f a n nr hn (X.act i j n h x u) = Y.act ir j nr (by omega) (f b i ir hi x) u) :
    MixedGradedHom X Y r :=
  ⟨fun a i => f a i (i+r) rfl, by
    intro a b i j n ir nr h hi hn x u
    subst ir nr
    exact hf i j n (i+r) (n+r) h rfl rfl x u⟩

@[simp] theorem mk_app (f) (hf) (a : C.Obj) (i n : ℤ) (e : i+r=n) :
    (mk (X := X) (Y := Y) f hf).app a i n e = f a i n e := by
  subst n
  rfl

theorem ext {f g : MixedGradedHom X Y r}
    (h : ∀ a i n e x, f.app a i n e x = g.app a i n e x) : f = g :=
  Subtype.ext (funext fun a => funext fun i => LinearMap.ext (h a i (i+r) rfl))

theorem comm_act (f : MixedGradedHom X Y r) {a b : C.Obj}
    (i j n ir nr : ℤ) (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr)
    (x : (X.complex b).X i) (u : (C.hom a b).X j) :
    f.app a n nr hn (X.act i j n h x u) = Y.act ir j nr (by omega) (f.app b i ir hi x) u :=
  f.property i j n ir nr h hi hn x u

@[simp] theorem zero_app (a : C.Obj) (i n : ℤ) (e : i+r=n) :
    (0 : MixedGradedHom X Y r).app a i n e = 0 := by
  subst n
  rfl

@[simp] theorem add_app (f g : MixedGradedHom X Y r) (a : C.Obj) (i n : ℤ) (e : i+r=n) :
    (f + g).app a i n e = f.app a i n e + g.app a i n e := by
  subst n
  rfl

@[simp] theorem sub_app (f g : MixedGradedHom X Y r) (a : C.Obj) (i n : ℤ) (e : i+r=n) :
    (f - g).app a i n e = f.app a i n e - g.app a i n e := by
  subst n
  rfl

@[simp] theorem smul_app (c : k) (f : MixedGradedHom X Y r) (a : C.Obj) (i n : ℤ) (e : i+r=n) :
    (c • f).app a i n e = c • f.app a i n e := by
  subst n
  rfl

@[simp] theorem units_app (c : ℤˣ) (f : MixedGradedHom X Y r) (a : C.Obj) (i n : ℤ) (e : i+r=n) :
    (c • f).app a i n e = c • f.app a i n e := by
  subst n
  rfl

end MixedGradedHom

private def successorFamily (r : ℤ) (f : Family X Y r) : Family X Y (r+1) :=
  fun a i => ((Y.complex a).d (i+r) (i+(r+1))).hom.comp (f a i) -
    r.negOnePow • (atDegree f a (i+1) (i+(r+1)) (by omega)).comp ((X.complex a).d i (i+1)).hom

private theorem successorFamily_apply (r : ℤ) (f : Family X Y r) (a : C.Obj)
    (i n : ℤ) (e : i+(r+1)=n) (x : (X.complex a).X i) :
    atDegree (successorFamily r f) a i n e x =
      (Y.complex a).d (i+r) n (atDegree f a i (i+r) rfl x) -
        r.negOnePow • atDegree f a (i+1) n (by omega) ((X.complex a).d i (i+1) x) := by
  subst n
  rfl

private theorem successor_rightLinear (r : ℤ) (f : MixedGradedHom X Y r) :
    IsRightLinear (successorFamily r f.val) := by
  intro a b i j n ir nr h hi hn x z
  rw [successorFamily_apply, successorFamily_apply]
  have e₁ : ir = (i+r)+1 := by omega
  have e₂ : nr = (n+r)+1 := by omega
  subst e₁ e₂
  rw [f.comm_act i j n (i+r) (n+r) h rfl rfl,
    Y.leibniz (i+r) j (n+r) (by omega), X.leibniz i j n h]
  simp only [map_add, Units.smul_def, map_zsmul]
  rw [f.comm_act (i+1) j (n+1) ((i+r)+1) ((n+r)+1) (by omega) (by omega) (by omega),
    f.comm_act i (j+1) (n+1) (i+r) ((n+r)+1) (by omega) rfl (by omega)]
  simp only [smul_add, smul_smul, Int.negOnePow_add, Units.val_mul, map_sub,
    LinearMap.sub_apply, map_zsmul]
  rw [mul_comm (r.negOnePow : ℤ) (i.negOnePow : ℤ)]
  abel

/-- The signed commutator in successor degrees. -/
def successor (X : RightModule.{u,v,w,p} C) (Y : RightModule.{u,v,w,q} C) (r : ℤ) :
    MixedGradedHom X Y r →ₗ[k] MixedGradedHom X Y (r+1) where
  toFun f := ⟨successorFamily r f.val, successor_rightLinear r f⟩
  map_add' f g := by
    apply MixedGradedHom.ext
    intro a i n e x
    rw [MixedGradedHom.add_app, LinearMap.add_apply]
    change atDegree (successorFamily r (f + g).val) a i n e x =
      atDegree (successorFamily r f.val) a i n e x + atDegree (successorFamily r g.val) a i n e x
    subst n
    have ha (j q : ℤ) (h : j+r=q) :
        atDegree (f + g).val a j q h = atDegree f.val a j q h + atDegree g.val a j q h :=
      MixedGradedHom.add_app f g a j q h
    simp only [successorFamily_apply, ha, LinearMap.add_apply]
    change ((Y.complex a).d (i+r) _).hom _ - _ = _
    simp only [map_add, smul_add]
    abel
  map_smul' c f := by
    apply MixedGradedHom.ext
    intro a i n e x
    rw [RingHom.id_apply, MixedGradedHom.smul_app, LinearMap.smul_apply]
    change atDegree (successorFamily r (c • f).val) a i n e x = c • atDegree (successorFamily r f.val) a i n e x
    have ha (j q : ℤ) (h : j+r=q) :
        atDegree (c • f).val a j q h = c • atDegree f.val a j q h :=
      MixedGradedHom.smul_app c f a j q h
    simp only [successorFamily_apply, ha, LinearMap.smul_apply, Units.smul_def, smul_sub]
    change ((Y.complex a).d (i+r) _).hom _ - _ = _
    rw [map_smul, smul_comm]

theorem successor_apply (r : ℤ) (f : MixedGradedHom X Y r) (a : C.Obj)
    (i n : ℤ) (e : i+(r+1)=n) (x : (X.complex a).X i) :
    (successor X Y r f).app a i n e x =
      (Y.complex a).d (i+r) n (f.app a i (i+r) rfl x) -
        r.negOnePow • f.app a (i+1) n (by omega) ((X.complex a).d i (i+1) x) :=
  successorFamily_apply r f.val a i n e x

theorem successor_at (r : ℤ) (f : MixedGradedHom X Y r) (a : C.Obj)
    (i m n : ℤ) (h : i+r=m) (e : i+(r+1)=n) (x : (X.complex a).X i) :
    (successor X Y r f).app a i n e x =
      (Y.complex a).d m n (f.app a i m h x) -
        r.negOnePow • f.app a (i+1) n (by omega) ((X.complex a).d i (i+1) x) := by
  subst m
  exact successor_apply r f a i n e x

private theorem d_d_apply (K : _root_.DerivedFormalization.ModuleCochain.{u,p} k)
    (i j n : ℤ) (x : K.X i) : K.d j n (K.d i j x) = 0 := by
  rw [← ModuleCat.comp_apply, K.d_comp_d]
  rfl

private theorem successor_sq (r : ℤ) (f : MixedGradedHom X Y r) :
    successor X Y (r+1) (successor X Y r f) = 0 := by
  apply MixedGradedHom.ext
  intro a i n e x
  have hn : n = (i+r+1)+1 := by omega
  subst hn
  rw [MixedGradedHom.zero_app, LinearMap.zero_apply,
    successor_at (r+1) _ a i ((i+r)+1) _ (by omega) (by omega),
    successor_apply r f a i ((i+r)+1) (by omega),
    successor_at r f a (i+1) ((i+r)+1) _ (by omega) (by omega)]
  change ((Y.complex a).d _ _).hom (_ - _) - _ = _
  simp only [map_sub, Units.smul_def, map_zsmul, d_d_apply, LinearMap.map_zero,
    smul_zero, sub_zero, zero_sub, Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

/-- The Hom complex for modules with possibly different coefficient universes. -/
@[reducible] def mixedHomComplex (X : RightModule.{u,v,w,p} C) (Y : RightModule.{u,v,w,q} C) :
    _root_.DerivedFormalization.ModuleCochain.{u,max w p q} k where
  X r := ModuleCat.of k (MixedGradedHom X Y r)
  d r s := if h : r+1=s then h ▸ ModuleCat.ofHom (successor X Y r) else 0
  shape r s h := by
    have h' : ¬ r+1=s := h
    simp [h']
  d_comp_d' r s t h e := by
    change r+1=s at h
    change s+1=t at e
    subst s t
    simp only [dite_true]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (successor_sq (X := X) (Y := Y) r)

theorem mixedHomComplex_d (r : ℤ) (f : MixedGradedHom X Y r) :
    (mixedHomComplex X Y).d r (r+1) f = successor X Y r f := by
  simp only [mixedHomComplex, dite_true]
  rfl

end MixedHom

section Models

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
variable (T : bimodule A B)

/-- A tensor functor together with its identification with the balanced quotient. -/
structure TensorModel where
  functor : RightDGModuleModel A ⥤ RightModule.{u,v,z,max vA v w} B
  degree : ∀ M b n, Degree T M b n ≃ₗ[k] ((functor.obj M).complex b).X n
  d_tmul (M : RightDGModuleModel A) (a : A.Obj) (b : B.Obj) (i j n : ℤ) (h : i+j=n)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    ((functor.obj M).complex b).d n (n+1) (degree M b n (tmul T M b a i j n h m t)) =
      degree M b (n+1) (tmul T M b a (i+1) j (n+1) (by omega) ((M.complex a).d i (i+1) m) t) +
      i.negOnePow • degree M b (n+1) (tmul T M b a i (j+1) (n+1) (by omega) m
        (((T.obj a).complex b).d j (j+1) t))
  act_tmul (M : RightDGModuleModel A) (a : A.Obj) {b c : B.Obj} (i j n l q : ℤ)
      (h : i+j=n) (e : n+l=q) (m : (M.complex a).X i)
      (t : ((T.obj a).complex c).X j) (f : (B.hom b c).X l) :
    (functor.obj M).act n l q e (degree M c n (tmul T M c a i j n h m t)) f =
      degree M b q (tmul T M b a i (j+l) q (by omega) m ((T.obj a).act j l (j+l) rfl t f))
  map_tmul {M M' : RightDGModuleModel A} (f : M ⟶ M') (a : A.Obj) (b : B.Obj)
      (i j n : ℤ) (h : i+j=n) (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    ((functor.map f).app b).f n (degree M b n (tmul T M b a i j n h m t)) =
      degree M' b n (tmul T M' b a i j n h ((f.app a).f i m) t)

/-- An internal Hom functor with its precomposition action and its maps in the target. -/
structure InternalHomModel where
  functor : RightDGModuleModel B ⥤ RightModule.{u,vA,w,max v z} A
  objectwise : ∀ N a, homComplex (T.obj a) N ≅ (functor.obj N).complex a
  action (N : RightDGModuleModel B) {a a' : A.Obj} (i j n : ℤ) (h : i+j=n)
      (g : gradedHom (T.obj a') N i) (f : (A.hom a a').X j) :
    (functor.obj N).act i j n h ((objectwise N a').hom.f i g) f =
      (objectwise N a).hom.f n ((dgModuleCategory B).comp i j n h g ((T.map a a').f j f))
  map {N N' : RightDGModuleModel B} (f : N ⟶ N') (a : A.Obj) (i : ℤ)
      (g : gradedHom (T.obj a) N i) :
    ((functor.map f).app a).f i ((objectwise N a).hom.f i g) =
      (objectwise N' a).hom.f i ((dgModuleCategory B).comp 0 i i (zero_add i) (ofStrict f) g)

end Models

section Naturality

variable {C : DGCategoryModel.{u,v,w} k}
variable {X X' : RightModule.{u,v,w,p} C} {Y Y' : RightModule.{u,v,w,q} C}
variable {r : ℤ}

/-- Precomposition by a closed degree-zero map. -/
def precompose (f : X' ⟶ X) (g : MixedGradedHom X Y r) : MixedGradedHom X' Y r :=
  MixedGradedHom.mk (fun a i n h => (g.app a i n h).comp ((f.app a).f i).hom) (by
    intro a b i j n ir nr h hi hn x z
    change g.app a n nr hn ((f.app a).f n (X'.act i j n h x z)) =
      Y.act ir j nr (by omega) (g.app b i ir hi ((f.app b).f i x)) z
    rw [f.comm_act, g.comm_act i j n ir nr h hi hn])

/-- Postcomposition by a closed degree-zero map. -/
def postcompose (f : Y ⟶ Y') (g : MixedGradedHom X Y r) : MixedGradedHom X Y' r :=
  MixedGradedHom.mk (fun a i n h => ((f.app a).f n).hom.comp (g.app a i n h)) (by
    intro a b i j n ir nr h hi hn x z
    change (f.app a).f nr (g.app a n nr hn (X.act i j n h x z)) =
      Y'.act ir j nr (by omega) ((f.app b).f ir (g.app b i ir hi x)) z
    rw [g.comm_act i j n ir nr h hi hn, f.comm_act])

theorem precompose_apply (f : X' ⟶ X) (g : MixedGradedHom X Y r)
    (a : C.Obj) (i n : ℤ) (h : i+r=n) (x : (X'.complex a).X i) :
    (precompose f g).app a i n h x = g.app a i n h ((f.app a).f i x) := by
  subst n
  rfl

theorem postcompose_apply (f : Y ⟶ Y') (g : MixedGradedHom X Y r)
    (a : C.Obj) (i n : ℤ) (h : i+r=n) (x : (X.complex a).X i) :
    (postcompose f g).app a i n h x = (f.app a).f n (g.app a i n h x) := by
  subst n
  rfl

/-- View an ordinary strict map in the mixed coefficient model. -/
def asMixedMap {M N : RightDGModuleModel C} (f : M ⟶ N) : asMixed M ⟶ asMixed N :=
  ⟨f.app, f.comm_act⟩

end Naturality

section SignedAdjunction

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
variable {T : bimodule A B}
variable (L : TensorModel T) (G : InternalHomModel T)

/-- The two complexes in the signed correspondence, formed over the original categories. -/
abbrev LeftHom (M : RightDGModuleModel A) (N : RightDGModuleModel B) :=
  mixedHomComplex (L.functor.obj M) (asMixed N)

abbrev RightHom (M : RightDGModuleModel A) (N : RightDGModuleModel B) :=
  mixedHomComplex (asMixed M) (G.functor.obj N)

abbrev CurryFamily :=
  ∀ M N, LeftHom L M N ≅ RightHom G M N

/-- The natural complex isomorphism with no sign in its evaluation formula. -/
structure CurryLaws (E : CurryFamily L G) : Prop where
  apply_tmul (M : RightDGModuleModel A) (N : RightDGModuleModel B) (r : ℤ)
      (F : (LeftHom L M N).X r) (a : A.Obj) (b : B.Obj) (i j n s q : ℤ)
      (e : i+j=n) (h : i+r=s) (h' : j+s=q)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    component ((G.objectwise N a).inv.f s (MixedGradedHom.app ((E M N).hom.f r F) a i s h m))
        b j q h' t =
      MixedGradedHom.app F b n q (by omega) (L.degree M b n (tmul T M b a i j n e m t))
  natural_source {M M' : RightDGModuleModel A} (f : M' ⟶ M) (N : RightDGModuleModel B)
      (r : ℤ) (F : (LeftHom L M N).X r) :
    (E M' N).hom.f r (precompose (L.functor.map f) F) =
      precompose (asMixedMap f) ((E M N).hom.f r F)
  natural_target (M : RightDGModuleModel A) {N N' : RightDGModuleModel B} (f : N ⟶ N')
      (r : ℤ) (F : (LeftHom L M N).X r) :
    (E M N').hom.f r (postcompose (asMixedMap f) F) =
      postcompose (G.functor.map f) ((E M N).hom.f r F)

def SignedAdjunction : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,vA,w} k)
    (B : DGCategoryModel.{u,v,z} k) (T : bimodule A B),
    ∃ (L : TensorModel T) (G : InternalHomModel T) (E : CurryFamily L G), CurryLaws L G E

end SignedAdjunction

section StrictAdjunction

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B}
variable (L : TensorModel T) (G : InternalHomModel T)

/-- The underlying module functors in an ambient universe containing both object sets. -/
abbrev ordinaryTensor : RightDGModuleModel A ⥤ RightDGModuleModel B :=
  L.functor ⋙ RightModule.toOrdinary

abbrev ordinaryHom : RightDGModuleModel B ⥤ RightDGModuleModel A :=
  G.functor ⋙ RightModule.toOrdinary

abbrev OrdinaryCurryFamily :=
  ∀ M N, homComplex ((ordinaryTensor.{u,v,w,z} L).obj M) N ≅ homComplex M ((ordinaryHom.{u,v,w,z} G).obj N)

/-- The ordinary adjunction is the degree-zero part of the complex adjunction.
The bundled adjunction includes both triangle identities. -/
structure StrictLaws (E : OrdinaryCurryFamily.{u,v,w,z} L G) (adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G) : Prop where
  apply_tmul (M : RightDGModuleModel A) (N : RightDGModuleModel B) (r : ℤ)
      (F : gradedHom ((ordinaryTensor.{u,v,w,z} L).obj M) N r)
      (a : A.Obj) (b : B.Obj) (i j n s q : ℤ) (e : i+j=n) (h : i+r=s) (h' : j+s=q)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    component ((G.objectwise N a).inv.f s (component ((E M N).hom.f r F) a i s h m))
        b j q h' t =
      component F b n q (by omega) (L.degree M b n (tmul T M b a i j n e m t))
  homEquiv (M : RightDGModuleModel A) (N : RightDGModuleModel B) (f : (ordinaryTensor.{u,v,w,z} L).obj M ⟶ N) :
    ofStrict (adj.homEquiv M N f) = (E M N).hom.f 0 (ofStrict f)
  unit (M : RightDGModuleModel A) (a : A.Obj) (b : B.Obj) (i j n : ℤ) (h : i+j=n)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    component ((G.objectwise ((ordinaryTensor.{u,v,w,z} L).obj M) a).inv.f i
      (((adj.unit.app M).app a).f i m)) b j n (by omega) t =
      L.degree M b n (tmul T M b a i j n h m t)
  counit (N : RightDGModuleModel B) (a : A.Obj) (b : B.Obj) (i j n : ℤ) (h : i+j=n)
      (g : gradedHom (T.obj a) N i) (t : ((T.obj a).complex b).X j) :
    ((adj.counit.app N).app b).f n
      (L.degree ((ordinaryHom.{u,v,w,z} G).obj N) b n (tmul T ((ordinaryHom.{u,v,w,z} G).obj N) b a i j n h
        ((G.objectwise N a).hom.f i g) t)) =
      component g b j n (by omega) t

def UnderivedAdjunction : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w z,w} k)
    (B : DGCategoryModel.{u,max v w z,z} k) (T : bimodule A B),
    ∃ (L : TensorModel T) (G : InternalHomModel T) (E : OrdinaryCurryFamily.{u,v,w,z} L G)
      (adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G), StrictLaws.{u,v,w,z} L G E adj

end StrictAdjunction

section Representable

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}

/-- A right dg-module isomorphism allowing different coefficient universes. -/
structure ModuleEquiv {C : DGCategoryModel.{u,v,w} k}
    (X : RightModule.{u,v,w,p} C) (Y : RightModule.{u,v,w,q} C) where
  degree (a : C.Obj) (n : ℤ) : (X.complex a).X n ≃ₗ[k] (Y.complex a).X n
  comm_d (a : C.Obj) (n : ℤ) (x : (X.complex a).X n) :
    degree a (n+1) ((X.complex a).d n (n+1) x) = (Y.complex a).d n (n+1) (degree a n x)
  comm_act {a b : C.Obj} (i j n : ℤ) (h : i+j=n) (x : (X.complex b).X i) (u : (C.hom a b).X j) :
    degree a n (X.act i j n h x u) = Y.act i j n h (degree b i x) u

/-- Evaluation on a tensor of a representable has inverse tensoring with its identity. -/
def RepresentableTensor : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,vA,w} k)
    (B : DGCategoryModel.{u,v,z} k) (T : bimodule A B),
    ∃ L : TensorModel T, ∀ a : A.Obj,
      let M := Yoneda.representable a
      ∃ E : ModuleEquiv (L.functor.obj M) (asMixed (T.obj a)),
        (∀ (b : B.Obj) (c : A.Obj) (i j n : ℤ) (e : i+j=n)
            (f : (A.hom c a).X i) (t : ((T.obj c).complex b).X j),
          E.degree b n (L.degree M b n (tmul T M b c i j n e f t)) = left T b i j n e f t) ∧
        (∀ (b : B.Obj) (n : ℤ) (t : ((T.obj a).complex b).X n),
          (E.degree b n).symm t = L.degree M b n (tmul T M b a 0 n n (zero_add n) (A.id a) t))

end Representable

section CoefficientTransport

universe t

open CoefficientLift (liftCategory liftModule liftMap)

/-- Restrict just the arrows along the coefficient lift, leaving all terms untouched. -/
@[reducible] def restrictLifted {C : DGCategoryModel.{u,v,w} k}
    (X : RightModule.{u,max v t,w,p} (liftCategory.{u,v,w,t} C)) :
    RightModule.{u,v,w,p} C where
  complex := X.complex
  act i j n h := (X.act i j n h).compl₂ ULift.moduleEquiv.symm.toLinearMap
  act_id a i x := X.act_id a i x
  act_assoc i j l x f g := X.act_assoc i j l x (ULift.up f) (ULift.up g)
  leibniz i j n h x f := X.leibniz i j n h x (ULift.up f)

/-- Transport the arrows of a mixed module without changing any coefficient terms. -/
@[reducible] def extendLifted {C : DGCategoryModel.{u,v,w} k}
    (X : RightModule.{u,v,w,p} C) :
    RightModule.{u,max v t,w,p} (liftCategory.{u,v,w,t} C) where
  complex := X.complex
  act i j n h := (X.act i j n h).compl₂ ULift.moduleEquiv.toLinearMap
  act_id a i x := X.act_id a i x
  act_assoc i j l x f g := X.act_assoc i j l x f.down g.down
  leibniz i j n h x f := X.leibniz i j n h x f.down

/-- Rewrite an equivalence over the original arrows as one over the lifted arrows. -/
def ModuleEquiv.overLift {C : DGCategoryModel.{u,v,w} k}
    {X : RightModule.{u,v,w,p} C}
    {Y : RightModule.{u,max v t,w,q} (liftCategory.{u,v,w,t} C)}
    (e : ModuleEquiv X (restrictLifted.{u,v,w,q,t} Y)) :
    ModuleEquiv (extendLifted.{u,v,w,p,t} X) Y where
  degree := e.degree
  comm_d := e.comm_d
  comm_act i j n h x f := e.comm_act i j n h x f.down

end CoefficientTransport

section AmbientAdjunction

universe t

open CoefficientLift (liftCategory liftModule liftMap)

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
variable {T : bimodule A B}


variable {S : bimodule (liftCategory.{u,vA,w,max v w z t} A) (liftCategory.{u,v,z,max vA w z t} B)}
variable (K : ∀ a, ModuleEquiv (asMixed (T.obj a)) ((restrictLifted.{u,v,z,max vA v w z t,max vA w z t}) (asMixed (S.obj a))))

/-- The given bimodule is transported using its original object set and homogeneous action. -/
structure BimoduleLiftLaws : Prop where
  obj_eq (a : A.Obj) : S.obj a = (liftModule.{u,v,z,max vA w z t}) (T.obj a)
  term_up (a : A.Obj) (b : B.Obj) (n : ℤ) (x : ((T.obj a).complex b).X n) :
    HEq (K a |>.degree b n x) (ULift.up.{max vA w z t} x)
  left_action (b : B.Obj) {a a' : A.Obj} (i j n : ℤ) (h : i+j=n)
      (f : (A.hom a a').X i) (x : ((T.obj a).complex b).X j) :
    (K a').degree b n (left T b i j n h f x) =
      left S b i j n h (ULift.up f) ((K a).degree b j x)

variable (L : TensorModel T) (G : InternalHomModel T)
variable (L' : TensorModel S) (G' : InternalHomModel S)


/-- Comparisons of the original mixed outputs with the actual ambient outputs.
The ambient right action is read on the original arrows via `ULift.up`. -/
structure OutputComparisons where
  tensor (M : RightDGModuleModel A) :
    ModuleEquiv (L.functor.obj M) ((restrictLifted.{u,v,z,max vA v w z t,max vA w z t}) (asMixed ((ordinaryTensor.{u,max vA v t,w,z} L').obj ((liftModule.{u,vA,w,max v w z t}) M))))
  hom (N : RightDGModuleModel B) :
    ModuleEquiv (G.functor.obj N) ((restrictLifted.{u,vA,w,max vA v w z t,max v w z t}) (asMixed ((ordinaryHom.{u,max vA v t,w,z} G').obj ((liftModule.{u,v,z,max vA w z t}) N))))
  tensor_tmul (M : RightDGModuleModel A) (b : B.Obj) (a : A.Obj)
      (i j n : ℤ) (h : i+j=n) (m : (M.complex a).X i) (x : ((T.obj a).complex b).X j) :
    (tensor M).degree b n (L.degree M b n (tmul T M b a i j n h m x)) =
      L'.degree ((liftModule.{u,vA,w,max v w z t}) M) b n (tmul S ((liftModule.{u,vA,w,max v w z t}) M) b a i j n h (ULift.up m) ((K a).degree b j x))
  hom_eval (N : RightDGModuleModel B) (a : A.Obj) (b : B.Obj)
      (r i n : ℤ) (h : i+r=n) (g : gradedHom (T.obj a) N r) (x : ((T.obj a).complex b).X i) :
    component ((G'.objectwise ((liftModule.{u,v,z,max vA w z t}) N) a).inv.f r
      ((hom N).degree a r ((G.objectwise N a).hom.f r g))) b i n h ((K a).degree b i x) =
        ULift.up (component g b i n h x)
  tensor_map {M P : RightDGModuleModel A} (f : M ⟶ P) (b : B.Obj) (n : ℤ)
      (x : ((L.functor.obj M).complex b).X n) :
    (tensor P).degree b n (((L.functor.map f).app b).f n x) =
      (((ordinaryTensor.{u,max vA v t,w,z} L').map ((liftMap.{u,vA,w,max v w z t}) f)).app b).f n ((tensor M).degree b n x)
  hom_map {N P : RightDGModuleModel B} (f : N ⟶ P) (a : A.Obj) (n : ℤ)
      (x : ((G.functor.obj N).complex a).X n) :
    (hom P).degree a n (((G.functor.map f).app a).f n x) =
      (((ordinaryHom.{u,max vA v t,w,z} G').map ((liftMap.{u,v,z,max vA w z t}) f)).app a).f n ((hom N).degree a n x)

variable {L G L' G'} {K}
variable (D : OutputComparisons.{u,v,w,vA,z,t} K L G L' G')

/-- The comparisons on the two Hom complexes commute with signed currying. -/
structure CurryComparison (E : CurryFamily L G)
    (E' : OrdinaryCurryFamily.{u,max vA v t,w,z} L' G') where
  source (M : RightDGModuleModel A) (N : RightDGModuleModel B) :
    ∀ r, (LeftHom L M N).X r ≃ₗ[k] gradedHom ((ordinaryTensor.{u,max vA v t,w,z} L').obj ((liftModule.{u,vA,w,max v w z t}) M)) ((liftModule.{u,v,z,max vA w z t}) N) r
  target (M : RightDGModuleModel A) (N : RightDGModuleModel B) :
    ∀ r, (RightHom G M N).X r ≃ₗ[k] gradedHom ((liftModule.{u,vA,w,max v w z t}) M) ((ordinaryHom.{u,max vA v t,w,z} G').obj ((liftModule.{u,v,z,max vA w z t}) N)) r
  source_eval (M : RightDGModuleModel A) (N : RightDGModuleModel B)
      (r : ℤ) (F : (LeftHom L M N).X r) (b : B.Obj) (i n : ℤ) (h : i+r=n)
      (x : ((L.functor.obj M).complex b).X i) :
    component (source M N r F) b i n h ((D.tensor M).degree b i x) =
      ULift.up (MixedGradedHom.app F b i n h x)
  target_eval (M : RightDGModuleModel A) (N : RightDGModuleModel B)
      (r : ℤ) (F : (RightHom G M N).X r) (a : A.Obj) (i n : ℤ) (h : i+r=n) (x : (M.complex a).X i) :
    component (target M N r F) a i n h (ULift.up x) =
      (D.hom N).degree a n (MixedGradedHom.app F a i n h x)
  source_d (M : RightDGModuleModel A) (N : RightDGModuleModel B)
      (r : ℤ) (F : (LeftHom L M N).X r) :
    source M N (r+1) ((LeftHom L M N).d r (r+1) F) =
      (homComplex ((ordinaryTensor.{u,max vA v t,w,z} L').obj ((liftModule.{u,vA,w,max v w z t}) M)) ((liftModule.{u,v,z,max vA w z t}) N)).d r (r+1) (source M N r F)
  target_d (M : RightDGModuleModel A) (N : RightDGModuleModel B)
      (r : ℤ) (F : (RightHom G M N).X r) :
    target M N (r+1) ((RightHom G M N).d r (r+1) F) =
      (homComplex ((liftModule.{u,vA,w,max v w z t}) M) ((ordinaryHom.{u,max vA v t,w,z} G').obj ((liftModule.{u,v,z,max vA w z t}) N))).d r (r+1) (target M N r F)
  curry (M : RightDGModuleModel A) (N : RightDGModuleModel B)
      (r : ℤ) (F : (LeftHom L M N).X r) :
    (E' ((liftModule.{u,vA,w,max v w z t}) M) ((liftModule.{u,v,z,max vA w z t}) N)).hom.f r (source M N r F) =
      target M N r ((E M N).hom.f r F)

/-- The unit and counit on the ambient categories have the original evaluation descriptions. -/
structure LiftedEvaluations (adj : (ordinaryTensor.{u,max vA v t,w,z} L') ⊣ (ordinaryHom.{u,max vA v t,w,z} G')) : Prop where
  unit (M : RightDGModuleModel A) (a : A.Obj) (b : B.Obj)
      (i j n : ℤ) (h : i+j=n) (m : (M.complex a).X i) (x : ((T.obj a).complex b).X j) :
    component ((G'.objectwise ((ordinaryTensor.{u,max vA v t,w,z} L').obj ((liftModule.{u,vA,w,max v w z t}) M)) a).inv.f i
      (((adj.unit.app ((liftModule.{u,vA,w,max v w z t}) M)).app a).f i (ULift.up m))) b j n (by omega) ((K a).degree b j x) =
        (D.tensor M).degree b n (L.degree M b n (tmul T M b a i j n h m x))
  counit (N : RightDGModuleModel B) (a : A.Obj) (b : B.Obj)
      (i j n : ℤ) (h : i+j=n) (g : gradedHom (T.obj a) N i) (x : ((T.obj a).complex b).X j) :
    ((adj.counit.app ((liftModule.{u,v,z,max vA w z t}) N)).app b).f n
      (L'.degree ((ordinaryHom.{u,max vA v t,w,z} G').obj ((liftModule.{u,v,z,max vA w z t}) N)) b n (tmul S ((ordinaryHom.{u,max vA v t,w,z} G').obj ((liftModule.{u,v,z,max vA w z t}) N)) b a i j n h
        ((D.hom N).degree a i ((G.objectwise N a).hom.f i g)) ((K a).degree b j x))) =
      ULift.up (component g b j n (by omega) x)

/-- The adjunction on the full module categories at every common coefficient bound. -/
def AmbientAdjunction : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,vA,w} k)
    (B : DGCategoryModel.{u,v,z} k) (T : bimodule A B),
    ∃ (S : bimodule (liftCategory.{u,vA,w,max v w z t} A) (liftCategory.{u,v,z,max vA w z t} B)) (K : ∀ a, ModuleEquiv (asMixed (T.obj a)) ((restrictLifted.{u,v,z,max vA v w z t,max vA w z t}) (asMixed (S.obj a))))
      (L : TensorModel T) (G : InternalHomModel T) (E : CurryFamily L G)
      (L' : TensorModel S) (G' : InternalHomModel S)
      (E' : OrdinaryCurryFamily.{u,max vA v t,w,z} L' G') (adj : (ordinaryTensor.{u,max vA v t,w,z} L') ⊣ (ordinaryHom.{u,max vA v t,w,z} G'))
      (D : OutputComparisons.{u,v,w,vA,z,t} K L G L' G'),
      BimoduleLiftLaws.{u,v,w,vA,z,t} K ∧ CurryLaws L G E ∧ StrictLaws.{u,max vA v t,w,z} L' G' E' adj ∧
        Nonempty (CurryComparison.{u,v,w,vA,z,t} D E E') ∧ LiftedEvaluations.{u,v,w,vA,z,t} D adj

end AmbientAdjunction

end Specs.DerivedFormalization.DG.BimoduleAdjunction
