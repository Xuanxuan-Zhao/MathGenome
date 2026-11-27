import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BalancedTensor

open CategoryTheory
open scoped Classical DirectSum TensorProduct

universe u v w z vA

namespace DerivedFormalization

/-- A dg bimodule, in the homogeneous right-linearity convention. -/
abbrev DGBimodule {k : Type u} [CommRing k] (A : DGCategory.{u,vA,w} k)
    (B : DGCategory.{u,v,z} k) :=
  Specs.DerivedFormalization.DG.BalancedTensor.bimodule A B

namespace DGBimodule

open Specs.DerivedFormalization.DG.BalancedTensor
open RightDGModule (GradedHom)

variable {k : Type u} [CommRing k]
variable {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
/-- Commutation with the differential in any pair of cochain degrees. -/
theorem _root_.Specs.DerivedFormalization.DG.BalancedTensor.CochainMap.comm_all
    {C : ModuleCochain.{u,vA} k} {D : ModuleCochain.{u,v} k}
    (f : CochainMap C D) (i j : ℤ) (x : C.X i) :
    f.f j (C.d i j x) = D.d i j (f.f i x) := by
  by_cases h : i+1=j
  · subst j
    exact f.comm i x
  · have hc : ¬ (ComplexShape.up ℤ).Rel i j := h
    rw [C.shape i j hc, D.shape i j hc]
    simp

section DGFunctor

variable {A₀ : DGCategory.{u,max v z,w} k}

/-- Interpret a bimodule as a bundled dg functor when the Hom universes agree. -/
def toDGFunctor (T : DGBimodule A₀ B) :
    DGFunctor A₀ (RightDGModule.dgCategory B) where
  obj := T.obj
  map a b := CochainComplex.ofHom (fun i => ModuleCat.ofHom ((T.map a b).f i)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact fun x => ((T.map a b).comm i x).symm)
  map_id := T.map_id
  map_comp := T.map_comp

/-- Regard a bundled dg functor to dg modules as a bimodule. -/
def ofDGFunctor (F : DGFunctor A₀ (RightDGModule.dgCategory B)) : DGBimodule A₀ B where
  obj := F.obj
  map a b := ⟨fun i => ((F.map a b).f i).hom, fun i x =>
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((F.map a b).comm i (i+1)).symm) x⟩
  map_id := F.map_id
  map_comp := F.map_comp

/-- Both translations preserve the object assignment and all homogeneous maps. -/
def dgFunctorEquiv : DGBimodule A₀ B ≃ DGFunctor A₀ (RightDGModule.dgCategory B) where
  toFun := toDGFunctor
  invFun := ofDGFunctor
  left_inv T := by
    cases T
    rfl
  right_inv F := by
    cases F with
    | mk obj map map_id map_comp =>
      have hm : (toDGFunctor (ofDGFunctor ⟨obj, map, map_id, map_comp⟩)).map = map :=
        funext fun a => funext fun b => HomologicalComplex.hom_ext _ _ fun _ => rfl
      change DGFunctorModel.mk obj _ _ _ = DGFunctorModel.mk obj map map_id map_comp
      congr

end DGFunctor

variable (T : DGBimodule A B) (M : RightDGModule A)

noncomputable section

/-- The bilinear map of homogeneous pure tensors into the balanced quotient. -/
def tensorPair (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n) :
    (M.complex a).X i →ₗ[k] ((T.obj a).complex b).X j →ₗ[k] Degree T M b n :=
  (TensorProduct.mk k _ _).compr₂
    ((Balance T M b n).mkQ.comp
      (DirectSum.lof k (Index A.Obj n) (Summand T M b n) ⟨a, ⟨(i,j), h⟩⟩))

theorem tensorPair_apply (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tensorPair T M b a i j n h m t = tmul T M b a i j n h m t := rfl

/-- Balancing in any choices of the intermediate and total degrees. -/
theorem tmul_balance (b : B.Obj) {a a' : A.Obj} (i l j il lj n : ℤ)
    (hi : i+l=il) (hj : l+j=lj) (h : il+j=n)
    (m : (M.complex a').X i) (f : (A.hom a a').X l) (t : ((T.obj a).complex b).X j) :
    tmul T M b a il j n h (M.act i l il hi m f) t =
      tmul T M b a' i lj n (by omega) m (left T b l j lj hj f t) := by
  subst il lj
  apply sub_eq_zero.mp
  rw [tmul, tmul, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨a, a', i, l, j, h, m, f, t, rfl⟩

section Lift

variable {P : Type*} [AddCommGroup P] [Module k P]
variable {b : B.Obj} {n : ℤ}

private def rawLift
    (F : ∀ (a : A.Obj) (i j : ℤ) (_ : i+j=n),
      (M.complex a).X i →ₗ[k] ((T.obj a).complex b).X j →ₗ[k] P) :
    Raw T M b n →ₗ[k] P :=
  DirectSum.toModule k (Index A.Obj n) P fun ⟨a, ⟨(i,j), h⟩⟩ =>
    TensorProduct.lift (F a i j h)

private theorem rawLift_tmul
    (F : ∀ (a : A.Obj) (i j : ℤ) (_ : i+j=n),
      (M.complex a).X i →ₗ[k] ((T.obj a).complex b).X j →ₗ[k] P)
    (a : A.Obj) (i j : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    rawLift T M F (rawTmul T M b a i j n h m t) = F a i j h m t := by
  simp [rawLift, rawTmul]

/-- The degreewise universal property of the balanced quotient. -/
def lift
    (F : ∀ (a : A.Obj) (i j : ℤ) (_ : i+j=n),
      (M.complex a).X i →ₗ[k] ((T.obj a).complex b).X j →ₗ[k] P)
    (hf : ∀ (a a' : A.Obj) (i l j : ℤ) (h : i+l+j=n)
      (m : (M.complex a').X i) (f : (A.hom a a').X l)
      (t : ((T.obj a).complex b).X j),
      F a (i+l) j h (M.act i l (i+l) rfl m f) t =
        F a' i (l+j) (by omega) m (left T b l j (l+j) rfl f t)) :
    Degree T M b n →ₗ[k] P :=
  (Balance T M b n).liftQ (rawLift T M F) (by
    apply Submodule.span_le.mpr
    rintro x ⟨a, a', i, l, j, h, m, f, t, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, rawLift_tmul, rawLift_tmul,
      hf, sub_self])

@[simp] theorem lift_tmul (F) (hf) (a : A.Obj) (i j : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    lift (P := P) T M F hf (tmul T M b a i j n h m t) = F a i j h m t := by
  exact (Submodule.liftQ_apply _ _ _).trans (rawLift_tmul T M F a i j h m t)

/-- Homogeneous pure tensors determine maps out of each degree. -/
theorem linearMap_ext {F G : Degree T M b n →ₗ[k] P}
    (h : ∀ (a : A.Obj) (i j : ℤ) (e : i+j=n)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j),
      F (tmul T M b a i j n e m t) = G (tmul T M b a i j n e m t)) : F = G := by
  refine (Balance T M b n).quot_hom_ext F G ?_
  have eq : F.comp (Balance T M b n).mkQ = G.comp (Balance T M b n).mkQ := by
    apply DirectSum.linearMap_ext
    rintro ⟨a, ⟨⟨i,j⟩, e⟩⟩
    apply TensorProduct.ext'
    exact h a i j e
  exact fun x => LinearMap.congr_fun eq x

end Lift

theorem left_leibniz (b : B.Obj) {a a' : A.Obj} (l j q : ℤ) (e : l+j=q)
    (f : (A.hom a a').X l) (t : ((T.obj a).complex b).X j) :
    ((T.obj a').complex b).d q (q+1) (left T b l j q e f t) =
      left T b (l+1) j (q+1) (by omega) ((A.hom a a').d l (l+1) f) t +
      l.negOnePow • left T b l (j+1) (q+1) (by omega) f
        (((T.obj a).complex b).d j (j+1) t) := by
  have eqDegree : j+l=q := by omega
  subst eqDegree
  have comm := (T.map a a').comm l f
  have eq := congrArg
    (fun g : GradedHom (T.obj a) (T.obj a') (l+1) => g.app b j (j+l+1) (by omega) t) comm
  change left T b (l+1) j (j+l+1) (by omega) ((A.hom a a').d l (l+1) f) t =
    GradedHom.app ((RightDGModule.homComplex (T.obj a) (T.obj a')).d l (l+1)
      ((T.map a a').f l f)) b j (j+l+1) (by omega) t at eq
  rw [RightDGModule.differentialFormula] at eq
  exact (eq_sub_iff_add_eq.mp eq).symm

theorem left_comm_act {b c : B.Obj} {a a' : A.Obj} (l j p lj jp q : ℤ)
    (e : l+j=lj) (h : j+p=jp) (hq : lj+p=q)
    (f : (A.hom a a').X l) (t : ((T.obj a).complex c).X j) (g : (B.hom b c).X p) :
    (T.obj a').act lj p q hq (left T c l j lj e f t) g =
      left T b l jp q (by omega) f ((T.obj a).act j p jp h t g) :=
  (GradedHom.comm_act ((T.map a a').f l f) j p jp lj q h (by omega) (by omega) t g).symm

section Hom

open Specs.DerivedFormalization.DG.HomComplex (ofStrict)

variable (N : RightDGModule B)

/-- The internal Hom into a right module, with right action by precomposition. -/
@[reducible] def mixedHomModule : RightModule.{u,vA,w,max v z} A where
  complex a := RightDGModule.homComplex (T.obj a) N
  act {a b} i j n h :=
    ((RightDGModule.dgCategory B).comp i j n h).compl₂ ((T.map a b).f j)
  act_id a i g := by
    change (RightDGModule.dgCategory B).comp i 0 i _ g ((T.map a a).f 0 (A.id a)) = g
    rw [T.map_id, (RightDGModule.dgCategory B).toData.comp_id]
  act_assoc {a b c} i j l x f g := by
    change (RightDGModule.dgCategory B).comp (i+j) l _ _
      ((RightDGModule.dgCategory B).comp i j _ _ x ((T.map b c).f j f)) ((T.map a b).f l g) =
      (RightDGModule.dgCategory B).comp i (j+l) _ _ x
        ((T.map a c).f (j+l) (A.comp j l (j+l) rfl f g))
    rw [T.map_comp, (RightDGModule.dgCategory B).toData.assoc]
  leibniz {a b} i j n h g f := by
    change ((RightDGModule.dgCategory B).hom (T.obj a) N).d n (n+1)
      ((RightDGModule.dgCategory B).comp i j n h g ((T.map a b).f j f)) =
      (RightDGModule.dgCategory B).comp (i+1) j (n+1) _
        ((RightDGModule.homComplex (T.obj b) N).d i (i+1) g) ((T.map a b).f j f) +
      i.negOnePow • (RightDGModule.dgCategory B).comp i (j+1) (n+1) _ g
        ((T.map a b).f (j+1) ((A.hom a b).d j (j+1) f))
    rw [(RightDGModule.dgCategory B).toData.leibniz]
    rw [← (T.map a b).comm j f]

theorem mixedHomModule_act {a b : A.Obj} (i j n : ℤ) (h : i+j=n)
    (g : (RightDGModule.homComplex (T.obj b) N).X i) (f : (A.hom a b).X j) :
    (mixedHomModule T N).act i j n h g f =
      (RightDGModule.dgCategory B).comp i j n h g ((T.map a b).f j f) := rfl

private def postcompose {N P : RightDGModule B} (f : N ⟶ P) (a : A.Obj) (i : ℤ) :
    (RightDGModule.homComplex (T.obj a) N).X i →ₗ[k]
      (RightDGModule.homComplex (T.obj a) P).X i :=
  (RightDGModule.dgCategory B).comp 0 i i (zero_add i) (ofStrict f)

private theorem comp_zero_assoc {X Y Z W : RightDGModule B} (i j n : ℤ) (h : i+j=n)
    (f : GradedHom Z W 0) (g : GradedHom Y Z i) (v : GradedHom X Y j) :
    (RightDGModule.dgCategory B).comp 0 n n (zero_add n) f
      ((RightDGModule.dgCategory B).comp i j n h g v) =
    (RightDGModule.dgCategory B).comp i j n h
      ((RightDGModule.dgCategory B).comp 0 i i (zero_add i) f g) v := by
  apply GradedHom.ext
  intro a p q e
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [RightDGModule.compositionFormula 0 n n _ f _ a p q q e (add_zero q),
    RightDGModule.compositionFormula i j n h g v a p (p+j) q rfl (by omega),
    RightDGModule.compositionFormula i j n h _ v a p (p+j) q rfl (by omega),
    RightDGModule.compositionFormula 0 i i _ f g a (p+j) q q (by omega) (add_zero q)]

/-- The strict map of internal Hom modules given by postcomposition. -/
def mixedHomMap {N P : RightDGModule B} (f : N ⟶ P) : mixedHomModule T N ⟶ mixedHomModule T P where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (postcompose T f a i)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change ((RightDGModule.dgCategory B).hom (T.obj a) P).d i (i+1)
      ((RightDGModule.dgCategory B).comp 0 i i _ (ofStrict f) g) =
      (RightDGModule.dgCategory B).comp 0 (i+1) (i+1) _ (ofStrict f)
        ((RightDGModule.homComplex (T.obj a) N).d i (i+1) g)
    have hd : (RightDGModule.homComplex N P).d 0 1 (ofStrict f) = 0 :=
      (RightDGModule.strictCycle f).property
    rw [(RightDGModule.dgCategory B).toData.leibniz]
    change (RightDGModule.dgCategory B).comp (0+1) i (i+1) _ _ g + _ = _
    rw [hd, map_zero, LinearMap.zero_apply, zero_add, Int.negOnePow_zero, one_smul])
  comm_act := by
    intro a b i j n h g v
    change (RightDGModule.dgCategory B).comp 0 n n _ (ofStrict f)
      ((RightDGModule.dgCategory B).comp i j n h g ((T.map a b).f j v)) =
      (RightDGModule.dgCategory B).comp i j n h
        ((RightDGModule.dgCategory B).comp 0 i i _ (ofStrict f) g) ((T.map a b).f j v)
    exact comp_zero_assoc i j n h (ofStrict f) g ((T.map a b).f j v)

theorem mixedHomMap_apply {N P : RightDGModule B} (f : N ⟶ P) (a : A.Obj) (i : ℤ)
    (g : (RightDGModule.homComplex (T.obj a) N).X i) :
    ((mixedHomMap T f).app a).f i g =
      (RightDGModule.dgCategory B).comp 0 i i (zero_add i) (ofStrict f) g := rfl

/-- The internal Hom functor on strict module maps. -/
def mixedHomFunctor : RightDGModule B ⥤ RightModule.{u,vA,w,max v z} A where
  obj := mixedHomModule T
  map := mixedHomMap T
  map_id N := by
    apply RightModule.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    exact (RightDGModule.dgCategory B).toData.id_comp i g
  map_comp {N P Q} f g := by
    apply RightModule.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change (RightDGModule.dgCategory B).comp 0 i i _ (ofStrict (f ≫ g)) h =
      (RightDGModule.dgCategory B).comp 0 i i _ (ofStrict g)
        ((RightDGModule.dgCategory B).comp 0 i i _ (ofStrict f) h)
    have hg : (RightDGModule.dgCategory B).comp 0 0 0 rfl (ofStrict g) (ofStrict f) =
        ofStrict (f ≫ g) := by
      apply Subtype.ext
      exact funext fun b => (CochainComplex.HomComplex.Cochain.ofHom_comp (f.app b) (g.app b)).symm
    rw [← hg]
    exact (comp_zero_assoc 0 i i (zero_add i) (ofStrict g) (ofStrict f) h).symm

theorem homConstruction : HomConstruction.{u,v,w,z,vA} := by
  intro k _ A B T
  exact ⟨mixedHomFunctor T, fun _ _ => Iso.refl _, fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

end Hom

section Tensor

private theorem tmul_add_left {b : B.Obj} {a : A.Obj} {i j n : ℤ} (e : i+j=n)
    (m m' : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tmul T M b a i j n e (m+m') t =
      tmul T M b a i j n e m t + tmul T M b a i j n e m' t := by
  simp only [← tensorPair_apply, map_add, LinearMap.add_apply]

private theorem tmul_add_right {b : B.Obj} {a : A.Obj} {i j n : ℤ} (e : i+j=n)
    (m : (M.complex a).X i) (t t' : ((T.obj a).complex b).X j) :
    tmul T M b a i j n e m (t+t') =
      tmul T M b a i j n e m t + tmul T M b a i j n e m t' := by
  simp only [← tensorPair_apply, map_add]

private theorem tmul_units_left {b : B.Obj} {a : A.Obj} {i j n : ℤ} (e : i+j=n)
    (s : ℤˣ) (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tmul T M b a i j n e (s • m) t = s • tmul T M b a i j n e m t := by
  simp only [← tensorPair_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]

private theorem tmul_units_right {b : B.Obj} {a : A.Obj} {i j n : ℤ} (e : i+j=n)
    (s : ℤˣ) (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tmul T M b a i j n e m (s • t) = s • tmul T M b a i j n e m t := by
  simp only [← tensorPair_apply, Units.smul_def, map_zsmul]

private def differentialPair (b : B.Obj) (n : ℤ) (a : A.Obj) (i j : ℤ) (e : i+j=n) :
    (M.complex a).X i →ₗ[k] ((T.obj a).complex b).X j →ₗ[k] Degree T M b (n+1) :=
  (tensorPair T M b a (i+1) j (n+1) (by omega)).comp ((M.complex a).d i (i+1)).hom +
    i.negOnePow • (tensorPair T M b a i (j+1) (n+1) (by omega)).compl₂
      (((T.obj a).complex b).d j (j+1)).hom

private theorem differentialPair_apply (b : B.Obj) (n : ℤ) (a : A.Obj) (i j : ℤ) (e : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    differentialPair T M b n a i j e m t =
      tmul T M b a (i+1) j (n+1) (by omega) ((M.complex a).d i (i+1) m) t +
      i.negOnePow • tmul T M b a i (j+1) (n+1) (by omega) m
        (((T.obj a).complex b).d j (j+1) t) := rfl

private def tensorD (b : B.Obj) (n : ℤ) : Degree T M b n →ₗ[k] Degree T M b (n+1) :=
  lift T M (differentialPair T M b n) (by
    intro a a' i l j h m f t
    rw [differentialPair_apply, differentialPair_apply, M.leibniz, left_leibniz,
      tmul_add_left, tmul_add_right, tmul_units_left, tmul_units_right]
    rw [tmul_balance T M b (i+1) l j (i+l+1) (l+j) (n+1) (by omega) rfl (by omega),
      tmul_balance T M b i (l+1) j (i+l+1) (l+j+1) (n+1) (by omega) (by omega) (by omega),
      tmul_balance T M b i l (j+1) (i+l) (l+j+1) (n+1) rfl (by omega) (by omega),
      Int.negOnePow_add, mul_smul, smul_add]
    abel)

private theorem tensorD_tmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tensorD T M b n (tmul T M b a i j n h m t) =
      tmul T M b a (i+1) j (n+1) (by omega) ((M.complex a).d i (i+1) m) t +
      i.negOnePow • tmul T M b a i (j+1) (n+1) (by omega) m
        (((T.obj a).complex b).d j (j+1) t) := by
  rw [tensorD, lift_tmul, differentialPair_apply]

private theorem d_d_apply (C : ModuleCochain.{u,v} k) (i j l : ℤ) (x : C.X i) :
    C.d j l (C.d i j x) = 0 := by
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (C.d_comp_d i j l)) x
  exact h

private theorem tensorD_sq (b : B.Obj) (n : ℤ) :
    (tensorD T M b (n+1)).comp (tensorD T M b n) = 0 := by
  apply linearMap_ext T M
  intro a i j h m t
  rw [LinearMap.comp_apply, tensorD_tmul, map_add, Units.smul_def, map_zsmul,
    tensorD_tmul, tensorD_tmul, d_d_apply, d_d_apply]
  simp only [← tensorPair_apply, map_zero, LinearMap.zero_apply,
    zero_add, smul_zero, add_zero, Units.smul_def]
  rw [Int.negOnePow_succ, Units.val_neg, neg_smul, neg_add_cancel]

private def actionPair {b c : B.Obj} (n p q : ℤ) (hq : n+p=q)
    (a : A.Obj) (i j : ℤ) (h : i+j=n) :
    (M.complex a).X i →ₗ[k] ((T.obj a).complex c).X j →ₗ[k]
      (B.hom b c).X p →ₗ[k] Degree T M b q :=
  LinearMap.mk₂ k
    (fun m t => (tensorPair T M b a i (j+p) q (by omega) m).comp
      ((T.obj a).act j p (j+p) rfl t))
    (by intros; simp [LinearMap.add_comp])
    (by intros; ext x; simp)
    (by intros; simp [LinearMap.comp_add])
    (by intros; ext x; simp)

private theorem actionPair_apply {b c : B.Obj} (n p q : ℤ) (hq : n+p=q)
    (a : A.Obj) (i j : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex c).X j) (v : (B.hom b c).X p) :
    actionPair T M n p q hq a i j h m t v =
      tmul T M b a i (j+p) q (by omega) m ((T.obj a).act j p (j+p) rfl t v) := rfl

private def tensorAction {b c : B.Obj} (n p q : ℤ) (hq : n+p=q) :
    Degree T M c n →ₗ[k] (B.hom b c).X p →ₗ[k] Degree T M b q :=
  lift T M (actionPair T M n p q hq) (by
    intro a a' i l j h m f t
    apply LinearMap.ext
    intro v
    rw [actionPair_apply, actionPair_apply, left_comm_act T l j p (l+j) (j+p) (l+j+p)
      rfl rfl rfl]
    exact tmul_balance T M b i l (j+p) (i+l) (l+j+p) q rfl (by omega) (by omega)
      m f ((T.obj a).act j p (j+p) rfl t v))

private theorem tensorAction_tmul {b c : B.Obj} (a : A.Obj) (i j n p jp q : ℤ)
    (h : i+j=n) (hq : n+p=q) (ej : j+p=jp) (m : (M.complex a).X i)
    (t : ((T.obj a).complex c).X j) (v : (B.hom b c).X p) :
    tensorAction T M n p q hq (tmul T M c a i j n h m t) v =
      tmul T M b a i jp q (by omega) m ((T.obj a).act j p jp ej t v) := by
  subst jp
  rw [tensorAction, lift_tmul, actionPair_apply]

private theorem tensorAction_id (b : B.Obj) (n : ℤ) :
    (tensorAction T M n 0 n (add_zero n)).flip (B.id b) = LinearMap.id := by
  apply linearMap_ext T M
  intro a i j h m t
  rw [LinearMap.flip_apply, tensorAction_tmul T M a i j n 0 j n h (add_zero n) (add_zero j),
    (T.obj a).act_id, LinearMap.id_apply]

private theorem tensorAction_assoc {b c e : B.Obj} (n p q : ℤ)
    (f : (B.hom c e).X p) (g : (B.hom b c).X q) :
    ((tensorAction T M (n+p) q (n+p+q) rfl).flip g).comp
      ((tensorAction T M n p (n+p) rfl).flip f) =
    (tensorAction T M n (p+q) (n+p+q) (add_assoc n p q).symm).flip
      (B.comp p q (p+q) rfl f g) := by
  apply linearMap_ext T M
  intro a i j h m t
  simp only [LinearMap.comp_apply, LinearMap.flip_apply]
  rw [tensorAction_tmul T M a i j n p (j+p) (n+p) h rfl rfl,
    tensorAction_tmul T M a i (j+p) (n+p) q (j+p+q) (n+p+q) (by omega) rfl rfl,
    tensorAction_tmul T M a i j n (p+q) (j+p+q) (n+p+q) h (by omega) (by omega),
    (T.obj a).act_assoc]

private theorem tensorAction_leibniz {b c : B.Obj} (n p q : ℤ) (e : n+p=q)
    (f : (B.hom b c).X p) :
    (tensorD T M b q).comp ((tensorAction T M n p q e).flip f) =
      ((tensorAction T M (n+1) p (q+1) (by omega)).flip f).comp (tensorD T M c n) +
      n.negOnePow • (tensorAction T M n (p+1) (q+1) (by omega)).flip
        ((B.hom b c).d p (p+1) f) := by
  apply linearMap_ext T M
  intro a i j h m t
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorD_tmul]
  rw [tensorAction_tmul T M a i j n p (j+p) q h e rfl, tensorD_tmul,
    (T.obj a).leibniz j p (j+p) rfl, tmul_add_right, tmul_units_right]
  simp only [map_add, Units.smul_def, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [tensorAction_tmul T M a (i+1) j (n+1) p (j+p) (q+1) (by omega) (by omega) rfl,
    tensorAction_tmul T M a i (j+1) (n+1) p (j+p+1) (q+1) (by omega) (by omega) (by omega),
    tensorAction_tmul T M a i j n (p+1) (j+p+1) (q+1) h (by omega) (by omega)]
  have sign : (n.negOnePow : ℤ) = (i.negOnePow : ℤ) * (j.negOnePow : ℤ) := by
    rw [← h, Int.negOnePow_add, Units.val_mul]
  rw [sign, mul_smul, smul_add]
  exact (add_assoc _ _ _).symm

section TensorMap

variable {M N : RightDGModule A} (f : M ⟶ N)

private def tensorMapDegree (b : B.Obj) (n : ℤ) : Degree T M b n →ₗ[k] Degree T N b n :=
  lift T M (fun a i j h => (tensorPair T N b a i j n h).comp ((f.app a).f i).hom) (by
    intro a a' i l j h m v t
    simp only [LinearMap.comp_apply, tensorPair_apply]
    change tmul T N b a (i+l) j n h ((f.app a).f (i+l) (M.act i l (i+l) rfl m v)) t =
      tmul T N b a' i (l+j) n _ ((f.app a').f i m) (left T b l j (l+j) rfl v t)
    rw [f.comm_act, tmul_balance])

private theorem tensorMapDegree_tmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    tensorMapDegree T f b n (tmul T M b a i j n h m t) =
      tmul T N b a i j n h ((f.app a).f i m) t := by
  rw [tensorMapDegree, lift_tmul]
  rfl

private theorem tensorMapDegree_d (b : B.Obj) (n : ℤ) :
    (tensorD T N b n).comp (tensorMapDegree T f b n) =
      (tensorMapDegree T f b (n+1)).comp (tensorD T M b n) := by
  apply linearMap_ext T M
  intro a i j h m t
  simp only [LinearMap.comp_apply, tensorMapDegree_tmul, tensorD_tmul, map_add,
    Units.smul_def, map_zsmul]
  have comm := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((f.app a).comm i (i+1))) m
  exact congrArg (fun x => tmul T N b a (i+1) j (n+1) (by omega) x t + _) comm

private theorem tensorMapDegree_act {b c : B.Obj} (n p q : ℤ) (e : n+p=q)
    (v : (B.hom b c).X p) :
    (tensorMapDegree T f b q).comp ((tensorAction T M n p q e).flip v) =
      ((tensorAction T N n p q e).flip v).comp (tensorMapDegree T f c n) := by
  apply linearMap_ext T M
  intro a i j h m t
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, tensorMapDegree_tmul]
  rw [tensorAction_tmul T M a i j n p (j+p) q h e rfl, tensorMapDegree_tmul,
    tensorAction_tmul T N a i j n p (j+p) q h e rfl]

end TensorMap

/-- The chosen quotient in each total degree, with the induced tensor differential. -/
@[reducible] def mixedTensorComplex (b : B.Obj) : ModuleCochain.{u,max vA v w} k where
  X n := ModuleCat.of k (Degree T M b n)
  d n q := if h : n+1=q then h ▸
    ModuleCat.ofHom (tensorD T M b n) else 0
  shape n q h := by
    have e : ¬ n+1=q := h
    simp [e]
  d_comp_d' n q r h e := by
    change n+1=q at h
    change q+1=r at e
    subst q r
    simp only [dite_true]
    exact congrArg ModuleCat.ofHom (tensorD_sq T M b n)

theorem mixedTensorComplex_d_tmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    (mixedTensorComplex T M b).d n (n+1) (tmul T M b a i j n h m t) =
      tmul T M b a (i+1) j (n+1) (by omega) ((M.complex a).d i (i+1) m) t +
      i.negOnePow • tmul T M b a i (j+1) (n+1) (by omega) m
        (((T.obj a).complex b).d j (j+1) t) := by
  simp only [mixedTensorComplex, dite_true]
  exact tensorD_tmul T M b a i j n h m t


/-- The balanced tensor product, with right action on the second factor. -/
@[reducible] def mixedTensorModule : RightModule.{u,v,z,max vA v w} B where
  complex := mixedTensorComplex T M
  act i j n h := tensorAction T M i j n h
  act_id b n x := LinearMap.congr_fun (tensorAction_id T M b n) x
  act_assoc n p q x f g := LinearMap.congr_fun (tensorAction_assoc T M n p q f g) x
  leibniz n p q e x f := by
    simp only [mixedTensorComplex, dite_true]
    exact LinearMap.congr_fun (tensorAction_leibniz T M n p q e f) x

theorem mixedTensorModule_act_tmul {b c : B.Obj} (a : A.Obj) (i j n p jp q : ℤ)
    (h : i+j=n) (e : n+p=q) (ej : j+p=jp) (m : (M.complex a).X i)
    (t : ((T.obj a).complex c).X j) (v : (B.hom b c).X p) :
    (mixedTensorModule T M).act n p q e (tmul T M c a i j n h m t) v =
      tmul T M b a i jp q (by omega) m ((T.obj a).act j p jp ej t v) :=
  tensorAction_tmul T M a i j n p jp q h e ej m t v

/-- Tensoring a strict map with the identity of the bimodule. -/
def mixedTensorMap {M N : RightDGModule A} (f : M ⟶ N) :
    mixedTensorModule T M ⟶ mixedTensorModule T N where
  app b := CochainComplex.ofHom (fun n => ModuleCat.ofHom (tensorMapDegree T f b n)) (by
    intro n
    simp only [mixedTensorModule, mixedTensorComplex, dite_true]
    exact congrArg ModuleCat.ofHom (tensorMapDegree_d T f b n))
  comm_act n p q e x v := LinearMap.congr_fun (tensorMapDegree_act T f n p q e v) x

theorem mixedTensorMap_tmul {M N : RightDGModule A} (f : M ⟶ N)
    (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    ((mixedTensorMap T f).app b).f n (tmul T M b a i j n h m t) =
      tmul T N b a i j n h ((f.app a).f i m) t :=
  tensorMapDegree_tmul T f b a i j n h m t

/-- The balanced tensor functor on strict module maps. -/
def mixedTensorFunctor : RightDGModule A ⥤ RightModule.{u,v,z,max vA v w} B where
  obj := mixedTensorModule T
  map := mixedTensorMap T
  map_id M := by
    apply RightModule.hom_ext
    intro b
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change tensorMapDegree T (𝟙 M) b n = LinearMap.id
    apply linearMap_ext T M
    intro a i j h m t
    rw [tensorMapDegree_tmul]
    rfl
  map_comp {M N P} f g := by
    apply RightModule.hom_ext
    intro b
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change tensorMapDegree T (f ≫ g) b n =
      (tensorMapDegree T g b n).comp (tensorMapDegree T f b n)
    apply linearMap_ext T M
    intro a i j h m t
    simp only [LinearMap.comp_apply, tensorMapDegree_tmul]
    rfl

theorem tensorConstruction : TensorConstruction.{u,v,w,z,vA} := by
  intro k _ A B T
  refine ⟨mixedTensorFunctor T, fun _ _ _ => LinearEquiv.refl _ _, ?_, ?_, ?_⟩
  · intro M a b i j n h m t
    exact mixedTensorComplex_d_tmul T M b a i j n h m t
  · intro M a b c i j n l q h e m t f
    exact mixedTensorModule_act_tmul T M a i j n l (j+l) q h e rfl m t f
  · intro M N f a b i j n h m t
    exact mixedTensorMap_tmul T f b a i j n h m t

end Tensor

section OrdinaryHom

variable {A₀ : DGCategory.{u,max v z,w} k} (T₀ : DGBimodule A₀ B)

/-- The internal Hom functor with values in the shared dg module category. -/
def homFunctor : RightDGModule B ⥤ RightDGModule A₀ :=
  mixedHomFunctor T₀ ⋙ RightModule.toOrdinary

abbrev homModule (N : RightDGModule B) : RightDGModule A₀ := (homFunctor T₀).obj N

abbrev homMap {N P : RightDGModule B} (f : N ⟶ P) :
    homModule T₀ N ⟶ homModule T₀ P := (homFunctor T₀).map f

theorem homModule_act (N : RightDGModule B) {a b : A₀.Obj} (i j n : ℤ) (h : i+j=n)
    (g : (RightDGModule.homComplex (T₀.obj b) N).X i) (f : (A₀.hom a b).X j) :
    (homModule T₀ N).act i j n h g f =
      (RightDGModule.dgCategory B).comp i j n h g ((T₀.map a b).f j f) := rfl

theorem homMap_apply {N P : RightDGModule B} (f : N ⟶ P) (a : A₀.Obj) (i : ℤ)
    (g : (RightDGModule.homComplex (T₀.obj a) N).X i) :
    ((homMap T₀ f).app a).f i g =
      (RightDGModule.dgCategory B).comp 0 i i (zero_add i)
        (Specs.DerivedFormalization.DG.HomComplex.ofStrict f) g := rfl

end OrdinaryHom

section OrdinaryTensor

variable {A₀ : DGCategory.{u,max v w z,w} k} {B₀ : DGCategory.{u,max v w z,z} k}
variable (T₀ : DGBimodule A₀ B₀)

/-- The balanced tensor functor in a common universe containing the source objects. -/
def tensorFunctor : RightDGModule A₀ ⥤ RightDGModule B₀ :=
  mixedTensorFunctor T₀ ⋙ RightModule.toOrdinary

abbrev tensorModule (M : RightDGModule A₀) : RightDGModule B₀ :=
  (tensorFunctor.{u,v,w,z} T₀).obj M

abbrev tensorComplex (M : RightDGModule A₀) (b : B₀.Obj) : ModuleCochain.{u,max v w z} k :=
  (tensorModule.{u,v,w,z} T₀ M).complex b

abbrev tensorMap {M N : RightDGModule A₀} (f : M ⟶ N) :
    tensorModule.{u,v,w,z} T₀ M ⟶ tensorModule.{u,v,w,z} T₀ N :=
  (tensorFunctor.{u,v,w,z} T₀).map f

variable (M₀ : RightDGModule A₀)

theorem tensorComplex_d_tmul (b : B₀.Obj) (a : A₀.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M₀.complex a).X i) (t : ((T₀.obj a).complex b).X j) :
    (tensorComplex.{u,v,w,z} T₀ M₀ b).d n (n+1) (tmul T₀ M₀ b a i j n h m t) =
      tmul T₀ M₀ b a (i+1) j (n+1) (by omega) ((M₀.complex a).d i (i+1) m) t +
      i.negOnePow • tmul T₀ M₀ b a i (j+1) (n+1) (by omega) m
        (((T₀.obj a).complex b).d j (j+1) t) :=
  mixedTensorComplex_d_tmul T₀ M₀ b a i j n h m t

theorem tensorModule_act_tmul {b c : B₀.Obj} (a : A₀.Obj) (i j n p jp q : ℤ)
    (h : i+j=n) (e : n+p=q) (ej : j+p=jp) (m : (M₀.complex a).X i)
    (t : ((T₀.obj a).complex c).X j) (f : (B₀.hom b c).X p) :
    (tensorModule.{u,v,w,z} T₀ M₀).act n p q e (tmul T₀ M₀ c a i j n h m t) f =
      tmul T₀ M₀ b a i jp q (by omega) m ((T₀.obj a).act j p jp ej t f) :=
  mixedTensorModule_act_tmul T₀ M₀ a i j n p jp q h e ej m t f

theorem tensorMap_tmul {M N : RightDGModule A₀} (f : M ⟶ N)
    (b : B₀.Obj) (a : A₀.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T₀.obj a).complex b).X j) :
    ((tensorMap.{u,v,w,z} T₀ f).app b).f n (tmul T₀ M b a i j n h m t) =
      tmul T₀ N b a i j n h ((f.app a).f i m) t :=
  mixedTensorMap_tmul T₀ f b a i j n h m t

end OrdinaryTensor

end
end DGBimodule
end DerivedFormalization
