import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BimoduleTensorComparisons

open CategoryTheory

universe u v w z vA

namespace DerivedFormalization.DGBimodule

open Specs.DerivedFormalization.DG.BalancedTensor (Degree tmul)
open Specs.DerivedFormalization.DG.BimoduleAdjunction (TensorModel ordinaryTensor)
open Specs.DerivedFormalization.DG.BimoduleTensorComparisons (TensorComparisons)
open RightDGModule (GradedHom shift shiftMap cone coneInclusion coneProjection
  coneGradedRetraction coneGradedSection strictCycle)

noncomputable section

variable {k : Type u} [CommRing k]

section BalancedQuotient

variable {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
variable {T : DGBimodule A B} {M N : RightDGModule A}

/-- Tensor a homogeneous right-linear map in the first factor. -/
private def tensorFirstMap {s : ℤ} (g : GradedHom M N s)
    (b : B.Obj) (n q : ℤ) (e : n + s = q) : Degree T M b n →ₗ[k] Degree T N b q :=
  lift T M (fun a i j h =>
    (tensorPair T N b a (i+s) j q (by omega)).comp (g.app a i (i+s) rfl).hom) (by
    intro a a' i l j h x f y
    simp only [LinearMap.comp_apply, tensorPair_apply]
    rw [g.comm_act i l (i+l) (i+s) (i+l+s) rfl rfl rfl x f]
    exact tmul_balance T N b (i+s) l j (i+l+s) (l+j) q (by omega) rfl (by omega)
      (g.app a' i (i+s) rfl x) f y)

private theorem tensorFirstMap_tmul {s : ℤ} (g : GradedHom M N s)
    (b : B.Obj) (a : A.Obj) (i j n q p : ℤ) (h : i+j=n) (e : n+s=q) (hp : i+s=p)
    (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    tensorFirstMap (T := T) g b n q e (tmul T M b a i j n h x y) =
      tmul T N b a p j q (by omega) (g.app a i p hp x) y := by
  subst p
  rw [tensorFirstMap, lift_tmul]
  rfl

private def shiftFirst (M : RightDGModule A) (s : ℤ) : GradedHom (shift M s) M s :=
  GradedHom.mk (fun a i q h => eqToHom (congrArg (M.complex a).X h)) (by
    intro a b i j n ir nr h hi hn x f
    subst ir nr
    rfl)

private def unshiftFirst (M : RightDGModule A) (s : ℤ) : GradedHom M (shift M s) (-s) :=
  GradedHom.mk (fun a i q h => eqToHom (congrArg (M.complex a).X (show i = q+s by omega))) (by
    intro a b i j n ir nr h hi hn x f
    have hi' : i = ir+s := by omega
    have hn' : n = nr+s := by omega
    subst hi' hn'
    rfl)

private theorem shiftFirst_apply (M : RightDGModule A) (s : ℤ) (a : A.Obj) (i : ℤ)
    (x : ((shift M s).complex a).X i) :
    (shiftFirst M s).app a i (i+s) rfl x = x := rfl

private theorem unshiftFirst_apply (M : RightDGModule A) (s : ℤ) (a : A.Obj) (i : ℤ)
    (x : (M.complex a).X (i+s)) :
    (unshiftFirst M s).app a (i+s) i (by omega) x = x := rfl

private theorem shiftTensorMap_tmul (M : RightDGModule A) (s : ℤ)
    (b : B.Obj) (a : A.Obj) (i j n q : ℤ) (h : i+j=n) (e : n+s=q)
    (x : ((shift M s).complex a).X i) (y : ((T.obj a).complex b).X j) :
    tensorFirstMap (T := T) (shiftFirst M s) b n q e (tmul T (shift M s) b a i j n h x y) =
      tmul T M b a (i+s) j q (by omega) x y := by
  rw [tensorFirstMap_tmul (p := i+s) (hp := rfl), shiftFirst_apply]

private theorem unshiftTensorMap_tmul (M : RightDGModule A) (s : ℤ)
    (b : B.Obj) (a : A.Obj) (i j n q : ℤ) (h : (i+s)+j=q) (e : q + -s = n)
    (x : (M.complex a).X (i+s)) (y : ((T.obj a).complex b).X j) :
    tensorFirstMap (T := T) (unshiftFirst M s) b q n e (tmul T M b a (i+s) j q h x y) =
      tmul T (shift M s) b a i j n (by omega) x y := by
  rw [tensorFirstMap_tmul (p := i) (hp := by omega), unshiftFirst_apply]

private def shiftTensorEquiv (M : RightDGModule A) (s : ℤ) (b : B.Obj) (n : ℤ) :
    Degree T (shift M s) b n ≃ₗ[k] Degree T M b (n+s) := by
  let f := tensorFirstMap (T := T) (shiftFirst M s) b n (n+s) rfl
  let g := tensorFirstMap (T := T) (unshiftFirst M s) b (n+s) n (by omega)
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · apply linearMap_ext T M
    intro a i j h x y
    obtain ⟨i', rfl⟩ : ∃ i' : ℤ, i = i'+s := ⟨i-s, by omega⟩
    change f (g (tmul T M b a (i'+s) j (n+s) h x y)) = _
    dsimp only [f, g]
    rw [unshiftTensorMap_tmul, shiftTensorMap_tmul]
    rfl
  · apply linearMap_ext T (shift M s)
    intro a i j h x y
    change g (f (tmul T (shift M s) b a i j n h x y)) = _
    dsimp only [f, g]
    rw [shiftTensorMap_tmul, unshiftTensorMap_tmul]
    rfl

private theorem shiftTensorEquiv_tmul (M : RightDGModule A) (s : ℤ)
    (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (x : ((shift M s).complex a).X i) (y : ((T.obj a).complex b).X j) :
    shiftTensorEquiv (T := T) M s b n (tmul T (shift M s) b a i j n h x y) =
      tmul T M b a (i+s) j (n+s) (by omega) x y :=
  shiftTensorMap_tmul M s b a i j n (n+s) h rfl x y


private def tensorDegreeMap (g : GradedHom M N 0) (b : B.Obj) (n : ℤ) :
    Degree T M b n →ₗ[k] Degree T N b n :=
  tensorFirstMap (T := T) g b n n (add_zero n)

private theorem tensorDegreeMap_tmul (g : GradedHom M N 0)
    (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    tensorDegreeMap (T := T) g b n (tmul T M b a i j n h x y) =
      tmul T N b a i j n h (g.app a i i (add_zero i) x) y :=
  tensorFirstMap_tmul g b a i j n n i h (add_zero n) (add_zero i) x y

private theorem strictCycle_apply (f : M ⟶ N) (a : A.Obj) (i : ℤ) (x : (M.complex a).X i) :
    GradedHom.app (strictCycle f).val a i i (add_zero i) x = (f.app a).f i x :=
  congrArg (fun g : (M.complex a).X i ⟶ (N.complex a).X i => g x)
    (CochainComplex.HomComplex.Cochain.ofHom_v (f.app a) i)

private theorem coneRetraction_apply (f : M ⟶ N) (a : A.Obj) (i : ℤ)
    (x : ((cone f).complex a).X i) :
    (coneGradedRetraction f).app a i i (add_zero i) x = x.1 := rfl

private theorem coneSection_apply (f : M ⟶ N) (a : A.Obj) (i : ℤ)
    (x : ((shift M 1).complex a).X i) :
    (coneGradedSection f).app a i i (add_zero i) x = (0, x) := rfl

private theorem tensorZeroLeft {b : B.Obj} {a : A.Obj} {i j n : ℤ}
    (h : i+j=n) (y : ((T.obj a).complex b).X j) :
    tmul T M b a i j n h 0 y = 0 := by
  simp only [← tensorPair_apply, map_zero, LinearMap.zero_apply]

private theorem tensorAddLeft {b : B.Obj} {a : A.Obj} {i j n : ℤ}
    (h : i+j=n) (x x' : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    tmul T M b a i j n h (x+x') y =
      tmul T M b a i j n h x y + tmul T M b a i j n h x' y := by
  simp only [← tensorPair_apply, map_add, LinearMap.add_apply]

private def tensorConeEquivAux (f : M ⟶ N) (b : B.Obj) (n : ℤ) :
    { e : Degree T (cone f) b n ≃ₗ[k] (Degree T N b n × Degree T (shift M 1) b n) //
      ∀ a i j (h : i+j=n) (x : ((cone f).complex a).X i) (y : ((T.obj a).complex b).X j),
        e (tmul T (cone f) b a i j n h x y) =
          (tmul T N b a i j n h x.1 y, tmul T (shift M 1) b a i j n h x.2 y) } := by
  let p := tensorDegreeMap (T := T) (coneGradedRetraction f) b n
  let q := tensorDegreeMap (T := T) (strictCycle (coneProjection f)).val b n
  let i₁ := tensorDegreeMap (T := T) (strictCycle (coneInclusion f)).val b n
  let i₂ := tensorDegreeMap (T := T) (coneGradedSection f) b n
  let forward := p.prod q
  let backward := i₁.coprod i₂
  have hf a i j (h : i+j=n) (x : ((cone f).complex a).X i)
      (y : ((T.obj a).complex b).X j) :
      forward (tmul T (cone f) b a i j n h x y) =
        (tmul T N b a i j n h x.1 y, tmul T (shift M 1) b a i j n h x.2 y) := by
    change (p (tmul T (cone f) b a i j n h x y), q (tmul T (cone f) b a i j n h x y)) = _
    dsimp only [p, q]
    rw [tensorDegreeMap_tmul, tensorDegreeMap_tmul, coneRetraction_apply, strictCycle_apply,
      RightDGModule.coneProjection_f]
  have hi₁ a i j (h : i+j=n) (x : (N.complex a).X i) (y : ((T.obj a).complex b).X j) :
      i₁ (tmul T N b a i j n h x y) = tmul T (cone f) b a i j n h (x, 0) y := by
    dsimp only [i₁]
    rw [tensorDegreeMap_tmul, strictCycle_apply, RightDGModule.coneInclusion_f]
  have hi₂ a i j (h : i+j=n) (x : ((shift M 1).complex a).X i)
      (y : ((T.obj a).complex b).X j) :
      i₂ (tmul T (shift M 1) b a i j n h x y) = tmul T (cone f) b a i j n h (0, x) y := by
    dsimp only [i₂]
    rw [tensorDegreeMap_tmul, coneSection_apply]
  refine ⟨LinearEquiv.ofLinearMap forward backward ?_ ?_, hf⟩
  · apply LinearMap.prod_ext
    · apply linearMap_ext T N
      intro a i j h x y
      change forward (i₁ (tmul T N b a i j n h x y) + i₂ 0) =
        (tmul T N b a i j n h x y, 0)
      rw [map_zero, add_zero, hi₁, hf, tensorZeroLeft]
    · apply linearMap_ext T (shift M 1)
      intro a i j h x y
      change forward (i₁ 0 + i₂ (tmul T (shift M 1) b a i j n h x y)) =
        (0, tmul T (shift M 1) b a i j n h x y)
      rw [map_zero, zero_add, hi₂, hf, tensorZeroLeft]
  · apply linearMap_ext T (cone f)
    intro a i j h x y
    change backward (forward (tmul T (cone f) b a i j n h x y)) = tmul T (cone f) b a i j n h x y
    rw [hf]
    change i₁ (tmul T N b a i j n h x.1 y) + i₂ (tmul T (shift M 1) b a i j n h x.2 y) = _
    rw [hi₁, hi₂, ← tensorAddLeft]
    congr 1
    exact Prod.ext (add_zero x.1) (zero_add x.2)

private def tensorConeEquiv (f : M ⟶ N) (b : B.Obj) (n : ℤ) :
    Degree T (cone f) b n ≃ₗ[k] (Degree T N b n × Degree T (shift M 1) b n) :=
  (tensorConeEquivAux (T := T) f b n).1

private theorem tensorConeEquiv_tmul (f : M ⟶ N)
    (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (x : ((cone f).complex a).X i) (y : ((T.obj a).complex b).X j) :
    tensorConeEquiv (T := T) f b n (tmul T (cone f) b a i j n h x y) =
      (tmul T N b a i j n h x.1 y, tmul T (shift M 1) b a i j n h x.2 y) :=
  (tensorConeEquivAux (T := T) f b n).2 a i j h x y

end BalancedQuotient

section OrdinaryTensor

variable {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
variable {T : DGBimodule A B} (L : TensorModel T) {M N : RightDGModule A}

private theorem tensorDegree_ext {P : Type*} [AddCommGroup P] [Module k P]
    {M : RightDGModule A} {b : B.Obj} {n : ℤ} {f g : (((ordinaryTensor.{u,v,w,z} L).obj M).complex b).X n →ₗ[k] P}
    (h : ∀ (a : A.Obj) (i j : ℤ) (e : i+j=n)
      (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j),
      f (L.degree M b n (tmul T M b a i j n e x y)) =
      g (L.degree M b n (tmul T M b a i j n e x y))) : f = g := by
  have he : f.comp (L.degree M b n).toLinearMap = g.comp (L.degree M b n).toLinearMap :=
    linearMap_ext T M h
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (L.degree M b n).surjective x
  exact LinearMap.congr_fun he x

private theorem tensorHom_ext {P : RightDGModule B} {f g : (ordinaryTensor.{u,v,w,z} L).obj M ⟶ P}
    (h : ∀ (b : B.Obj) (n : ℤ) (a : A.Obj) (i j : ℤ) (e : i+j=n)
      (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j),
      (f.app b).f n (L.degree M b n (tmul T M b a i j n e x y)) =
      (g.app b).f n (L.degree M b n (tmul T M b a i j n e x y))) : f = g :=
  RightDGModuleModel.hom_ext fun b => HomologicalComplex.hom_ext _ _
    fun n => ModuleCat.hom_ext (tensorDegree_ext.{u,v,w,z} L (h b n))

private def tensorIsoOfComponents {P : RightDGModule B}
    (e : ∀ b n, (((ordinaryTensor.{u,v,w,z} L).obj M).complex b).X n ≃ₗ[k] (P.complex b).X n)
    (hd : ∀ b n a i j (h : i+j=n) (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j),
      let t := L.degree M b n (tmul T M b a i j n h x y)
      e b (n+1) ((((ordinaryTensor.{u,v,w,z} L).obj M).complex b).d n (n+1) t) =
        (P.complex b).d n (n+1) (e b n t))
    (ha : ∀ {b c : B.Obj} n l q (hq : n+l=q) a i j (h : i+j=n)
      (x : (M.complex a).X i) (y : ((T.obj a).complex c).X j) (f : (B.hom b c).X l),
      let t := L.degree M c n (tmul T M c a i j n h x y)
      e b q (((ordinaryTensor.{u,v,w,z} L).obj M).act n l q hq t f) =
        P.act n l q hq (e c n t) f) : (ordinaryTensor.{u,v,w,z} L).obj M ≅ P := by
  refine DG.CoefficientLift.isoOfComponents e ?_ ?_
  · intro b n x
    have hd' : (e b (n+1)).toLinearMap.comp ((((ordinaryTensor.{u,v,w,z} L).obj M).complex b).d n (n+1)).hom =
        (((P.complex b).d n (n+1)).hom).comp (e b n).toLinearMap :=
      tensorDegree_ext.{u,v,w,z} L (hd b n)
    exact LinearMap.congr_fun hd' x
  · intro b c n l q hq x f
    have ha' : (e b q).toLinearMap.comp ((((ordinaryTensor.{u,v,w,z} L).obj M).act n l q hq).flip f) =
        ((P.act n l q hq).flip f).comp (e c n).toLinearMap :=
      tensorDegree_ext.{u,v,w,z} L (fun a i j h x y => ha n l q hq a i j h x y f)
    exact LinearMap.congr_fun ha' x

private theorem map_intUnits_smul {P Q H : Type*} [AddCommGroup P] [AddCommGroup Q]
    [FunLike H P Q] [AddMonoidHomClass H P Q] (f : H) (c : ℤˣ) (x : P) :
    f (c • x) = c • f x := by
  simp only [Units.smul_def, map_zsmul]

private theorem intUnits_smul_hom_apply {P Q : ModuleCat k} (s : ℤˣ) (f : P ⟶ Q) (x : P) :
    (s • f) x = s • f x := rfl

private theorem tmul_intUnits_smul_left (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (c : ℤˣ) (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    tmul T M b a i j n h (c • x) y = c • tmul T M b a i j n h x y := by
  simp only [← tensorPair_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]

private theorem tensorDiffAt (M : RightDGModule A) (a : A.Obj) (b : B.Obj) (i j n p q : ℤ)
    (h : i+j=n) (hp : i+1=p) (hq : n+1=q) (x : (M.complex a).X i)
    (y : ((T.obj a).complex b).X j) :
    ((L.functor.obj M).complex b).d n q (L.degree M b n (tmul T M b a i j n h x y)) =
      L.degree M b q (tmul T M b a p j q (by omega) ((M.complex a).d i p x) y) +
      i.negOnePow • L.degree M b q (tmul T M b a i (j+1) q (by omega) x
        (((T.obj a).complex b).d j (j+1) y)) := by
  subst p q
  exact L.d_tmul M a b i j n h x y

private def tensorShiftDegree (M : RightDGModule A) (s : ℤ) (b : B.Obj) (n : ℤ) :
    (((ordinaryTensor.{u,v,w,z} L).obj (shift M s)).complex b).X n ≃ₗ[k] ((shift ((ordinaryTensor.{u,v,w,z} L).obj M) s).complex b).X n :=
  (L.degree (shift M s) b n).symm.trans
    ((shiftTensorEquiv (T := T) M s b n).trans (L.degree M b (n+s)))

private theorem tensorShiftDegree_tmul (M : RightDGModule A) (s : ℤ)
    (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (x : ((shift M s).complex a).X i) (y : ((T.obj a).complex b).X j) :
    tensorShiftDegree.{u,v,w,z} L M s b n (L.degree (shift M s) b n
      (tmul T (shift M s) b a i j n h x y)) =
      L.degree M b (n+s) (tmul T M b a (i+s) j (n+s) (by omega) x y) := by
  simp only [tensorShiftDegree, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    shiftTensorEquiv_tmul]

private def tensorShiftIso (M : RightDGModule A) (s : ℤ) :
    (ordinaryTensor.{u,v,w,z} L).obj (shift M s) ≅ shift ((ordinaryTensor.{u,v,w,z} L).obj M) s := by
  refine tensorIsoOfComponents.{u,v,w,z} L (tensorShiftDegree.{u,v,w,z} L M s) ?_ ?_
  · intro b n a i j h x y
    change tensorShiftDegree.{u,v,w,z} L M s b (n+1)
      (((L.functor.obj (shift M s)).complex b).d n (n+1) _) = _
    rw [tensorShiftDegree_tmul.{u,v,w,z}, L.d_tmul]
    simp only [map_add, map_intUnits_smul, tensorShiftDegree_tmul.{u,v,w,z}]
    have hd : ((shift M s).complex a).d i (i+1) x =
        s.negOnePow • (M.complex a).d (i+s) (i+1+s) x := rfl
    change _ = (s.negOnePow • ((L.functor.obj M).complex b).d (n+s) (n+1+s)) _
    rw [intUnits_smul_hom_apply,
      tensorDiffAt.{u,v,w,z} L M a b (i+s) j (n+s) (i+1+s) (n+1+s)
        (by omega) (by omega) (by omega) x y]
    -- Reindexing the first factor changes the sign on the second-factor differential.
    have hs : s.negOnePow * (i+s).negOnePow = i.negOnePow := by
      rw [Int.negOnePow_add, mul_left_comm, Int.units_mul_self, mul_one]
    rw [hd, tmul_intUnits_smul_left.{u,v,w,z}, map_intUnits_smul, smul_add, smul_smul, hs]
  · intro b c n l q hq a i j h x y f
    change tensorShiftDegree.{u,v,w,z} L M s b q
      ((L.functor.obj (shift M s)).act n l q hq _ f) = _
    rw [L.act_tmul, tensorShiftDegree_tmul.{u,v,w,z}, tensorShiftDegree_tmul.{u,v,w,z}]
    change _ = (L.functor.obj M).act (n+s) l (q+s) (by omega)
      (L.degree M c (n+s) (tmul T M c a (i+s) j (n+s) (by omega) x y)) f
    rw [L.act_tmul]

private theorem tensorShiftIso_tmul (M : RightDGModule A) (s : ℤ)
    (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (x : ((shift M s).complex a).X i) (y : ((T.obj a).complex b).X j) :
    (((tensorShiftIso.{u,v,w,z} L M s).hom.app b).f n)
      (L.degree (shift M s) b n (tmul T (shift M s) b a i j n h x y)) =
      L.degree M b (n+s) (tmul T M b a (i+s) j (n+s) (by omega) x y) :=
  tensorShiftDegree_tmul.{u,v,w,z} L M s b a i j n h x y

private theorem tensorShiftIso_natural (f : M ⟶ N) (s : ℤ) :
    (ordinaryTensor.{u,v,w,z} L).map (shiftMap s f) ≫ (tensorShiftIso.{u,v,w,z} L N s).hom =
      (tensorShiftIso.{u,v,w,z} L M s).hom ≫ shiftMap s ((ordinaryTensor.{u,v,w,z} L).map f) := by
  apply tensorHom_ext.{u,v,w,z} L
  intro b n a i j h x y
  change (((tensorShiftIso.{u,v,w,z} L N s).hom.app b).f n)
      (((L.functor.map (shiftMap s f)).app b).f n
        (L.degree (shift M s) b n (tmul T (shift M s) b a i j n h x y))) =
    ((L.functor.map f).app b).f (n+s)
      ((((tensorShiftIso.{u,v,w,z} L M s).hom.app b).f n)
        (L.degree (shift M s) b n (tmul T (shift M s) b a i j n h x y)))
  rw [L.map_tmul, tensorShiftIso_tmul.{u,v,w,z}, tensorShiftIso_tmul.{u,v,w,z}, L.map_tmul]
  rfl


private theorem tensorNegLeft {b : B.Obj} {a : A.Obj} {i j n : ℤ}
    (h : i+j=n) (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    tmul T M b a i j n h (-x) y = -tmul T M b a i j n h x y := by
  simp only [← tensorPair_apply, map_neg, LinearMap.neg_apply]

private def tensorConeDegree (f : M ⟶ N) (b : B.Obj) (n : ℤ) :
    (((ordinaryTensor.{u,v,w,z} L).obj (cone f)).complex b).X n ≃ₗ[k]
      ((cone ((ordinaryTensor.{u,v,w,z} L).map f)).complex b).X n :=
  (L.degree (cone f) b n).symm.trans
    ((tensorConeEquiv (T := T) f b n).trans
      ((L.degree N b n).prodCongr
        ((shiftTensorEquiv (T := T) M 1 b n).trans (L.degree M b (n+1)))))

private theorem tensorConeDegree_tmul (f : M ⟶ N) (b : B.Obj) (a : A.Obj)
    (i j n : ℤ) (h : i+j=n) (x : ((cone f).complex a).X i) (y : ((T.obj a).complex b).X j) :
    tensorConeDegree.{u,v,w,z} L f b n (L.degree (cone f) b n (tmul T (cone f) b a i j n h x y)) =
      (L.degree N b n (tmul T N b a i j n h x.1 y),
        L.degree M b (n+1) (tmul T M b a (i+1) j (n+1) (by omega) x.2 y)) := by
  simp only [tensorConeDegree, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    tensorConeEquiv_tmul, LinearEquiv.prodCongr_apply, shiftTensorEquiv_tmul]

private def tensorConeIso (f : M ⟶ N) :
    (ordinaryTensor.{u,v,w,z} L).obj (cone f) ≅ cone ((ordinaryTensor.{u,v,w,z} L).map f) := by
  refine tensorIsoOfComponents.{u,v,w,z} L (tensorConeDegree.{u,v,w,z} L f) ?_ ?_
  · intro b n a i j h x y
    change tensorConeDegree.{u,v,w,z} L f b (n+1)
      (((L.functor.obj (cone f)).complex b).d n (n+1) _) =
        ((cone ((ordinaryTensor.{u,v,w,z} L).map f)).complex b).d n (n+1) _
    rw [tensorConeDegree_tmul.{u,v,w,z}, RightDGModule.cone_d ((ordinaryTensor.{u,v,w,z} L).map f),
      L.d_tmul, RightDGModule.cone_d f]
    simp only [map_add, map_intUnits_smul, tensorConeDegree_tmul.{u,v,w,z},
      Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · -- The off-diagonal term is the tensor of the strict map.
      change _ = ((L.functor.obj N).complex b).d n (n+1)
        (L.degree N b n (tmul T N b a i j n h x.1 y)) +
          ((L.functor.map f).app b).f (n+1)
            (L.degree M b (n+1) (tmul T M b a (i+1) j (n+1) (by omega) x.2 y))
      rw [L.d_tmul, L.map_tmul, tensorAddLeft, map_add]
      abel
    · change _ = -((L.functor.obj M).complex b).d (n+1) (n+1+1)
        (L.degree M b (n+1) (tmul T M b a (i+1) j (n+1) (by omega) x.2 y))
      rw [L.d_tmul, tensorNegLeft.{u,v,w,z}, map_neg, Int.negOnePow_succ, Units.neg_smul,
        neg_add, neg_neg]
  · intro b c n l q hq a i j h x y g
    change tensorConeDegree.{u,v,w,z} L f b q
      ((L.functor.obj (cone f)).act n l q hq _ g) =
        (cone ((ordinaryTensor.{u,v,w,z} L).map f)).act n l q hq _ g
    rw [tensorConeDegree_tmul.{u,v,w,z}, L.act_tmul, tensorConeDegree_tmul.{u,v,w,z},
      RightDGModule.cone_act ((ordinaryTensor.{u,v,w,z} L).map f)]
    apply Prod.ext
    · change _ = (L.functor.obj N).act n l q hq
        (L.degree N c n (tmul T N c a i j n h x.1 y)) g
      rw [L.act_tmul]
    · change _ = (L.functor.obj M).act (n+1) l (q+1) (by omega)
        (L.degree M c (n+1) (tmul T M c a (i+1) j (n+1) (by omega) x.2 y)) g
      rw [L.act_tmul]

private theorem tensorConeIso_tmul (f : M ⟶ N) (b : B.Obj) (a : A.Obj)
    (i j n : ℤ) (h : i+j=n) (x : ((cone f).complex a).X i) (y : ((T.obj a).complex b).X j) :
    (((tensorConeIso.{u,v,w,z} L f).hom.app b).f n)
      (L.degree (cone f) b n (tmul T (cone f) b a i j n h x y)) =
      (L.degree N b n (tmul T N b a i j n h x.1 y),
        L.degree M b (n+1) (tmul T M b a (i+1) j (n+1) (by omega) x.2 y)) :=
  tensorConeDegree_tmul.{u,v,w,z} L f b a i j n h x y

private theorem tensorConeIso_inclusion (f : M ⟶ N) :
    (ordinaryTensor.{u,v,w,z} L).map (coneInclusion f) ≫ (tensorConeIso.{u,v,w,z} L f).hom =
      coneInclusion ((ordinaryTensor.{u,v,w,z} L).map f) := by
  apply tensorHom_ext.{u,v,w,z} L
  intro b n a i j h x y
  let t := L.degree N b n (tmul T N b a i j n h x y)
  change (((tensorConeIso.{u,v,w,z} L f).hom.app b).f n)
      (((L.functor.map (coneInclusion f)).app b).f n t) = (t, 0)
  dsimp only [t]
  rw [L.map_tmul, RightDGModule.coneInclusion_f, tensorConeIso_tmul.{u,v,w,z}]
  change (_, L.degree M b (n+1) (tmul T M b a (i+1) j (n+1) (by omega) 0 y)) = _
  rw [tensorZeroLeft, map_zero]

private theorem tensorConeIso_projection (f : M ⟶ N) :
    (ordinaryTensor.{u,v,w,z} L).map (coneProjection f) ≫ (tensorShiftIso.{u,v,w,z} L M 1).hom =
      (tensorConeIso.{u,v,w,z} L f).hom ≫ coneProjection ((ordinaryTensor.{u,v,w,z} L).map f) := by
  apply tensorHom_ext.{u,v,w,z} L
  intro b n a i j h x y
  let t := L.degree (cone f) b n (tmul T (cone f) b a i j n h x y)
  change (((tensorShiftIso.{u,v,w,z} L M 1).hom.app b).f n)
    (((L.functor.map (coneProjection f)).app b).f n t) =
      ((((tensorConeIso.{u,v,w,z} L f).hom.app b).f n) t).2
  dsimp only [t]
  rw [L.map_tmul, RightDGModule.coneProjection_f, tensorShiftIso_tmul.{u,v,w,z},
    tensorConeIso_tmul.{u,v,w,z}]

/-- The canonical strict comparisons for tensoring with a dg bimodule. -/
theorem tensorComparisons : TensorComparisons.{u,v,w,z} := by
  intro k _ A B T L
  exact ⟨tensorShiftIso.{u,v,w,z} L, fun f => tensorConeIso.{u,v,w,z} L f,
    fun f s => tensorShiftIso_natural.{u,v,w,z} L f s,
    fun f => tensorConeIso_inclusion.{u,v,w,z} L f,
    fun f => tensorConeIso_projection.{u,v,w,z} L f,
    fun M s a b i j n h x y => tensorShiftIso_tmul.{u,v,w,z} L M s b a i j n h x y,
    fun f a b i j n h x y => tensorConeIso_tmul.{u,v,w,z} L f b a i j n h x y⟩

end OrdinaryTensor

end

end DerivedFormalization.DGBimodule
