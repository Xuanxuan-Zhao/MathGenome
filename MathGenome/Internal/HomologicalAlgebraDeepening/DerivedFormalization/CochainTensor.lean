import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainCoefficientLift
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Batteries.Tactic.OpenPrivate

/-! The tensor of ordinary cochain complexes, with independent ring and module universes. -/

namespace DerivedFormalization.CochainTensor

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ZeroObject
open Specs.DerivedFormalization.DG.Basic (moduleTensor)
open CochainCoefficientLift (lift termEquiv lift_d lift_f)

universe u v t

variable {R : Type u} [CommRing R]

noncomputable section

abbrev tensor (X Y : Comp.{v} R) : Comp.{v} R := Specs.DerivedFormalization.CochainTensor.tensor X Y

abbrev map {X X' Y Y' : Comp.{v} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensor X Y ⟶ tensor X' Y' := Specs.DerivedFormalization.CochainTensor.map f g

abbrev ι (X Y : Comp.{v} R) (i j n : ℤ) (h : i + j = n) := Specs.DerivedFormalization.CochainTensor.ι X Y i j n h

abbrev pure (X Y : Comp.{v} R) {i j n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (tensor X Y).X n := ι X Y i j n h (x ⊗ₜ[R] y)

abbrev IsKFlat (F : Comp.{v} R) : Prop := Specs.DerivedFormalization.CochainTensor.isKFlat F

def tensorCofanIsColimit (X Y : Comp.{v} R) (n : ℤ) : IsColimit (Specs.DerivedFormalization.CochainTensor.cofan X Y n) :=
  let K := (((moduleTensor R).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj X).obj Y
  K.toGradedObject.isColimitCofanMapObj (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) n

theorem coproduct : Specs.DerivedFormalization.CochainTensor.Coproduct.{u,v} :=
  fun X Y n => ⟨tensorCofanIsColimit X Y n⟩

private theorem module_hom_ext {A B : ModuleCat.{v} R} {f g : A ⟶ B}
    (h : ∀ x : A, f x = g x) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext h)

private theorem summand_hom_ext {A B C : ModuleCat.{v} R}
    {f g : ModuleCat.of R (A ⊗[R] B) ⟶ C}
    (h : ∀ (x : A) (y : B), f (x ⊗ₜ[R] y) = g (x ⊗ₜ[R] y)) : f = g :=
  ModuleCat.hom_ext (TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext (h x)))

theorem term_hom_ext {X Y : Comp.{v} R} {M : ModuleCat.{v} R} {n : ℤ}
    {f g : (tensor X Y).X n ⟶ M}
    (w : ∀ i j (h : i + j = n) (x : X.X i) (y : Y.X j),
      f (pure X Y h x y) = g (pure X Y h x y)) : f = g := by
  apply mapBifunctor.hom_ext (K₁ := X) (K₂ := Y) (F := moduleTensor R) (c := .up ℤ)
  intro i j h
  exact summand_hom_ext (w i j h)

theorem hom_ext {X Y Z : Comp.{v} R} {f g : tensor X Y ⟶ Z}
    (w : ∀ i j n (h : i + j = n) (x : X.X i) (y : Y.X j),
      f.f n (pure X Y h x y) = g.f n (pure X Y h x y)) : f = g :=
  HomologicalComplex.hom_ext _ _ fun n => term_hom_ext (fun i j h => w i j n h)

private theorem map_sign {M N : ModuleCat.{v} R} (f : M ⟶ N) (s : ℤˣ) (x : M) :
    f (s • x) = s • f x := by
  change f.hom (s • x) = s • f.hom x
  simp only [Units.smul_def, map_zsmul]

private theorem map_add_apply {M N : ModuleCat.{v} R} (f : M ⟶ N) (x y : M) :
    f (x + y) = f x + f y := f.hom.map_add x y

open HomologicalComplex.mapBifunctor in
theorem differential : Specs.DerivedFormalization.CochainTensor.Differential.{u,v} := by
  intro R _ X Y i j n h x y
  let F := moduleTensor R
  let c := ComplexShape.up ℤ
  have h₁ : i + 1 + j = n + 1 := by omega
  have h₂ : i + (j + 1) = n + 1 := by omega
  have hd :
      ι X Y i j n h ≫ (tensor X Y).d n (n + 1) =
        (F.map (X.d i (i + 1))).app (Y.X j) ≫ ι X Y (i + 1) j (n + 1) h₁ +
        i.negOnePow • ((F.obj (X.X i)).map (Y.d j (j + 1)) ≫
          ι X Y i (j + 1) (n + 1) h₂) := by
    rw [d_eq X Y F c, Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq X Y F c (show c.Rel i (i + 1) from rfl) j (n + 1) h₁,
      d₂_eq X Y F c i (show c.Rel j (j + 1) from rfl) (n + 1) h₂]
    exact congrArg (· + _) (one_smul ℤˣ _)
  exact ConcreteCategory.congr_hom hd (x ⊗ₜ[R] y)

theorem differentialSquared : Specs.DerivedFormalization.CochainTensor.DifferentialSquared.{u,v} :=
  fun X Y i j k => (tensor X Y).d_comp_d i j k

theorem map_on_pure : Specs.DerivedFormalization.CochainTensor.MapOnPure.{u,v} := by
  intro R _ X X' Y Y' f g i j n h x y
  exact ConcreteCategory.congr_hom
    (ι_mapBifunctorMap f g (moduleTensor R) (.up ℤ) i j n h) (x ⊗ₜ[R] y)

private instance moduleTensor_additive : (moduleTensor.{u,v} R).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    apply summand_hom_ext
    intro x z
    change (f x + g x) ⊗ₜ[R] z = (f x ⊗ₜ[R] z) + (g x ⊗ₜ[R] z)
    exact TensorProduct.add_tmul _ _ _

private instance moduleTensor_obj_additive (X : ModuleCat.{v} R) :
    ((moduleTensor R).obj X).Additive where
  map_add := by
    intro Y Z f g
    apply summand_hom_ext
    intro x y
    change x ⊗ₜ[R] (f y + g y) = (x ⊗ₜ[R] f y) + (x ⊗ₜ[R] g y)
    exact TensorProduct.tmul_add _ _ _

def mapHomotopy {X X' Y Y' : Comp.{v} R} {f f' : X ⟶ X'} {g g' : Y ⟶ Y'}
    (h : Homotopy f f') (k : Homotopy g g') : Homotopy (map f g) (map f' g') := by
  let _ (M : ModuleCat.{v} R) := moduleTensor_obj_additive M
  let _ : (moduleTensor.{u,v} R).Additive := moduleTensor_additive
  let _ : HasMapBifunctor X' Y (moduleTensor R) (.up ℤ) := inferInstance
  exact (mapBifunctorMapHomotopy₁ h g (moduleTensor R) (.up ℤ)).trans
    (mapBifunctorMapHomotopy₂ f' k (moduleTensor R) (.up ℤ))

theorem homotopyCompatibility : Specs.DerivedFormalization.CochainTensor.HomotopyCompatibility.{u,v} :=
  fun h k => ⟨mapHomotopy h k⟩

def diagonalIso (X Y : Comp.{u} R) : tensor X Y ≅ tensorComplex X Y := Iso.refl _

theorem diagonal : Specs.DerivedFormalization.CochainTensor.Diagonal.{u} := by
  intro R _
  refine ⟨diagonalIso, ?_, ?_⟩
  · intros
    rfl
  · intro X X' Y Y' f g
    change map f g ≫ 𝟙 _ = 𝟙 _ ≫ tensorMap f g
    simpa only [Category.comp_id, Category.id_comp] using (show map f g = tensorMap f g from rfl)

theorem diagonalKFlat : Specs.DerivedFormalization.CochainTensor.DiagonalKFlat.{u} :=
  fun _ => Iff.rfl

private def symmetryTerm (X Y : Comp.{v} R) (n : ℤ) :
    (tensor X Y).X n ⟶ (tensor Y X).X n :=
  mapBifunctorDesc (fun i j h =>
    (i * j).negOnePow • (ModuleCat.ofHom (TensorProduct.comm R (X.X i) (Y.X j)).toLinearMap ≫
      ι Y X j i n (by change i + j = n at h; omega)))

private theorem symmetryTerm_apply (X Y : Comp.{v} R) (i j n : ℤ) (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    symmetryTerm X Y n (pure X Y h x y) =
      (i * j).negOnePow • pure Y X (by omega : j + i = n) y x := by
  have eq := ι_mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := moduleTensor R)
    (c := .up ℤ) (fun a b hab =>
      (a * b).negOnePow • (ModuleCat.ofHom (TensorProduct.comm R (X.X a) (Y.X b)).toLinearMap ≫
        ι Y X b a n (by change a + b = n at hab; omega))) i j h
  exact ConcreteCategory.congr_hom eq (x ⊗ₜ[R] y)

private def symmetryHom (X Y : Comp.{v} R) : tensor X Y ⟶ tensor Y X where
  f := symmetryTerm X Y
  comm' := by
    intro n m hm
    change n + 1 = m at hm
    subst m
    apply term_hom_ext
    intro i j h x y
    simp only [ModuleCat.comp_apply]
    rw [symmetryTerm_apply, map_sign, differential Y X, differential X Y, map_add_apply,
      map_sign, symmetryTerm_apply, symmetryTerm_apply, smul_add]
    simp only [smul_smul, add_mul, mul_add, one_mul, mul_one, Int.negOnePow_add]
    have hs : i.negOnePow * ((i * j).negOnePow * i.negOnePow) = (i * j).negOnePow := by
      calc
        _ = (i * j).negOnePow * (i.negOnePow * i.negOnePow) := by ac_rfl
        _ = _ := by rw [Int.units_mul_self, mul_one]
    rw [hs]
    exact add_comm _ _

private theorem symmetryHom_involutive (X Y : Comp.{v} R) :
    symmetryHom X Y ≫ symmetryHom Y X = 𝟙 (tensor X Y) := by
  apply hom_ext
  intro i j n h x y
  change symmetryTerm Y X n (symmetryTerm X Y n (pure X Y h x y)) = pure X Y h x y
  rw [symmetryTerm_apply, map_sign, symmetryTerm_apply, mul_comm j i, smul_smul,
    Int.units_mul_self, one_smul]

/-- The Koszul symmetry of the total tensor, at any module universe. -/
def symmetryIso (X Y : Comp.{v} R) : tensor X Y ≅ tensor Y X where
  hom := symmetryHom X Y
  inv := symmetryHom Y X
  hom_inv_id := symmetryHom_involutive X Y
  inv_hom_id := symmetryHom_involutive Y X

theorem symmetryIso_apply (X Y : Comp.{v} R) (i j n : ℤ) (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (symmetryIso X Y).hom.f n (pure X Y h x y) =
      (i * j).negOnePow • pure Y X (by omega : j + i = n) y x :=
  symmetryTerm_apply X Y i j n h x y

theorem symmetryIso_natural {X X' Y Y' : Comp.{v} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    map f g ≫ (symmetryIso X' Y').hom = (symmetryIso X Y).hom ≫ map g f := by
  apply hom_ext
  intro i j n h x y
  change (symmetryIso X' Y').hom.f n ((map f g).f n (pure X Y h x y)) =
    (map g f).f n ((symmetryIso X Y).hom.f n (pure X Y h x y))
  rw [map_on_pure, symmetryIso_apply, symmetryIso_apply, map_sign, map_on_pure]

theorem symmetry : Specs.DerivedFormalization.CochainTensor.Symmetry.{u,v} :=
  fun {_} _ => ⟨symmetryIso, symmetryIso_apply, fun f g => symmetryIso_natural f g,
    symmetryHom_involutive⟩

open CochainComplex.HomComplex (Cochain) in
private def conjugateCochain (X Y : Comp.{v} R) (q : ℤ) :
    Cochain X Y q ≃ₗ[R] Cochain ((lift.{t} R).obj X) ((lift.{t} R).obj Y) q where
  toFun f := Cochain.mk fun i j h => (ModuleCat.uliftFunctor.{t, v} R).map (f.v i j h)
  invFun f := Cochain.mk fun i j h => ModuleCat.ofHom
    ((termEquiv.{t} Y j).symm.toLinearMap.comp ((f.v i j h).hom.comp
      (termEquiv.{t} X i).toLinearMap))
  left_inv f := by
    apply Cochain.ext
    intro i j h
    simp only [Cochain.mk_v]
    rfl
  right_inv f := by
    apply Cochain.ext
    intro i j h
    simp only [Cochain.mk_v]
    apply module_hom_ext
    rintro ⟨x⟩
    rfl
  map_add' f g := by
    apply Cochain.ext
    intro i j h
    simp only [Cochain.mk_v, Cochain.add_v, Functor.map_add]
  map_smul' r f := by
    apply Cochain.ext
    intro i j h
    simp only [Cochain.mk_v, Cochain.smul_v, Functor.map_smul, RingHom.id_apply]

open CochainComplex.HomComplex (Cochain) in
private def liftHomTerm (X Y : Comp.{v} R) (q : ℤ) :
    ((lift.{t} R).obj (internalHom X Y)).X q ≅
      (internalHom ((lift.{t} R).obj X) ((lift.{t} R).obj Y)).X q :=
  ((termEquiv.{t} (internalHom X Y) q).symm.trans
    (conjugateCochain.{u,v,t} X Y q)).toModuleIso

open CochainComplex.HomComplex (Cochain) in
private theorem liftHomTerm_apply (X Y : Comp.{v} R) (q i j : ℤ) (h : i + q = j)
    (f : Cochain X Y q) (x : X.X i) :
    ((liftHomTerm.{u,v,t} X Y q).hom (termEquiv.{t} (internalHom X Y) q f)).v i j h
      (termEquiv.{t} X i x) = termEquiv.{t} Y j (f.v i j h x) := by
  change (Cochain.mk (F := (lift.{t} R).obj X) (G := (lift.{t} R).obj Y) (fun a b hab => (ModuleCat.uliftFunctor.{t, v} R).map
    (f.v a b hab))).v i j h (termEquiv.{t} X i x) = _
  rw [Cochain.mk_v]
  rfl

open CochainComplex.HomComplex (Cochain) in
private theorem liftedHomTerm_ext {X Y : Comp.{v} R} {q : ℤ}
    {f g : Cochain ((lift.{t} R).obj X) ((lift.{t} R).obj Y) q}
    (w : ∀ i j (h : i + q = j) (x : X.X i),
      f.v i j h (termEquiv.{t} X i x) = g.v i j h (termEquiv.{t} X i x)) : f = g := by
  apply Cochain.ext
  intro i j h
  apply module_hom_ext
  rintro ⟨x⟩
  exact w i j h x

open CochainComplex.HomComplex (Cochain) in
/-- The internal Hom comparison conjugates each component by the term lift. -/
def liftHomIso (X Y : Comp.{v} R) :
    (lift.{t} R).obj (internalHom X Y) ≅
      internalHom ((lift.{t} R).obj X) ((lift.{t} R).obj Y) :=
  HomologicalComplex.Hom.isoOfComponents (liftHomTerm.{u,v,t} X Y) (by
    intro q r hr
    change q + 1 = r at hr
    subst r
    apply module_hom_ext
    rintro ⟨f⟩
    apply liftedHomTerm_ext
    intro i j hj x
    obtain rfl : j = i + q + 1 := by omega
    change (((internalHom ((lift.{t} R).obj X) ((lift.{t} R).obj Y)).d q (q + 1)
      ((liftHomTerm.{u,v,t} X Y q).hom (termEquiv.{t} (internalHom X Y) q f))).v
      i (i + q + 1) hj (termEquiv.{t} X i x)) =
      (((liftHomTerm.{u,v,t} X Y (q + 1)).hom (((lift.{t} R).obj (internalHom X Y)).d
        q (q + 1) (termEquiv.{t} (internalHom X Y) q f))).v i (i + q + 1) hj
        (termEquiv.{t} X i x))
    rw [internalHom_d_apply, liftHomTerm_apply, lift_d, lift_d, liftHomTerm_apply,
      lift_d, liftHomTerm_apply, internalHom_d_apply]
    rfl)

open CochainComplex.HomComplex (Cochain) in
theorem liftHomIso_apply (X Y : Comp.{v} R) (q i j : ℤ) (h : i + q = j)
    (f : Cochain X Y q) (x : X.X i) :
    ((liftHomIso.{u,v,t} X Y).hom.f q (termEquiv.{t} (internalHom X Y) q f)).v i j h
      (termEquiv.{t} X i x) = termEquiv.{t} Y j (f.v i j h x) :=
  liftHomTerm_apply X Y q i j h f x

theorem liftHomIso_natural {X X' Y Y' : Comp.{v} R} (f : X' ⟶ X) (g : Y ⟶ Y') :
    (lift.{t} R).map (internalHomMap f g) ≫ (liftHomIso.{u,v,t} X' Y').hom =
      (liftHomIso.{u,v,t} X Y).hom ≫ internalHomMap ((lift.{t} R).map f) ((lift.{t} R).map g) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply module_hom_ext
  rintro ⟨z⟩
  apply liftedHomTerm_ext
  intro i j h x
  change ((liftHomIso X' Y').hom.f q (((lift R).map (internalHomMap f g)).f q
      (termEquiv (internalHom X Y) q z))).v i j h (termEquiv X' i x) =
    ((internalHomMap ((lift R).map f) ((lift R).map g)).f q
      ((liftHomIso X Y).hom.f q (termEquiv (internalHom X Y) q z))).v i j h (termEquiv X' i x)
  rw [lift_f, liftHomIso_apply, internalHomMap_apply, internalHomMap_apply, lift_f,
    liftHomIso_apply, lift_f]

theorem liftHom : Specs.DerivedFormalization.CochainTensor.LiftHom.{u,v,t} :=
  fun {_} _ => ⟨liftHomIso, liftHomIso_apply, fun f g => liftHomIso_natural f g⟩

private abbrev TensorDegree (n : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = n}

private def liftTensorCofan (X Y : Comp.{v} R) (n : ℤ) :
    Cofan (fun p : TensorDegree n => (ModuleCat.uliftFunctor.{t, v} R).obj
      (ModuleCat.of R (X.X p.1.1 ⊗[R] Y.X p.1.2))) :=
  Cofan.mk (((lift.{t} R).obj (tensor X Y)).X n) (fun p =>
    (ModuleCat.uliftFunctor.{t, v} R).map (ι X Y p.1.1 p.1.2 n p.2))

open private moduleLiftPreservesColimits from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainCoefficientLift

private def liftTensorCofanIsColimit (X Y : Comp.{v} R) (n : ℤ) :
    IsColimit (liftTensorCofan.{u,v,t} X Y n) := by
  letI := moduleLiftPreservesColimits.{t,v} R (Discrete (TensorDegree n))
  exact isColimitCofanMkObjOfIsColimit (ModuleCat.uliftFunctor.{t,v} R)
    (fun p : TensorDegree n => ModuleCat.of R (X.X p.1.1 ⊗[R] Y.X p.1.2))
    (fun p => ι X Y p.1.1 p.1.2 n p.2) (tensorCofanIsColimit X Y n)

private def liftSummandIso (X Y : Comp.{v} R) (i j : ℤ) :
    (ModuleCat.uliftFunctor.{t,v} R).obj (ModuleCat.of R (X.X i ⊗[R] Y.X j)) ≅
      ModuleCat.of R (((lift.{t} R).obj X).X i ⊗[R] ((lift.{t} R).obj Y).X j) :=
  (ULift.moduleEquiv.trans (TensorProduct.congr (termEquiv.{t} X i) (termEquiv.{t} Y j))).toModuleIso

open Specs.DerivedFormalization.CochainTensor (cofan) in
private def liftTensorTerm (X Y : Comp.{v} R) (n : ℤ) :
    ((lift.{t} R).obj (tensor X Y)).X n ≅
      (tensor ((lift.{t} R).obj X) ((lift.{t} R).obj Y)).X n := by
  let c := liftTensorCofan.{u,v,t} X Y n
  let d := cofan ((lift.{t} R).obj X) ((lift.{t} R).obj Y) n
  let hc : IsColimit c := liftTensorCofanIsColimit X Y n
  let hd : IsColimit d := tensorCofanIsColimit _ _ n
  let e (p : TensorDegree n) := liftSummandIso.{u,v,t} X Y p.1.1 p.1.2
  let hom : c.pt ⟶ d.pt := Cofan.IsColimit.desc hc (fun p => (e p).hom ≫ d.inj p)
  let inv : d.pt ⟶ c.pt := Cofan.IsColimit.desc hd (fun p => (e p).inv ≫ c.inj p)
  have h₁ : hom ≫ inv = 𝟙 c.pt := by
    apply Cofan.IsColimit.hom_ext hc
    intro p
    simp only [hom, inv, Category.assoc, Cofan.IsColimit.fac_assoc, Cofan.IsColimit.fac,
      Iso.hom_inv_id_assoc, Category.comp_id]
  have h₂ : inv ≫ hom = 𝟙 d.pt := by
    apply Cofan.IsColimit.hom_ext hd
    intro p
    simp only [hom, inv, Category.assoc, Cofan.IsColimit.fac_assoc, Cofan.IsColimit.fac,
      Iso.inv_hom_id_assoc, Category.comp_id]
  exact ⟨hom, inv, h₁, h₂⟩

private theorem liftTensorTerm_apply (X Y : Comp.{v} R) (i j n : ℤ) (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (liftTensorTerm.{u,v,t} X Y n).hom (termEquiv.{t} (tensor X Y) n (pure X Y h x y)) =
      pure _ _ h (termEquiv.{t} X i x) (termEquiv.{t} Y j y) := by
  let p : TensorDegree n := ⟨(i, j), h⟩
  have w := Cofan.IsColimit.fac (liftTensorCofanIsColimit.{u,v,t} X Y n)
    (fun p : TensorDegree n => (liftSummandIso.{u,v,t} X Y p.1.1 p.1.2).hom ≫
      ι ((lift.{t} R).obj X) ((lift.{t} R).obj Y) p.1.1 p.1.2 n p.2) p
  exact ConcreteCategory.congr_hom w (ULift.up (x ⊗ₜ[R] y))

private theorem liftedTensorTerm_ext {X Y : Comp.{v} R} {n : ℤ} {M : ModuleCat.{max v t} R}
    {f g : ((lift.{t} R).obj (tensor X Y)).X n ⟶ M}
    (w : ∀ i j (h : i + j = n) (x : X.X i) (y : Y.X j),
      f (termEquiv.{t} (tensor X Y) n (pure X Y h x y)) =
        g (termEquiv.{t} (tensor X Y) n (pure X Y h x y))) : f = g := by
  apply Cofan.IsColimit.hom_ext (liftTensorCofanIsColimit.{u,v,t} X Y n)
  rintro ⟨⟨i, j⟩, h⟩
  apply module_hom_ext
  rintro ⟨z⟩
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact w i j h x y
  | add z z' hz hz' =>
      exact (map_add_apply _ _ _).trans ((congrArg₂ (· + ·) hz hz').trans (map_add_apply _ _ _).symm)

private theorem termEquiv_sign (C : Comp.{v} R) (n : ℤ) (s : ℤˣ) (z : C.X n) :
    termEquiv.{t} C n (s • z) = s • termEquiv.{t} C n z := rfl

/-- The comparison with coefficient lift on both tensor factors. -/
def liftTensorIso (X Y : Comp.{v} R) :
    (lift.{t} R).obj (tensor X Y) ≅ tensor ((lift.{t} R).obj X) ((lift.{t} R).obj Y) :=
  HomologicalComplex.Hom.isoOfComponents (liftTensorTerm.{u,v,t} X Y) (by
    intro n m hm
    change n + 1 = m at hm
    subst m
    apply liftedTensorTerm_ext
    intro i j h x y
    change (tensor ((lift.{t} R).obj X) ((lift.{t} R).obj Y)).d n (n + 1)
      ((liftTensorTerm.{u,v,t} X Y n).hom (termEquiv.{t} (tensor X Y) n (pure X Y h x y))) =
      (liftTensorTerm.{u,v,t} X Y (n+1)).hom
        (((lift.{t} R).obj (tensor X Y)).d n (n+1) (termEquiv.{t} (tensor X Y) n (pure X Y h x y)))
    rw [liftTensorTerm_apply, differential, lift_d, lift_d, lift_d, differential]
    rw [map_add]
    rw [map_add_apply, termEquiv_sign, map_sign, liftTensorTerm_apply, liftTensorTerm_apply])

theorem liftTensorIso_apply (X Y : Comp.{v} R) (i j n : ℤ) (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (liftTensorIso.{u,v,t} X Y).hom.f n (termEquiv.{t} (tensor X Y) n (pure X Y h x y)) =
      pure _ _ h (termEquiv.{t} X i x) (termEquiv.{t} Y j y) :=
  liftTensorTerm_apply X Y i j n h x y

theorem liftTensorIso_natural {X X' Y Y' : Comp.{v} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    (lift.{t} R).map (map f g) ≫ (liftTensorIso.{u,v,t} X' Y').hom =
      (liftTensorIso.{u,v,t} X Y).hom ≫ map ((lift.{t} R).map f) ((lift.{t} R).map g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply liftedTensorTerm_ext
  intro i j h x y
  change (liftTensorIso.{u,v,t} X' Y').hom.f n (((lift.{t} R).map (map f g)).f n
    (termEquiv.{t} (tensor X Y) n (pure X Y h x y))) =
    (map ((lift.{t} R).map f) ((lift.{t} R).map g)).f n ((liftTensorIso.{u,v,t} X Y).hom.f n
      (termEquiv.{t} (tensor X Y) n (pure X Y h x y)))
  rw [lift_f, map_on_pure, liftTensorIso_apply, liftTensorIso_apply, map_on_pure, lift_f, lift_f]

theorem liftTensor : Specs.DerivedFormalization.CochainTensor.LiftTensor.{u,v,t} :=
  fun {_} _ => ⟨liftTensorIso, liftTensorIso_apply, fun f g => liftTensorIso_natural f g⟩

end

end DerivedFormalization.CochainTensor
