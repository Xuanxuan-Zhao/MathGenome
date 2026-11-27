import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurAlgebras
import Mathlib.RingTheory.Flat.Stability
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace DerivedFormalization.Affine.FlatCotangentAmitsurDiagram

open Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram
open Specs.DerivedFormalization.Affine.CotangentBaseChange
  (Differential FlatComparison IsAssociator IsSymbolMap OrdinaryFlat extend symbol symbolTensor)
open Specs.DerivedFormalization.Affine.CotangentComplex (Model)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor act regular restrict restrictFunctor term)

noncomputable section

universe u v t w

set_option maxHeartbeats 450000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [CharZero k]

private theorem powerFlat {A C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Module.Flat A C] (p : ℕ) : Module.Flat A (power A C p) := by
  have h₀ : Module.Flat A (power A C 0) := by
    obtain ⟨e, _, _⟩ := Descent.AmitsurAlgebras.onePower A C
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  induction p with
  | zero => exact h₀
  | succ p hp =>
    letI : Module.Flat A (power A C p) := hp
    letI : Module.Flat A (power A C 0) := h₀
    obtain ⟨e, _⟩ := Descent.AmitsurAlgebras.appendPowers A C (p + 1) 1
    exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

section Concentrated

variable {X Y : NonpositiveCDGA.{u,w} k}

private abbrev atZero (f : X ⟶ Y) : X.DegreeZero →ₐ[k] Y.DegreeZero :=
  CommDGAlgebra.degreeZeroMap (f : X.toCommDGAlgebra ⟶ Y.toCommDGAlgebra)

private def concentratedLinear (g : X.DegreeZero →ₐ[k] Y.DegreeZero) (i : ℤ) :
    X.complex.X i ⟶ Y.complex.X i :=
  if h : i = 0 then
    eqToHom (congrArg X.complex.X h) ≫ ModuleCat.ofHom g.toLinearMap ≫
      eqToHom (congrArg Y.complex.X h.symm)
  else 0

@[simp] private theorem concentratedLinear_zero (g : X.DegreeZero →ₐ[k] Y.DegreeZero) :
    concentratedLinear g 0 = ModuleCat.ofHom g.toLinearMap := by
  simp [concentratedLinear]

/-- A map from a complex concentrated in degree zero is the algebra map on
that degree, with zero components elsewhere. -/
private def concentratedMap (hX : ∀ i : ℤ, i ≠ 0 → Subsingleton (X.complex.X i))
    (g : X.DegreeZero →ₐ[k] Y.DegreeZero) : X ⟶ Y where
  chainMap :=
    { f := concentratedLinear g
      comm' := by
        intro i j hij
        by_cases hi : i = 0
        · subst i
          have hj : j = 1 := by
            change (0 : ℤ) + 1 = j at hij
            omega
          subst j
          apply ModuleCat.hom_ext
          ext x
          change Y.complex.d 0 1 (concentratedLinear g 0 x) =
            concentratedLinear g 1 (X.complex.d 0 1 x)
          rw [NonpositiveCDGA.d_zero_apply Y, NonpositiveCDGA.d_zero_apply X, map_zero]
        · apply ModuleCat.hom_ext
          ext x
          rw [(hX i hi).elim x (0 : X.complex.X i)]
          simp only [map_zero] }
  map_one := by
    change concentratedLinear g 0 X.one = Y.one
    rw [concentratedLinear_zero]
    exact g.map_one
  map_mul := by
    intro i j n h x y
    change concentratedLinear g n (X.mul i j n h x y) =
      Y.mul i j n h (concentratedLinear g i x) (concentratedLinear g j y)
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        have hn : n = 0 := by omega
        subst n
        simp only [concentratedLinear_zero]
        exact g.map_mul x y
      · rw [(hX j hj).elim y (0 : X.complex.X j)]
        simp only [map_zero]
    · rw [(hX i hi).elim x (0 : X.complex.X i)]
      simp only [map_zero, LinearMap.zero_apply]

private theorem concentratedMap_zero (hX : ∀ i : ℤ, i ≠ 0 → Subsingleton (X.complex.X i))
    (g : X.DegreeZero →ₐ[k] Y.DegreeZero) (x : X.DegreeZero) :
    atZero (concentratedMap hX g) x = g x := by
  change concentratedLinear g 0 x = _
  rw [concentratedLinear_zero]
  rfl

private theorem concentratedHom_ext (hX : ∀ i : ℤ, i ≠ 0 → Subsingleton (X.complex.X i))
    {f g : X ⟶ Y} (h : ∀ x : X.DegreeZero, atZero f x = atZero g x) : f = g := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  by_cases hi : i = 0
  · subst i
    exact h x
  · rw [(hX i hi).elim x (0 : X.complex.X i)]
    simp only [map_zero]

private theorem ordinaryConcentrated (R : CommAlgCat.{w} k) (i : ℤ) (hi : i ≠ 0) :
    Subsingleton ((NonpositiveCDGA.ordinary R).complex.X i) :=
  ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of k R) i hi)

end Concentrated

section TransportedRings

variable {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

private def stalk (k : Type u) [Field k] [CharZero k] (R : Type v)
    [CommRing R] [Algebra k R] := transported.{u,v,t} k R

private theorem stalkConcentrated (R : Type v) [CommRing R] [Algebra k R]
    (i : ℤ) (hi : i ≠ 0) : Subsingleton ((stalk.{u,v,t} k R).complex.X i) :=
  ⟨fun x y => ULift.ext ((ordinaryConcentrated (CommAlgCat.of k R) i hi).elim x.down y.down)⟩

private def stalkZeroEquiv (R : Type v) [CommRing R] [Algebra k R] :
    (stalk.{u,v,t} k R).DegreeZero ≃ₐ[k] R where
  toFun x := x.down
  invFun x := ULift.up x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change c • (1 : R) = c • (1 : R)
    rfl

private def stalkHom {D : NonpositiveCDGA.{u,max v t} k} (f : R →ₐ[k] D.DegreeZero) :
    stalk.{u,v,t} k R ⟶ D :=
  concentratedMap (stalkConcentrated R) (f.comp (stalkZeroEquiv R).toAlgHom)

private theorem stalkHom_zero {D : NonpositiveCDGA.{u,max v t} k}
    (f : R →ₐ[k] D.DegreeZero) (x : R) :
    atZero (stalkHom f) (ULift.up x) = f x := by
  unfold stalkHom
  rw [concentratedMap_zero]
  rfl

private def readStalk {D : NonpositiveCDGA.{u,max v t} k}
    (f : stalk.{u,v,t} k R ⟶ D) : R →ₐ[k] D.DegreeZero :=
  (atZero f).comp (stalkZeroEquiv R).symm.toAlgHom

private abbrev liftedOrdinary (R : Type v) [CommRing R] [Algebra k R] :
    NonpositiveCDGA.{u,max v t} k :=
  NonpositiveCDGA.ordinary (CommAlgCat.of k (ULift.{t} R))

private def stalkOrdinaryIso (R : Type v) [CommRing R] [Algebra k R] :
    stalk.{u,v,t} k R ≅ liftedOrdinary.{u,v,t} (k := k) R := by
  let e : (stalk.{u,v,t} k R).DegreeZero ≃ₐ[k]
      (liftedOrdinary.{u,v,t} (k := k) R).DegreeZero :=
    { toFun := fun x => ULift.up x.down
      invFun := fun x => ULift.up x.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let hR := stalkConcentrated (k := k) R
  let hU := ordinaryConcentrated (CommAlgCat.of k (ULift.{t} R))
  exact
    { hom := concentratedMap hR e.toAlgHom
      inv := concentratedMap hU e.symm.toAlgHom
      hom_inv_id := concentratedHom_ext hR (fun x => by
        change atZero (concentratedMap hU e.symm.toAlgHom)
          (atZero (concentratedMap hR e.toAlgHom) x) = x
        rw [concentratedMap_zero, concentratedMap_zero]
        exact e.symm_apply_apply x)
      inv_hom_id := concentratedHom_ext hU (fun x => by
        change atZero (concentratedMap hR e.toAlgHom)
          (atZero (concentratedMap hU e.symm.toAlgHom) x) = x
        rw [concentratedMap_zero, concentratedMap_zero]
        exact e.apply_symm_apply x) }

private def liftedAlgHom (f : R →ₐ[k] S) : ULift.{t} R →ₐ[k] ULift.{t} S where
  toFun x := ULift.up (f x.down)
  map_one' := ULift.ext f.map_one
  map_zero' := ULift.ext f.map_zero
  map_mul' x y := ULift.ext (f.map_mul x.down y.down)
  map_add' x y := ULift.ext (f.map_add x.down y.down)
  commutes' c := ULift.ext (f.commutes c)

private theorem stalkOrdinaryIso_zero (R : Type v) [CommRing R] [Algebra k R]
    (x : (stalk.{u,v,t} k R).DegreeZero) :
    atZero (stalkOrdinaryIso (k := k) R).hom x = ULift.up x.down := by
  unfold stalkOrdinaryIso
  rw [concentratedMap_zero]
  rfl

private theorem stalkOrdinaryIso_natural (f : R →ₐ[k] S) :
    transportedMap.{u,v,t} f ≫ (stalkOrdinaryIso S).hom =
      (stalkOrdinaryIso R).hom ≫ NonpositiveCDGA.ordinaryMap (CommAlgCat.ofHom (liftedAlgHom f)) := by
  apply concentratedHom_ext (X := stalk.{u,v,t} k R) (stalkConcentrated R)
  intro x
  let eR := stalkOrdinaryIso.{u,v,t} (k := k) R
  let eS := stalkOrdinaryIso.{u,v,t} (k := k) S
  change eS.hom.chainMap.f 0 (ULift.up (f x.down)) =
    ULift.up (f ((eR.hom.chainMap.f 0 x).down))
  have er := stalkOrdinaryIso_zero.{u,v,t} (k := k) R x
  have es := stalkOrdinaryIso_zero.{u,v,t} (k := k) S (ULift.up (f x.down))
  change eR.hom.chainMap.f 0 x = ULift.up x.down at er
  change eS.hom.chainMap.f 0 (ULift.up (f x.down)) = ULift.up (f x.down) at es
  rw [er, es]

private theorem ordinaryFlat_of_flat [Algebra R S] [IsScalarTower k R S] [Module.Flat R S] :
    OrdinaryFlat (transportedMap.{u,v,t} (IsScalarTower.toAlgHom k R S)) := by
  let f := IsScalarTower.toAlgHom k R S
  refine ⟨CommAlgCat.of k (ULift.{t} R), CommAlgCat.of k (ULift.{t} S),
    CommAlgCat.ofHom (liftedAlgHom f), stalkOrdinaryIso R, stalkOrdinaryIso S,
    stalkOrdinaryIso_natural f, ?_⟩
  let lifted : Algebra (ULift.{t} R) (ULift.{t} S) := (liftedAlgHom f).toRingHom.toAlgebra
  change @Module.Flat (ULift.{t} R) (ULift.{t} S) _ _ lifted.toModule
  have e : lifted.toModule = ULift.module := by
    apply Module.ext'
    intro r s
    apply ULift.ext
    exact (Algebra.smul_def (R := R) r.down s.down).symm
  rw [e]
  exact (Module.Flat.ulift_left_iff (R := R) (M := ULift.{t} S)).2 inferInstance

end TransportedRings

section OrdinaryPushout

variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
variable [IsScalarTower k A B] [IsScalarTower k A C]

private abbrev pushoutLeft : B →ₐ[k] B ⊗[A] C :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[A] C).restrictScalars k

private abbrev pushoutRight : C →ₐ[k] B ⊗[A] C :=
  (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).restrictScalars k

private abbrev leftBase := IsScalarTower.toAlgHom k A B
private abbrev rightBase := IsScalarTower.toAlgHom k A C

private def tensorRingDesc {D : Type w} [CommRing D] [Algebra k D]
    (l : B →ₐ[k] D) (r : C →ₐ[k] D)
    (comm : ∀ x : A, l (algebraMap A B x) = r (algebraMap A C x)) :
    B ⊗[A] C →ₐ[k] D := by
  let a : A →ₐ[k] D := l.comp (IsScalarTower.toAlgHom k A B)
  letI : Algebra A D := a.toRingHom.toAlgebra
  letI : IsScalarTower k A D := IsScalarTower.of_algHom a
  let l' : B →ₐ[A] D := { l.toRingHom with commutes' := fun _ => rfl }
  let r' : C →ₐ[A] D := { r.toRingHom with commutes' := fun x => (comm x).symm }
  exact (Algebra.TensorProduct.lift l' r' fun x y => mul_comm _ _).restrictScalars k

omit [CharZero k] [IsScalarTower k A C] in
private theorem tensorRingDesc_tmul {D : Type w} [CommRing D] [Algebra k D]
    (l : B →ₐ[k] D) (r : C →ₐ[k] D)
    (comm : ∀ x : A, l (algebraMap A B x) = r (algebraMap A C x))
    (b : B) (c : C) :
    tensorRingDesc l r comm (b ⊗ₜ[A] c) = l b * r c := rfl

omit [CharZero k] [Algebra k C] [IsScalarTower k A C] in
private theorem tensorRingHom_ext {D : Type w} [CommRing D] [Algebra k D]
    {l r : B ⊗[A] C →ₐ[k] D}
    (hb : ∀ b : B, l (b ⊗ₜ[A] (1 : C)) = r (b ⊗ₜ[A] (1 : C)))
    (hc : ∀ c : C, l ((1 : B) ⊗ₜ[A] c) = r ((1 : B) ⊗ₜ[A] c)) : l = r := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    have h : b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, map_mul, hb, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private abbrev ordinaryPushoutLeft : stalk.{u,v,t} k B ⟶ stalk.{u,v,t} k (B ⊗[A] C) :=
  transportedMap.{u,v,t} (pushoutLeft (A := A))

private abbrev ordinaryPushoutRight : stalk.{u,v,t} k C ⟶ stalk.{u,v,t} k (B ⊗[A] C) :=
  transportedMap.{u,v,t} (pushoutRight (A := A))

private theorem ordinaryTensorComm
    (s : PushoutCocone (transportedMap.{u,v,t} (leftBase (k := k) (A := A) (B := B)))
      (transportedMap.{u,v,t} (rightBase (k := k) (A := A) (C := C))))
    (x : A) :
    readStalk s.inl (algebraMap A B x) = readStalk s.inr (algebraMap A C x) :=
  congrArg (fun f => atZero f (ULift.up x)) s.condition

private def ordinaryTensorDesc
    (s : PushoutCocone (transportedMap.{u,v,t} (leftBase (k := k) (A := A) (B := B)))
      (transportedMap.{u,v,t} (rightBase (k := k) (A := A) (C := C)))) :
    stalk.{u,v,t} k (B ⊗[A] C) ⟶ s.pt :=
  stalkHom (tensorRingDesc (readStalk s.inl) (readStalk s.inr) (ordinaryTensorComm s))

private theorem ordinaryTensorPushout :
    IsPushout (transportedMap.{u,v,t} (leftBase (k := k) (A := A) (B := B)))
      (transportedMap.{u,v,t} (rightBase (k := k) (A := A) (C := C)))
      (ordinaryPushoutLeft.{u,v,t} (k := k) (A := A) (B := B) (C := C))
      (ordinaryPushoutRight.{u,v,t} (k := k) (A := A) (B := B) (C := C)) := by
  have comm : transportedMap.{u,v,t} (leftBase (k := k) (A := A) (B := B)) ≫
      ordinaryPushoutLeft.{u,v,t} (k := k) (A := A) (B := B) (C := C) =
      transportedMap.{u,v,t} (rightBase (k := k) (A := A) (C := C)) ≫ ordinaryPushoutRight := by
    apply concentratedHom_ext (stalkConcentrated A)
    intro x
    exact congrArg ULift.up (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := C) x.down)
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk comm ordinaryTensorDesc ?_ ?_ ?_)
  · intro s
    apply concentratedHom_ext (stalkConcentrated B)
    intro x
    let p := readStalk s.inl
    let q := readStalk s.inr
    change atZero (stalkHom (tensorRingDesc p q (ordinaryTensorComm s))) (ULift.up (x.down ⊗ₜ[A] (1 : C))) = p x.down
    rw [stalkHom_zero, tensorRingDesc_tmul, map_one, mul_one]
  · intro s
    apply concentratedHom_ext (stalkConcentrated C)
    intro x
    let p := readStalk s.inl
    let q := readStalk s.inr
    change atZero (stalkHom (tensorRingDesc p q (ordinaryTensorComm s))) (ULift.up ((1 : B) ⊗ₜ[A] x.down)) = q x.down
    rw [stalkHom_zero, tensorRingDesc_tmul, map_one, one_mul]
  · intro s m hl hr
    apply concentratedHom_ext (stalkConcentrated (B ⊗[A] C))
    intro x
    change readStalk m x.down = readStalk (ordinaryTensorDesc s) x.down
    apply DFunLike.congr_fun
    apply tensorRingHom_ext
    · intro b
      have e := congrArg (fun f => atZero f (ULift.up b)) hl
      change readStalk m (b ⊗ₜ[A] (1 : C)) = readStalk s.inl b at e
      change _ = atZero (ordinaryTensorDesc s) (ULift.up (b ⊗ₜ[A] (1 : C)))
      unfold ordinaryTensorDesc
      rw [e, stalkHom_zero, tensorRingDesc_tmul, map_one, mul_one]
    · intro c
      have e := congrArg (fun f => atZero f (ULift.up c)) hr
      change readStalk m ((1 : B) ⊗ₜ[A] c) = readStalk s.inr c at e
      change _ = atZero (ordinaryTensorDesc s) (ULift.up ((1 : B) ⊗ₜ[A] c))
      unfold ordinaryTensorDesc
      rw [e, stalkHom_zero, tensorRingDesc_tmul, map_one, one_mul]

end OrdinaryPushout

section StrictModules

open CochainComplex.HomComplex (Cochain)
open private tensor_ext scalarExtend scalarExtend_pure unit_tensor_action symbol_commutes representStrict
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
open private differentialMap_ext unitTensor unitTensor_apply
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex
open private isoOfDegreewiseBijective isoOfDegreewiseBijective_hom
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellLift

variable {P Q D : NonpositiveCDGA.{u,w} k}

local notation "ι" => NonpositiveCDGA.toCommDGAlgebra

private abbrev canonicalTensor (k : Type u) [Field k] [CharZero k] : ModuleTensor.{u,w} k :=
  Tensor.moduleTensorModel k

variable (T : ModuleTensor.{u,w} k)
variable (F : ∀ {U V : CommDGAlgebra.{u,w} k} (f : U ⟶ V) (N : V.Module), T.Formulas f N)

private def tensorLinearEquiv (g : P ⟶ Q) (M : P.Module) (n : ℤ) :
    term ((extend (canonicalTensor k) g).obj M) n ≃ₗ[k] term ((extend T g).obj M) n :=
  ((canonicalTensor k).degree (g : ι P ⟶ ι Q) M (regular (ι Q)) n).symm.trans
    (T.degree (g : ι P ⟶ ι Q) M (regular (ι Q)) n)

private theorem tensorLinearEquiv_pure (g : P ⟶ Q) (M : P.Module)
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : Q.complex.X j) :
    tensorLinearEquiv T g M n ((canonicalTensor k).tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x y) =
      T.tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x y := rfl

include F in
private def tensorHom (g : P ⟶ Q) (M : P.Module) :
    (extend (canonicalTensor k) g).obj M ⟶ (extend T g).obj M := by
  let L := tensorLinearEquiv T g M
  let M₀ := (extend (canonicalTensor k) g).obj M
  let M₁ := (extend T g).obj M
  let G := F (g : ι P ⟶ ι Q) (regular (ι Q))
  let G₀ := Tensor.moduleTensor_formulas (g : ι P ⟶ ι Q) (regular (ι Q))
  refine Tensor.homOfDegrees (fun n => (L n).toLinearMap) ?_ ?_
  · intro n x
    have e : ((M₁.complex ()).d n (n+1)).hom.comp (L n).toLinearMap =
        (L (n+1)).toLinearMap.comp ((M₀.complex ()).d n (n+1)).hom := by
      apply Tensor.pure_ext
      intro i j h y z
      let z₀ := (canonicalTensor k).tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h y z
      change (M₁.complex ()).d n (n+1) (tensorLinearEquiv T g M n z₀) =
        tensorLinearEquiv T g M (n+1) ((M₀.complex ()).d n (n+1) z₀)
      dsimp only [z₀]
      rw [tensorLinearEquiv_pure, G.differential, G₀.differential]
      simp only [map_add, Units.smul_def, map_zsmul, tensorLinearEquiv_pure]
    exact LinearMap.congr_fun e x
  · intro n l q h x b
    have e : (L q).toLinearMap.comp ((act M₀ n l q h).flip b) =
        ((act M₁ n l q h).flip b).comp (L n).toLinearMap := by
      apply Tensor.pure_ext
      intro i j e y z
      let z₀ := (canonicalTensor k).tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n e y z
      change tensorLinearEquiv T g M q (act M₀ n l q h z₀ b) =
        act M₁ n l q h (tensorLinearEquiv T g M n z₀) b
      dsimp only [z₀]
      rw [tensorLinearEquiv_pure, G₀.action, G.action, tensorLinearEquiv_pure]
    exact LinearMap.congr_fun e x

include F in
private def tensorIso (g : P ⟶ Q) (M : P.Module) :
    (extend (canonicalTensor k) g).obj M ≅ (extend T g).obj M :=
  isoOfDegreewiseBijective (tensorHom T F g M) (fun a n => by cases a; exact (tensorLinearEquiv T g M n).bijective)

include F in
private theorem tensorIso_hom_pure (g : P ⟶ Q) (M : P.Module) (i j n : ℤ) (h : i+j=n)
    (x : term M i) (y : Q.complex.X j) :
    ((tensorIso T F g M).hom.app ()).f n
      ((canonicalTensor k).tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x y) =
      T.tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x y := by
  rw [tensorIso, isoOfDegreewiseBijective_hom]
  rfl

private theorem isoInv_apply {U V : Q.Module} (e : U ≅ V) (n : ℤ) (x : term U n) :
    (e.inv.app ()).f n ((e.hom.app ()).f n x) = x :=
  CategoryTheory.congr_fun (congrArg (fun m : U ⟶ U => (m.app ()).f n) e.hom_inv_id) x

include F in
private theorem tensorIso_inv_pure (g : P ⟶ Q) (M : P.Module) (i j n : ℤ) (h : i+j=n)
    (x : term M i) (y : Q.complex.X j) :
    ((tensorIso T F g M).inv.app ()).f n (T.tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x y) =
      (canonicalTensor k).tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x y := by
  rw [← tensorIso_hom_pure T F g M]
  exact isoInv_apply (tensorIso T F g M) n _

private theorem symbolMapExists {U : NonpositiveCDGA.{u,w} k} {f : U ⟶ P}
    (O O' : Differential f) :
    ∃ L : O.module ⟶ O'.module, ∀ i x, (L.app ()).f i (symbol O i x) = symbol O' i x := by
  let chain : P.complex ⟶ O'.module.complex () :=
    CochainComplex.ofHom (fun i => O'.symbol.val.v i i (add_zero i)) (by
      intro i
      exact ModuleCat.hom_ext (LinearMap.ext (symbol_commutes _ O'.closed i)))
  have eq : Cochain.ofHom chain = O'.symbol.val := by
    apply Cochain.ext
    intro i j h
    obtain rfl : i = j := by omega
    rfl
  exact representStrict O O'.module chain (eq.symm ▸ O'.symbol.property)

private theorem differentialIsoExists {U : NonpositiveCDGA.{u,w} k} {f : U ⟶ P}
    (O O' : Differential f) :
    ∃ e : O.module ≅ O'.module, ∀ i x, (e.hom.app ()).f i (symbol O i x) = symbol O' i x := by
  obtain ⟨L, hL⟩ := symbolMapExists O O'
  obtain ⟨K, hK⟩ := symbolMapExists O' O
  refine ⟨⟨L, K, ?_, ?_⟩, hL⟩
  · apply differentialMap_ext O
    intro i x
    change (K.app ()).f i ((L.app ()).f i (symbol O i x)) = symbol O i x
    rw [hL, hK]
  · apply differentialMap_ext O'
    intro i x
    change (L.app ()).f i ((K.app ()).f i (symbol O' i x)) = symbol O' i x
    rw [hK, hL]

include F in
/-- Extend coefficients strictly along a commuting triangle, fixing the first
factor of the tensor. -/
private def scalarMap (g : P ⟶ Q) (d : Q ⟶ D) (g' : P ⟶ D) (h : g ≫ d = g')
    (M : P.Module) :
    (extend T g).obj M ⟶ restrict (d : ι Q ⟶ ι D) ((extend T g').obj M) := by
  let U := unitTensor (g' : ι P ⟶ ι D) M (F g' (regular (ι D)))
  refine scalarExtend T (F g (regular (ι Q))) ⟨U.app, ?_⟩
  rintro ⟨⟩ ⟨⟩ i j n e x a
  change (U.app ()).f n (act M i j n e x a) =
    act ((extend T g').obj M) i j n e ((U.app ()).f i x) (d.chainMap.f j (g.chainMap.f j a))
  have h₀ := CategoryTheory.congr_fun (congrArg (fun m : P ⟶ D => m.chainMap.f j) h) a
  change d.chainMap.f j (g.chainMap.f j a) = g'.chainMap.f j a at h₀
  rw [h₀]
  exact U.comm_act (a := ()) (b := ()) i j n e x a

include F in
private theorem scalarMap_pure (g : P ⟶ Q) (d : Q ⟶ D) (g' : P ⟶ D) (h : g ≫ d = g')
    (M : P.Module) (i j n : ℤ) (e : i+j=n) (x : term M i) (a : Q.complex.X j) :
    ((scalarMap T F g d g' h M).app ()).f n (T.tmul (g : ι P ⟶ ι Q)
        (N := regular (ι Q)) i j n e x a) =
      T.tmul (g' : ι P ⟶ ι D) (N := regular (ι D)) i j n e x (d.chainMap.f j a) := by
  unfold scalarMap
  rw [scalarExtend_pure]
  change act ((extend T g').obj M) i j n e
    ((unitTensor (g' : ι P ⟶ ι D) M (F g' (regular (ι D)))).app () |>.f i x)
      (d.chainMap.f j a) = _
  rw [unitTensor_apply, unit_tensor_action T (F g' (regular (ι D)))]

include F in
private theorem extendedSymbol_ext {U : NonpositiveCDGA.{u,w} k} {f : U ⟶ P}
    (O : Differential f) (g : P ⟶ Q) {N : Q.Module}
    {L K : (extend T g).obj O.module ⟶ N}
    (h : ∀ (i j n : ℤ) (e : i+j=n) (x : P.complex.X i) (y : Q.complex.X j),
      (L.app ()).f n (symbolTensor T O g i j n e x y) =
        (K.app ()).f n (symbolTensor T O g i j n e x y)) : L = K := by
  let G := F (g : ι P ⟶ ι Q) (regular (ι Q))
  let U₀ := unitTensor (g : ι P ⟶ ι Q) O.module G
  let res := restrictFunctor (g : ι P ⟶ ι Q)
  have e : U₀ ≫ res.map L = U₀ ≫ res.map K := by
    apply differentialMap_ext O
    intro i x
    exact h i 0 i (add_zero i) x Q.one
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply tensor_ext T
  intro i j s x y
  change (L.app ()).f n (T.tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n s x y) = _
  rw [← unit_tensor_action T G i j n s x y, L.comm_act, K.comm_act]
  have e₀ := CategoryTheory.congr_fun
    (congrArg (fun c : O.module ⟶ res.obj N => (c.app ()).f i) e) x
  exact congrArg (fun a => act N i j n s a y) e₀


include F in
private def extendIso (g : P ⟶ Q) {L N : P.Module} (e : L ≅ N) :
    (extend (canonicalTensor k) g).obj L ≅ (extend T g).obj N :=
  tensorIso T F g L ≪≫ (extend T g).mapIso e

include F in
private theorem extendIso_hom_pure (g : P ⟶ Q) {L N : P.Module} (e : L ≅ N)
    (i j n : ℤ) (h : i+j=n) (x : term L i) (a : Q.complex.X j) :
    ((extendIso T F g e).hom.app ()).f n
      ((canonicalTensor k).tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x a) =
      T.tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h ((e.hom.app ()).f i x) a := by
  change (((extend T g).map e.hom).app ()).f n
    (((tensorIso T F g L).hom.app ()).f n _) = _
  rw [tensorIso_hom_pure, (F g (regular (ι Q))).first]

include F in
private theorem extendIso_inv_pure (g : P ⟶ Q) {L N : P.Module} (e : L ≅ N)
    (i j n : ℤ) (h : i+j=n) (x : term N i) (a : Q.complex.X j) :
    ((extendIso T F g e).inv.app ()).f n
      (T.tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h x a) =
      (canonicalTensor k).tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i j n h ((e.inv.app ()).f i x) a := by
  change ((tensorIso T F g L).inv.app ()).f n
    ((((extend T g).map e.inv).app ()).f n _) = _
  rw [(F g (regular (ι Q))).first, tensorIso_inv_pure]

include F in
private def extensionAssociator (g : P ⟶ Q) (h : Q ⟶ D) (M : P.Module) :
    (extend T h).obj ((extend T g).obj M) ≅ (extend T (g ≫ h)).obj M :=
  (extendIso T F h (tensorIso T F g M)).symm ≪≫
    Tensor.baseChangeComp (g : ι P ⟶ ι Q) (h : ι Q ⟶ ι D) M ≪≫ tensorIso T F (g ≫ h) M

include F in
private theorem extensionAssociator_pure (g : P ⟶ Q) (h : Q ⟶ D) (M : P.Module) :
    IsAssociator T g h M (extensionAssociator T F g h M) := by
  intro i j l m n hm hn x y z
  change ((tensorIso T F (g ≫ h) M).hom.app ()).f n
    (((Tensor.baseChangeComp (g : ι P ⟶ ι Q) (h : ι Q ⟶ ι D) M).hom.app ()).f n
      (((extendIso T F h (tensorIso T F g M)).inv.app ()).f n _)) = _
  rw [extendIso_inv_pure, tensorIso_inv_pure]
  have e := Tensor.baseChangeComp_pure (g : ι P ⟶ ι Q) (h : ι Q ⟶ ι D)
    M i j l m n hm hn x y z
  change ((Tensor.baseChangeComp (g : ι P ⟶ ι Q) (h : ι Q ⟶ ι D) M).hom.app ()).f n
    ((canonicalTensor k).tmul (h : ι Q ⟶ ι D)
    (N := regular (ι D)) m l n hn ((canonicalTensor k).tmul (g : ι P ⟶ ι Q)
      (N := regular (ι Q)) i j m hm x y) z) =
    (canonicalTensor k).tmul (g ≫ h : ι P ⟶ ι D) (N := regular (ι D)) i (j+l) n (by omega) x
      (D.mul j l (j+l) rfl (h.chainMap.f j y) z) at e
  exact (congrArg (fun z => ((tensorIso T F (g ≫ h) M).hom.app ()).f n z) e).trans
    (tensorIso_hom_pure T F (g ≫ h) M _ _ _ _ _ _)

private theorem multiply_unit (h : Q ⟶ D) (j l : ℤ) (e : 0+j=l) (z : D.complex.X j) :
    D.mul 0 j l e (h.chainMap.f 0 Q.one) z =
      Semifree.castDegree D.complex.X (show j = l by omega) z := by
  obtain rfl : j = l := by omega
  rw [h.map_one]
  exact D.toDGAlgebra.id_comp j z

private theorem associator_unit (g : P ⟶ Q) (h : Q ⟶ D) (M : P.Module)
    (e : (extend T h).obj ((extend T g).obj M) ≅ (extend T (g ≫ h)).obj M)
    (he : IsAssociator T g h M e) (i j n : ℤ) (hn : i+j=n)
    (x : term M i) (z : D.complex.X j) :
    (e.hom.app ()).f n (T.tmul (h : ι Q ⟶ ι D) (N := regular (ι D)) i j n hn
        (T.tmul (g : ι P ⟶ ι Q) (N := regular (ι Q)) i 0 i (add_zero i) x Q.one) z) =
      T.tmul (g ≫ h : ι P ⟶ ι D) (N := regular (ι D)) i j n hn x z := by
  refine (he i 0 j i n (add_zero i) hn x Q.one z).trans ?_
  have eq (l : ℤ) (hl : 0+j=l) :
      T.tmul (g ≫ h : ι P ⟶ ι D) (N := regular (ι D)) i l n (by omega) x
          (D.mul 0 j l hl (h.chainMap.f 0 Q.one) z) =
        T.tmul (g ≫ h : ι P ⟶ ι D) (N := regular (ι D)) i j n hn x z := by
    rw [multiply_unit]
    obtain rfl : j = l := by omega
    rfl
  exact eq (0+j) rfl

end StrictModules

section SymbolMaps

open private symbolMaps from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentBaseChange

variable {U V P Q D U' P' Q' : NonpositiveCDGA.{u,w} k}
local notation "ι" => NonpositiveCDGA.toCommDGAlgebra
local notation "Ω" => (fun {_ _} f => Kahler.model f)

variable (T : ModuleTensor.{u,w} k)
variable (F : ∀ {X Y : CommDGAlgebra.{u,w} k} (f : X ⟶ Y) (N : Y.Module), T.Formulas f N)

include F in
private theorem localSymbolMap {f : U ⟶ P} {f' : U' ⟶ P'}
    (O : Differential f) (O' : Differential f')
    (a : U ⟶ U') (p : P ⟶ P') (g : P ⟶ Q) (g' : P' ⟶ Q') (d : Q ⟶ Q')
    (hf : f ≫ p = a ≫ f') (hg : g ≫ d = p ≫ g') :
    ∃ m, IsSymbolMap T O O' g g' p d m := by
  obtain ⟨s, hs⟩ := differentialIsoExists O (Ω f)
  obtain ⟨s', hs'⟩ := differentialIsoExists (Ω f') O'
  obtain ⟨m₀, hm₀, _⟩ := symbolMaps a p g g' d hf hg
  let e := extendIso T F g s.symm
  let e' := extendIso T F g' s'
  refine ⟨e.inv ≫ m₀ ≫ (restrictFunctor (d : ι Q ⟶ ι Q')).map e'.hom, ?_⟩
  intro i j n h x z
  change (e'.hom.app ()).f n ((m₀.app ()).f n ((e.inv.app ()).f n _)) = _
  dsimp only [e, e', symbolTensor]
  have h₁ := extendIso_inv_pure T F g s.symm i j n h (symbol O i x) z
  change _ = (canonicalTensor k).tmul (g : ι P ⟶ ι Q)
    (N := regular (ι Q)) i j n h ((s.hom.app ()).f i (symbol O i x)) z at h₁
  rw [hs] at h₁
  have h₂ := extendIso_hom_pure T F g' s' i j n h
    (symbol (Ω f') i (p.chainMap.f i x)) (d.chainMap.f j z)
  rw [hs'] at h₂
  exact (congrArg (fun y => ((extendIso T F g' s').hom.app ()).f n ((m₀.app ()).f n y)) h₁).trans
    ((congrArg (fun y => ((extendIso T F g' s').hom.app ()).f n y) (hm₀ i j n h x z)).trans h₂)

include F in
private theorem symbolMapId {f : U ⟶ P} (O : Differential f) (g : P ⟶ Q)
    (p : P ⟶ P) (d : Q ⟶ Q) (hp : p = 𝟙 P) (hd : d = 𝟙 Q)
    {L : (extend T g).obj O.module ⟶ restrict (d : ι Q ⟶ ι Q) ((extend T g).obj O.module)}
    (hL : IsSymbolMap T O O g g p d L) (n : ℤ) (x : term ((extend T g).obj O.module) n) :
    (L.app ()).f n x = x := by
  subst p d
  let N := (extend T g).obj O.module
  let I : N ⟶ restrict (𝟙 (ι Q)) N :=
    ⟨(𝟙 N : N ⟶ N).app, by intros; rfl⟩
  have e : L = I := by
    apply extendedSymbol_ext T F O g
    intro i j m h y z
    exact hL i j m h y z
  rw [e]
  rfl

include F in
private theorem symbolMapComposite
    {U₁ U₂ U₃ P₁ P₂ P₃ D₁ D₂ D₃ : NonpositiveCDGA.{u,w} k}
    {f₁ : U₁ ⟶ P₁} {f₂ : U₂ ⟶ P₂} {f₃ : U₃ ⟶ P₃}
    (O₁ : Differential f₁) (O₂ : Differential f₂) (O₃ : Differential f₃)
    (g₁ : P₁ ⟶ D₁) (g₂ : P₂ ⟶ D₂) (g₃ : P₃ ⟶ D₃)
    (p₁ : P₁ ⟶ P₂) (p₂ : P₂ ⟶ P₃) (p₃ : P₁ ⟶ P₃)
    (d₁ : D₁ ⟶ D₂) (d₂ : D₂ ⟶ D₃) (d₃ : D₁ ⟶ D₃)
    (hp : p₃ = p₁ ≫ p₂) (hd : d₃ = d₁ ≫ d₂)
    {L : (extend T g₁).obj O₁.module ⟶ restrict (d₁ : ι D₁ ⟶ ι D₂) ((extend T g₂).obj O₂.module)}
    {K : (extend T g₂).obj O₂.module ⟶ restrict (d₂ : ι D₂ ⟶ ι D₃) ((extend T g₃).obj O₃.module)}
    {H : (extend T g₁).obj O₁.module ⟶ restrict (d₃ : ι D₁ ⟶ ι D₃) ((extend T g₃).obj O₃.module)}
    (hL : IsSymbolMap T O₁ O₂ g₁ g₂ p₁ d₁ L)
    (hK : IsSymbolMap T O₂ O₃ g₂ g₃ p₂ d₂ K)
    (hH : IsSymbolMap T O₁ O₃ g₁ g₃ p₃ d₃ H)
    (n : ℤ) (x : term ((extend T g₁).obj O₁.module) n) :
    (H.app ()).f n x = (K.app ()).f n ((L.app ()).f n x) := by
  subst p₃ d₃
  let comp : (extend T g₁).obj O₁.module ⟶
      restrict (d₁ ≫ d₂ : ι D₁ ⟶ ι D₃) ((extend T g₃).obj O₃.module) :=
    ⟨(L ≫ (restrictFunctor (d₁ : ι D₁ ⟶ ι D₂)).map K).app,
      fun {a b} i j m h z y => by
        cases a; cases b
        change (K.app ()).f m ((L.app ()).f m (act _ i j m h z y)) =
          act ((extend T g₃).obj O₃.module) i j m h
            ((K.app ()).f i ((L.app ()).f i z)) (d₂.chainMap.f j (d₁.chainMap.f j y))
        rw [L.comm_act]
        exact K.comm_act (a := ()) (b := ()) i j m h ((L.app ()).f i z) (d₁.chainMap.f j y)⟩
  have e : H = comp := by
    apply extendedSymbol_ext T F O₁ g₁
    intro i j m h z y
    change (H.app ()).f m (symbolTensor T O₁ g₁ i j m h z y) =
      (K.app ()).f m ((L.app ()).f m (symbolTensor T O₁ g₁ i j m h z y))
    rw [hH, hL, hK]
    rfl
  rw [e]
  rfl

end SymbolMaps

section FlatComparisonTransport

variable {U P B C : NonpositiveCDGA.{u,w} k}
variable {f : U ⟶ P} {g : U ⟶ B} {a : U ⟶ C}
variable {X : PushoutCocone f a} {Y : PushoutCocone g a} {π : P ⟶ B}
local notation "ι" => NonpositiveCDGA.toCommDGAlgebra
local notation "Ω" => (fun {_ _} f => Kahler.model f)

variable (T : ModuleTensor.{u,w} k)
variable (F : ∀ {V W : CommDGAlgebra.{u,w} k} (f : V ⟶ W) (N : W.Module), T.Formulas f N)
variable (J : FlatComparison (canonicalTensor k) Ω π X Y)
variable {O : Differential f}
variable (e : (Ω f).module ≅ O.module)

include F in
private def transportFlatComparison :
    (extend T Y.inl).obj ((extend T π).obj O.module) ≅
      (extend T J.augmentation).obj (Ω X.inr).module :=
  (extendIso T F Y.inl (extendIso T F π e)).symm ≪≫ J.iso ≪≫
    tensorIso T F J.augmentation (Ω X.inr).module

include F in
private theorem transportFlatComparison_symbol
    (he : ∀ i x, (e.inv.app ()).f i (symbol O i x) = symbol (Ω f) i x)
    (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
    (x : P.complex.X i) (b : B.complex.X j) (z : Y.pt.complex.X l) :
    ((transportFlatComparison T F J e).hom.app ()).f n
      (T.tmul (Y.inl : ι B ⟶ ι Y.pt) (N := regular (ι Y.pt))
        m l n hn (symbolTensor T O π i j m hm x b) z) =
    symbolTensor T (Ω X.inr) J.augmentation i (j+l) n (by omega)
      (X.inl.chainMap.f i x) (Y.pt.mul j l (j+l) rfl (Y.inl.chainMap.f j b) z) := by
  let e₀ := extendIso T F π e
  let e₁ := extendIso T F Y.inl e₀
  let e₂ := tensorIso T F J.augmentation (Ω X.inr).module
  change (e₂.hom.app ()).f n ((J.iso.hom.app ()).f n ((e₁.inv.app ()).f n _)) = _
  dsimp only [e₁, e₀, symbolTensor]
  rw [extendIso_inv_pure, extendIso_inv_pure, he]
  exact (congrArg (fun y => (e₂.hom.app ()).f n y) (J.onSymbols i j l m n hm hn x b z)).trans
    (tensorIso_hom_pure T F J.augmentation (Ω X.inr).module _ _ _ _ _ _)

end FlatComparisonTransport

section Amitsur

open private flatComparisons symbolMaps from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentBaseChange
open private tensorIsPushout from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedAffineBaseChange
open private coproductModel from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.TensorResolutionComparison

variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra A B] [Algebra A C]
variable [IsScalarTower k A B]

set_option quotPrecheck false
set_option hygiene false in
local notation "globalLeg" => globalBase.{u,v,t} (k := k) (A := A) (B := B)
set_option hygiene false in
local notation "toPower" => powerLeg.{u,v,t} (k := k) (A := A) (C := C)
set_option hygiene false in
local notation "toTarget" => targetLeg.{u,v,t} (k := k) (A := A) (B := B) (C := C)
set_option hygiene false in
local notation "localLeg" => localBase.{u,v,t} (k := k) (A := A) (B := B) (C := C)
set_option hygiene false in
local notation "powerFactor" => powerMap.{u,v,t} (k := k) (A := A) (C := C)
set_option hygiene false in
local notation "targetFactor" => targetMap.{u,v,t} (k := k) (A := A) (B := B) (C := C)

local notation "ι" => NonpositiveCDGA.toCommDGAlgebra
local notation "Ω" => (fun {_ _} f => Kahler.model f)

private abbrev factorAlg {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    target A B C p →ₐ[B] target A B C q :=
  Algebra.TensorProduct.map (AlgHom.id B B) (AmitsurAlgebrasSpec.map f)

private theorem powerLeg_factor {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    toPower p ≫ powerFactor f = toPower q := by
  apply concentratedHom_ext (X := stalk.{u,v,t} k A) (stalkConcentrated A)
  intro x
  exact congrArg ULift.up
    ((AmitsurAlgebrasSpec.map f : power A C p →ₐ[A] power A C q).commutes (x.down : A))

private theorem targetLeg_factor {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    toTarget p ≫ targetFactor f = toTarget q := by
  apply concentratedHom_ext (X := stalk.{u,v,t} k B) (stalkConcentrated B)
  intro x
  let b : B := x.down
  let map : target A B C p →ₐ[B] target A B C q := factorAlg f
  change ULift.up (map (algebraMap B (target A B C p) b)) =
    ULift.up (algebraMap B (target A B C q) b)
  exact congrArg ULift.up (map.commutes b)

private theorem localLeg_factor {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    localLeg p ≫ targetFactor f = powerFactor f ≫ localLeg q := by
  apply concentratedHom_ext (X := stalk.{u,v,t} k (power A C p)) (stalkConcentrated _)
  intro x
  exact congrArg ULift.up (Algebra.TensorProduct.map_tmul (AlgHom.id B B)
    (AmitsurAlgebrasSpec.map f) (1 : B) (x.down : power A C p))

private theorem powerFactor_id (p : ℕ) : powerFactor (id : Fin (p + 1) → Fin (p + 1)) = 𝟙 _ := by
  apply concentratedHom_ext (X := stalk.{u,v,t} k (power A C p)) (stalkConcentrated _)
  intro x
  exact congrArg ULift.up (DFunLike.congr_fun (Descent.AmitsurAlgebras.map_id (A := A) (B := C)
    (p + 1)) (x.down : power A C p))

private theorem powerFactor_comp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (g : Fin (q + 1) → Fin (r + 1)) :
    powerFactor (g ∘ f) = powerFactor f ≫ powerFactor g := by
  apply concentratedHom_ext (X := stalk.{u,v,t} k (power A C p)) (stalkConcentrated _)
  intro x
  exact congrArg ULift.up (DFunLike.congr_fun (Descent.AmitsurAlgebras.map_comp (A := A) (B := C)
    f g) (x.down : power A C p))

private theorem targetFactor_id (p : ℕ) : targetFactor (id : Fin (p + 1) → Fin (p + 1)) = 𝟙 _ := by
  have e : (factorAlg (A := A) (B := B) (C := C) (id : Fin (p + 1) → Fin (p + 1))) = AlgHom.id B _ := by
    apply Algebra.TensorProduct.ext'
    intro b c
    change (AlgHom.id B B) b ⊗ₜ[A] AmitsurAlgebrasSpec.map id c = b ⊗ₜ[A] c
    have h := DFunLike.congr_fun (Descent.AmitsurAlgebras.map_id (A := A) (B := C) (p + 1)) c
    exact congrArg (fun y => b ⊗ₜ[A] y) h
  apply concentratedHom_ext (X := stalk.{u,v,t} k (target A B C p)) (stalkConcentrated _)
  intro x
  exact congrArg ULift.up (DFunLike.congr_fun e (x.down : target A B C p))

private theorem targetFactor_comp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (g : Fin (q + 1) → Fin (r + 1)) :
    targetFactor (g ∘ f) = targetFactor f ≫ targetFactor g := by
  have e : factorAlg (A := A) (B := B) (C := C) (g ∘ f) =
      (factorAlg g).comp (factorAlg f) := by
    apply Algebra.TensorProduct.ext'
    intro b c
    change b ⊗ₜ[A] AmitsurAlgebrasSpec.map (g ∘ f) c =
      b ⊗ₜ[A] AmitsurAlgebrasSpec.map g (AmitsurAlgebrasSpec.map f c)
    exact congrArg (fun y => b ⊗ₜ[A] y)
      (DFunLike.congr_fun (Descent.AmitsurAlgebras.map_comp (A := A) (B := C) f g) c)
  apply concentratedHom_ext (X := stalk.{u,v,t} k (target A B C p)) (stalkConcentrated _)
  intro x
  exact congrArg ULift.up (DFunLike.congr_fun e (x.down : target A B C p))

variable (T : ModuleTensor.{u,max v t} k)
variable (F : ∀ {U V : CommDGAlgebra.{u,max v t} k} (f : U ⟶ V) (N : V.Module), T.Formulas f N)
variable (M : Model globalLeg)

private abbrev resolvedCocone (p : ℕ) : PushoutCocone M.base (toPower p) :=
  (tensorIsPushout coproductModel M.base (toPower p)).cocone

private abbrev ordinaryCocone (p : ℕ) : PushoutCocone globalLeg (toPower p) :=
  (ordinaryTensorPushout.{u,v,t} (k := k) (A := A) (B := B) (C := power A C p)).cocone

private def flatColumnData [Module.Flat A C] (p : ℕ) :
    FlatComparison (canonicalTensor k) Ω M.augmentation (resolvedCocone (C := C) M p)
      (ordinaryCocone (k := k) (A := A) (B := B) (C := C) p) := by
  let X := tensorIsPushout coproductModel M.base (toPower p)
  let Y := ordinaryTensorPushout.{u,v,t} (k := k) (A := A) (B := B) (C := power A C p)
  letI : Module.Flat A (power A C p) := powerFlat p
  have ha : OrdinaryFlat (toPower p) := ordinaryFlat_of_flat (R := A) (S := power A C p)
  exact (flatComparisons M.augmentation M.triangle M.semifree M.surjective M.quasiIso ha
    X.cocone Y.cocone ⟨X.isColimit⟩ ⟨Y.isColimit⟩).some

include F in
private def makeColumn [Module.Flat A C]
    (e : (Ω M.base).module ≅ M.differentials.module)
    (he : ∀ i x, (e.inv.app ()).f i (symbol M.differentials i x) = symbol (Ω M.base) i x)
    (p : ℕ) : Column (C := C) T M p := by
  let X := resolvedCocone (C := C) M p
  let Y := ordinaryCocone (k := k) (A := A) (B := B) (C := C) p
  let J : FlatComparison (canonicalTensor k) Ω M.augmentation X Y :=
    flatColumnData (C := C) M p
  exact
    { model := J.model
      resolutionMap := X.inl
      resolutionPushout := tensorIsPushout coproductModel M.base (toPower p)
      ordinaryPushout := ordinaryTensorPushout.{u,v,t} (k := k) (A := A) (B := B) (C := power A C p)
      augmentation_comm := J.left
      comparison := transportFlatComparison T F J e
      symbols := transportFlatComparison_symbol T F J e he
      associator := extensionAssociator T F M.augmentation (toTarget p) M.differentials.module
      onAssociator := extensionAssociator_pure T F M.augmentation (toTarget p) M.differentials.module }

variable {T M} {p q : ℕ}

private def resolutionFactor (X : Column (C := C) T M p) (Y : Column (C := C) T M q)
    (f : Fin (p + 1) → Fin (q + 1)) : X.model.algebra ⟶ Y.model.algebra :=
  X.resolutionPushout.desc Y.resolutionMap (powerFactor f ≫ Y.model.base) (by
    rw [Y.resolutionPushout.w, ← Category.assoc, powerLeg_factor])

@[reassoc] private theorem resolutionFactor_left (X : Column (C := C) T M p)
    (Y : Column (C := C) T M q) (f : Fin (p + 1) → Fin (q + 1)) :
    X.resolutionMap ≫ resolutionFactor X Y f = Y.resolutionMap :=
  X.resolutionPushout.inl_desc _ _ _

@[reassoc] private theorem resolutionFactor_right (X : Column (C := C) T M p)
    (Y : Column (C := C) T M q) (f : Fin (p + 1) → Fin (q + 1)) :
    X.model.base ≫ resolutionFactor X Y f = powerFactor f ≫ Y.model.base :=
  X.resolutionPushout.inr_desc _ _ _

private theorem resolutionFactor_augmentation (X : Column (C := C) T M p)
    (Y : Column (C := C) T M q) (f : Fin (p + 1) → Fin (q + 1)) :
    X.model.augmentation ≫ targetFactor f = resolutionFactor X Y f ≫ Y.model.augmentation := by
  apply X.resolutionPushout.hom_ext
  · rw [← Category.assoc, X.augmentation_comm, Category.assoc, targetLeg_factor,
      resolutionFactor_left_assoc, Y.augmentation_comm]
  · rw [← Category.assoc, X.model.triangle, localLeg_factor,
      resolutionFactor_right_assoc, Y.model.triangle]

private theorem normalizedComparisonSymbol (X : Column (C := C) T M p)
    (i j n : ℤ) (h : i+j=n) (x : M.algebra.complex.X i)
    (z : (transported.{u,v,t} k (target A B C p)).complex.X j) :
    ((X.associator.inv ≫ X.comparison.hom).app ()).f n
      (symbolTensor T M.differentials (M.augmentation ≫ toTarget p) i j n h x z) =
    symbolTensor T X.model.differentials X.model.augmentation i j n h (X.resolutionMap.chainMap.f i x) z := by
  let y := (transported.{u,v,t} k B).one
  let u := symbolTensor T M.differentials M.augmentation i 0 i (add_zero i) x y
  let w := T.tmul (toTarget p : ι (transported.{u,v,t} k B) ⟶
      ι (transported.{u,v,t} k (target A B C p)))
    (N := regular (ι (transported.{u,v,t} k (target A B C p)))) i j n h u z
  have e := associator_unit T M.augmentation (toTarget p) M.differentials.module
    X.associator X.onAssociator i j n h (symbol M.differentials i x) z
  change (X.associator.hom.app ()).f n w =
    symbolTensor T M.differentials (M.augmentation ≫ toTarget p) i j n h x z at e
  change (X.comparison.hom.app ()).f n ((X.associator.inv.app ()).f n _) = _
  rw [← e, isoInv_apply]
  have ew := X.symbols i 0 j i n (add_zero i) h x y z
  change (X.comparison.hom.app ()).f n w = _ at ew
  refine ew.trans ?_
  have eq (l : ℤ) (hl : 0+j=l) :
      symbolTensor T X.model.differentials X.model.augmentation i l n (by omega)
        (X.resolutionMap.chainMap.f i x)
        ((transported.{u,v,t} k (target A B C p)).mul 0 j l hl ((toTarget p).chainMap.f 0 y) z) =
      symbolTensor T X.model.differentials X.model.augmentation i j n h
        (X.resolutionMap.chainMap.f i x) z := by
    obtain rfl : j = l := by omega
    exact congrArg (fun z' => symbolTensor T X.model.differentials X.model.augmentation i j n h
      (X.resolutionMap.chainMap.f i x) z') (multiply_unit (toTarget p) j j hl z)
  exact eq (0+j) rfl

include F in
private def makeMap (X : Column (C := C) T M p) (Y : Column (C := C) T M q)
    (f : Fin (p + 1) → Fin (q + 1)) : ColumnMap X Y f := by
  let m := resolutionFactor X Y f
  let h₁ := resolutionFactor_right X Y f
  let h₂ := resolutionFactor_augmentation X Y f
  let cot := localSymbolMap T F X.model.differentials Y.model.differentials
    (powerFactor f) m X.model.augmentation Y.model.augmentation (targetFactor f) h₁ h₂
  let Z := transported.{u,v,t} k (target A B C q)
  let R := restrictFunctor (targetFactor f : _ ⟶ ι Z)
  let L := scalarMap T F (toTarget p) (targetFactor f) (toTarget q) (targetLeg_factor f) (M.module T)
  let norm := X.associator.inv ≫ L ≫ R.map Y.associator.hom
  have hnorm : IsSymbolMap T M.differentials M.differentials
      (M.augmentation ≫ toTarget p) (M.augmentation ≫ toTarget q) (𝟙 M.algebra) (targetFactor f) norm := by
    intro i j n h x z
    let B₀ := transported.{u,v,t} k B
    let w := symbolTensor T M.differentials M.augmentation i 0 i (add_zero i) x B₀.one
    have ep := associator_unit T M.augmentation (toTarget p) M.differentials.module
      X.associator X.onAssociator i j n h (symbol M.differentials i x) z
    have eq := associator_unit T M.augmentation (toTarget q) M.differentials.module
      Y.associator Y.onAssociator i j n h (symbol M.differentials i x) ((targetFactor f).chainMap.f j z)
    change (Y.associator.hom.app ()).f n ((L.app ()).f n ((X.associator.inv.app ()).f n _)) = _
    change _ = symbolTensor T M.differentials (M.augmentation ≫ toTarget q)
      i j n h x ((targetFactor f).chainMap.f j z)
    change _ = symbolTensor T M.differentials (M.augmentation ≫ toTarget p) i j n h x z at ep
    rw [← ep, isoInv_apply]
    have eL := scalarMap_pure T F (toTarget p) (targetFactor f) (toTarget q)
      (targetLeg_factor f) (M.module T) i j n h w z
    change (L.app ()).f n _ = _ at eL
    exact (congrArg (fun y => (Y.associator.hom.app ()).f n y) eL).trans eq
  refine ⟨m, resolutionFactor_left X Y f, h₁, h₂, cot.choose, cot.choose_spec, norm, hnorm, ?_⟩
  have nat : norm ≫ R.map (Y.associator.inv ≫ Y.comparison.hom) =
      X.associator.inv ≫ X.comparison.hom ≫ cot.choose := by
    apply extendedSymbol_ext T F M.differentials (M.augmentation ≫ toTarget p)
    intro i j n h x z
    change ((Y.associator.inv ≫ Y.comparison.hom).app ()).f n
      ((norm.app ()).f n (symbolTensor T M.differentials _ i j n h x z)) =
      (cot.choose.app ()).f n (((X.associator.inv ≫ X.comparison.hom).app ()).f n
        (symbolTensor T M.differentials _ i j n h x z))
    rw [hnorm, normalizedComparisonSymbol Y, normalizedComparisonSymbol X, cot.choose_spec]
    have e := CategoryTheory.congr_fun
      (congrArg (fun a : M.algebra ⟶ Y.model.algebra => a.chainMap.f i)
        (resolutionFactor_left X Y f)) x
    exact congrArg (fun y => symbolTensor T Y.model.differentials Y.model.augmentation
      i j n h y ((targetFactor f).chainMap.f j z)) e.symm
  apply (cancel_epi X.associator.inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using nat

include F in
private theorem makeMap_extension (X : Column (C := C) T M p) (Y : Column (C := C) T M q)
    (f : Fin (p + 1) → Fin (q + 1)) :
    (makeMap (F := F) X Y f).extensionMap =
      scalarMap T F (toTarget p) (targetFactor f) (toTarget q) (targetLeg_factor f) (M.module T) := by
  let R := restrictFunctor (targetFactor f : _ ⟶ ι (transported.{u,v,t} k (target A B C q)))
  let L := scalarMap T F (toTarget p) (targetFactor f) (toTarget q) (targetLeg_factor f) (M.module T)
  change X.associator.hom ≫ (X.associator.inv ≫ L ≫ R.map Y.associator.hom) ≫
    R.map Y.associator.inv = L
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [R.map_id, Category.comp_id]

/-- A single transported semifree model gives the full strict diagram over the
ordered Amitsur tensor powers. -/
theorem flatCotangentDiagram : FlatCotangentDiagram.{u,v,t} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _ _ _ _ T F M
  obtain ⟨e, he⟩ := differentialIsoExists M.differentials (Ω M.base)
  let col : ∀ p : ℕ, Column (C := C) T M p := makeColumn (C := C) T F M e.symm he
  let maps {p q} (f : Fin (p + 1) → Fin (q + 1)) := makeMap (F := F) (col p) (col q) f
  have hid (p : ℕ) : (maps (id : Fin (p + 1) → Fin (p + 1))).algebraMap = 𝟙 _ := by
    apply (col p).resolutionPushout.hom_ext
    · rw [(maps _).fromResolution, Category.comp_id]
    · rw [(maps _).fromBase, powerFactor_id, Category.id_comp, Category.comp_id]
  have hcomp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (g : Fin (q + 1) → Fin (r + 1)) :
      (maps (g ∘ f)).algebraMap = (maps f).algebraMap ≫ (maps g).algebraMap := by
    apply (col p).resolutionPushout.hom_ext
    · rw [(maps _).fromResolution, ← Category.assoc, (maps f).fromResolution, (maps g).fromResolution]
    · rw [(maps _).fromBase, ← Category.assoc, (maps f).fromBase, Category.assoc,
        (maps g).fromBase, powerFactor_comp, Category.assoc]
  refine ⟨⟨powerFlat (A := A) (C := C), col, @maps, hid, @hcomp, ?_, ?_, ?_⟩⟩
  · intro p n x
    exact symbolMapId T F (col p).model.differentials (col p).model.augmentation
      _ _ (hid p) (targetFactor_id p) (maps _).symbols n x
  · intro p q r f g n x
    exact symbolMapComposite T F (col p).model.differentials (col q).model.differentials
      (col r).model.differentials (col p).model.augmentation (col q).model.augmentation
      (col r).model.augmentation _ _ _ _ _ _ (hcomp f g) (targetFactor_comp f g)
      (maps f).symbols (maps g).symbols (maps (g ∘ f)).symbols n x
  · intro p q f i j n h x z
    change ((makeMap (F := F) (col p) (col q) f).extensionMap.app ()).f n _ = _
    rw [makeMap_extension]
    exact scalarMap_pure T F _ _ _ (targetLeg_factor f) (M.module T) i j n h x z

end Amitsur

end

end DerivedFormalization.Affine.FlatCotangentAmitsurDiagram
