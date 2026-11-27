import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.OrdinaryDGTensorComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.Tensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensor
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

open CategoryTheory CategoryTheory.Limits
open scoped Classical TensorProduct DirectSum

namespace DerivedFormalization.Affine.OrdinaryDGTensorComparison

open Specs.DerivedFormalization.Affine.OrdinaryDGTensorComparison
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor dgCat term act regular signedLeft signedBimodule)
open Specs.DerivedFormalization.Affine.CotangentComplex (cdgaLift)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws quotient)
open Specs.DerivedFormalization.DG.DerivedKProjective
  (derivedCategoryInstance kProjectiveObjects restrictedLocalization)
open Specs.DerivedFormalization.DG.HomComplex (homotopyClass)
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange
  (extend extendId extendComp extendId_hom_tmul extendComp_hom_tmul extend_map_tmul)

noncomputable section

universe u v t

variable {k : Type u} [Field k] [CharZero k]
variable {R S V : Type v} [CommRing R] [CommRing S] [CommRing V]
variable [Algebra k R] [Algebra k S] [Algebra k V]

set_option allowUnsafeReducibility true in
attribute [local reducible] ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  Specs.DerivedFormalization.Descent.PerfectHomBaseChange.scalarExtension

local instance transportedRing : CommRing (transported.{u,v,t} k R).DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero (transported.{u,v,t} k R)

local instance transportedAlgebra : Algebra k (transported.{u,v,t} k R).DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero (transported.{u,v,t} k R)

private abbrev termEquiv (E : StrictComparison.{u,v,t} k R) (X : compValue.{max v t} R) (n : ℤ) :
    ((restriction.{u,v,t} k R).obj X).X n ≃ₗ[k] term (E.strict.obj X) n :=
  (HomologicalComplex.Hom.isoApp (E.terms X) n).toLinearEquiv

private theorem termEquiv_map (E : StrictComparison.{u,v,t} k R)
    {X Y : compValue.{max v t} R} (f : X ⟶ Y) (n : ℤ) (x : X.X n) :
    (E.strict.map f |>.app () |>.f n) (termEquiv E X n x) =
      termEquiv E Y n (f.f n x) := by
  let x₀ : ((restriction.{u,v,t} k R).obj X).X n := x
  exact (congrArg (fun g => g.f n x₀) (E.terms_natural f)).symm

private theorem termEquiv_d (E : StrictComparison.{u,v,t} k R)
    (X : compValue.{max v t} R) (n : ℤ) (x : X.X n) :
    ((E.strict.obj X).complex ()).d n (n+1) (termEquiv E X n x) =
      termEquiv E X (n+1) (X.d n (n+1) x) :=
  ConcreteCategory.congr_hom ((E.terms X).hom.comm n (n+1))
    (show ((restriction.{u,v,t} k R).obj X).X n from x)

private theorem termEquiv_action (E : StrictComparison.{u,v,t} k R)
    (X : compValue.{max v t} R) (n : ℤ) (a : R) (x : X.X n) :
    act (E.strict.obj X) n 0 n (add_zero n) (termEquiv E X n x) (E.scalar a) =
      termEquiv E X n (a • x) := E.action X n a x

private theorem transported_eq_zero (j : ℤ) (hj : j ≠ 0)
    (x : (transported.{u,v,t} k R).complex.X j) : x = 0 := by
  apply ULift.ext
  exact (ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of k R) j hj)).elim x.down 0

private theorem transportedMap_scalar (E : StrictComparison.{u,v,t} k R)
    (F : StrictComparison.{u,v,t} k S) (f : R →ₐ[k] S) (x : R) :
    (transportedMap.{u,v,t} f).chainMap.f 0 (E.scalar x) = F.scalar (f x) := by
  rw [E.scalar_apply, F.scalar_apply]
  rfl

private theorem transported_mul_scalar (E : StrictComparison.{u,v,t} k R) (a b : R) :
    (transported.{u,v,t} k R).mul 0 0 0 rfl (E.scalar a) (E.scalar b) = E.scalar (a * b) :=
  (E.scalar.map_mul a b).symm

private abbrev stalkFunctor (k : Type u) [Field k] [CharZero k] :=
  NonpositiveCDGA.ordinaryFunctor.{u,v} k ⋙ cdgaLift.{u,v,t} k

private theorem scalarMap_id :
    scalarMap.{u,v,t} k R R = 𝟙 (transported.{u,v,t} k R) := by
  have h : CommAlgCat.ofHom (IsScalarTower.toAlgHom k R R) = 𝟙 (CommAlgCat.of k R) :=
    CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
  exact (congrArg (stalkFunctor.{u,v,t} k).map h).trans
    ((stalkFunctor.{u,v,t} k).map_id _)

private theorem dgHom_ext_at {A : CommDGAlgebra.{u,v} k} {M N : A.Module} {a b : M ⟶ N}
    (h : ∀ n (x : term M n), (a.app ()).f n x = (b.app ()).f n x) : a = b := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  exact HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext (h n))

private theorem cast_tmul {A B : CommDGAlgebra.{u,v} k} (T : ModuleTensor.{u,v} k)
    {f g : A ⟶ B} (e : f = g) (M : A.Module) (N : B.Module)
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    ((eqToHom (congrArg (fun a => T.obj a M N) e)).app ()).f n (T.tmul f i j n h x y) =
      T.tmul g i j n h x y := by
  subst g
  rfl

private theorem tensor_add_ext {Q P Z : Type*} [AddCommGroup Q] [AddCommGroup P]
    [AddCommGroup Z] [Module R Q] [Module R P]
    {f g : Q ⊗[R] P →+ Z} (h : ∀ (q : Q) (p : P), f (q ⊗ₜ[R] p) = g (q ⊗ₜ[R] p)) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  exact TensorProduct.inductionOn x h
    (fun x y hx hy => by simp only [map_add, hx, hy])

private theorem extendHom_ext (E : StrictComparison.{u,v,t} k R)
    (X : compValue.{max v t} R) {M : (transported.{u,v,t} k R).Module}
    {a b : E.strict.obj X ⟶ M} (h : ∀ n (x : X.X n),
      (a.app ()).f n (termEquiv E X n x) = (b.app ()).f n (termEquiv E X n x)) :
    a = b :=
  dgHom_ext_at fun n y => by
    obtain ⟨x, rfl⟩ := (termEquiv E X n).surjective y
    exact h n x

private abbrev onOrdinaryTerms {M : (transported.{u,v,t} k R).Module}
    (E : StrictComparison.{u,v,t} k R) (X : compValue.{max v t} R)
    (a : E.strict.obj X ⟶ M) (n : ℤ) : X.X n →+ term M n :=
  ((a.app ()).f n).hom.toAddMonoidHom.comp (termEquiv E X n).toLinearMap.toAddMonoidHom

section Balanced

variable {A B : CommDGAlgebra.{u,v} k}
variable (T : ModuleTensor.{u,v} k) (f : A ⟶ B) (M : A.Module) (N : B.Module)

/-- The universal balanced pairing transported to the terms of the chosen tensor model. -/
private abbrev dgPair (i j n : ℤ) (h : i+j=n) :
    term M i →ₗ[k] term N j →ₗ[k] term (T.obj f M N) n :=
  (DGBimodule.tensorPair (signedBimodule f N) M () () i j n h).compr₂ (T.degree f M N n).toLinearMap

private theorem balance (i l j il lj n : ℤ) (hi : i+l=il) (hj : l+j=lj) (h : il+j=n)
    (x : term M i) (a : A.complex.X l) (y : term N j) :
    T.tmul f il j n h (act M i l il hi x a) y =
      T.tmul f i lj n (by omega) x (signedLeft N l j lj hj (f.chainMap.f l a) y) :=
  congrArg (T.degree f M N n) (Affine.Tensor.pure_balance f i l j il lj n hi hj h x a y)

private theorem tensor_action_at (hT : T.Formulas f N)
    (i j n l jl q : ℤ) (h : i+j=n) (hj : j+l=jl) (hq : n+l=q)
    (x : term M i) (y : term N j) (a : B.complex.X l) :
    act (T.obj f M N) n l q hq (T.tmul f i j n h x y) a =
      T.tmul f i jl q (by omega) x (act N j l jl hj y a) := by
  subst jl
  exact hT.action M i j n l q h hq x y a

private theorem dgTensor_ext {Q : Type*} [AddCommGroup Q] [Module k Q] (n : ℤ)
    {g h : term (T.obj f M N) n →ₗ[k] Q}
    (e : ∀ i j (eq : i+j=n) x y, g (T.tmul f i j n eq x y) = h (T.tmul f i j n eq x y)) : g = h := by
  let d := T.degree f M N n
  have hh : g.comp d.toLinearMap = h.comp d.toLinearMap :=
    DGBimodule.linearMap_ext (signedBimodule f N) M (b := ()) (n := n)
      (fun ⟨⟩ i j eq x y => e i j eq x y)
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := d.surjective x
  exact DFunLike.congr_fun hh z

/-- An additive map out of a tensor degree is determined by homogeneous pure tensors. -/
private theorem dgTensor_add_ext {Q : Type*} [AddCommGroup Q] (n : ℤ)
    {g h : term (T.obj f M N) n →+ Q}
    (e : ∀ i j (eq : i+j=n) x y, g (T.tmul f i j n eq x y) = h (T.tmul f i j n eq x y)) : g = h := by
  let Bim := signedBimodule f N
  let d := T.degree f M N n
  let K := Specs.DerivedFormalization.DG.BalancedTensor.Balance Bim M () n
  let q := d.toLinearMap.toAddMonoidHom.comp K.mkQ.toAddMonoidHom
  have eq : g.comp q = h.comp q := by
    apply DirectSum.addHom_ext
    rintro ⟨⟨⟩, ⟨⟨i,j⟩, eq⟩⟩ z
    let l := (DirectSum.lof k _ (Specs.DerivedFormalization.DG.BalancedTensor.Summand Bim M () n)
      ⟨(), ⟨(i,j), eq⟩⟩).toAddMonoidHom
    change (g.comp q).comp l z = (h.comp q).comp l z
    refine DFunLike.congr_fun (tensor_add_ext (f := (g.comp q).comp l) (g := (h.comp q).comp l) ?_) z
    intro x y
    -- The raw quotient uses a different decidable equality on the degree index.
    have hl : l (x ⊗ₜ[k] y) =
      Specs.DerivedFormalization.DG.BalancedTensor.rawTmul Bim M () () i j n eq x y := by
      dsimp only [l, LinearMap.toAddMonoidHom_coe,
        Specs.DerivedFormalization.DG.BalancedTensor.rawTmul]
      congr 2
      apply Subsingleton.elim
    change g (d (K.mkQ (l (x ⊗ₜ[k] y)))) = h (d (K.mkQ (l (x ⊗ₜ[k] y))))
    rw [hl]
    exact e i j eq x y
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := d.surjective z
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective K w
  exact DFunLike.congr_fun eq w

private def dgTensorLift {Q : Type*} [AddCommGroup Q] [Module k Q] (n : ℤ)
    (p : ∀ i j : ℤ, i+j=n → (term M i →ₗ[k] term N j →ₗ[k] Q))
    (hp : ∀ i l j il lj (hi : i+l=il) (hj : l+j=lj) (h : il+j=n)
      (x : term M i) (a : A.complex.X l) (y : term N j),
      p il j h (act M i l il hi x a) y =
      p i lj (by omega) x (signedLeft N l j lj hj (f.chainMap.f l a) y)) :
    term (T.obj f M N) n →ₗ[k] Q :=
  (DGBimodule.lift (signedBimodule f N) M (b := ()) (fun _ => p)
    (fun ⟨⟩ ⟨⟩ i l j h x a y => hp i l j (i+l) (l+j) rfl rfl h x a y)).comp (T.degree f M N n).symm.toLinearMap

private theorem dgTensorLift_tmul {Q : Type*} [AddCommGroup Q] [Module k Q] (n : ℤ)
    (p : ∀ i j : ℤ, i+j=n → (term M i →ₗ[k] term N j →ₗ[k] Q)) (hp)
    (i j : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    dgTensorLift T f M N n p hp (T.tmul f i j n h x y) = p i j h x y := by
  simp only [dgTensorLift, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Specs.DerivedFormalization.Affine.Tensor.pure, DGBimodule.lift_tmul]

end Balanced

section Iso

variable {A : CommDGAlgebra.{u,v} k} {M N : A.Module}

/-- A degreewise linear isomorphism commuting with the differential and action
has a dg-module inverse. -/
private def dgIsoOfTerms (e : ∀ n, term M n ≃ₗ[k] term N n)
    (hd : ∀ n x, (N.complex ()).d n (n+1) (e n x) = e (n+1) ((M.complex ()).d n (n+1) x))
    (ha : ∀ i j n (h : i+j=n) (x : term M i) (a : A.complex.X j),
      e n (act M i j n h x a) = act N i j n h (e i x) a) : M ≅ N := by
  let c : M.complex () ≅ N.complex () :=
    HomologicalComplex.Hom.isoOfComponents (fun n => (e n).toModuleIso) (by
      intro n m h
      obtain rfl : n+1=m := h
      exact ModuleCat.hom_ext (LinearMap.ext (hd n)))
  refine ⟨⟨fun _ => c.hom, ?_⟩, ⟨fun _ => c.inv, ?_⟩, ?_, ?_⟩
  · rintro ⟨⟩ ⟨⟩ i j n h x a
    exact ha i j n h x a
  · rintro ⟨⟩ ⟨⟩ i j n h y a
    obtain ⟨x, rfl⟩ := (e i).surjective y
    change (e n).symm (act N i j n h (e i x) a) = act M i j n h ((e i).symm (e i x)) a
    rw [← ha, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  · exact RightDGModuleModel.hom_ext (fun ⟨⟩ => c.hom_inv_id)
  · exact RightDGModuleModel.hom_ext (fun ⟨⟩ => c.inv_hom_id)

private def dgTensorIsoOfTerms {B : CommDGAlgebra.{u,v} k} (T : ModuleTensor.{u,v} k)
    (f : A ⟶ B) (X : A.Module) (Y P : B.Module)
    (e : ∀ n, term (T.obj f X Y) n ≃ₗ[k] term P n)
    (hd : ∀ i j n (h : i+j=n) x y,
      (P.complex ()).d n (n+1) (e n (T.tmul f i j n h x y)) =
        e (n+1) (((T.obj f X Y).complex ()).d n (n+1) (T.tmul f i j n h x y)))
    (ha : ∀ i j n l q (h : i+j=n) (hq : n+l=q) x y a,
      e q (act (T.obj f X Y) n l q hq (T.tmul f i j n h x y) a) =
        act P n l q hq (e n (T.tmul f i j n h x y)) a) : T.obj f X Y ≅ P :=
  dgIsoOfTerms e
    (fun n x => DFunLike.congr_fun
      (dgTensor_ext T f X Y n
        (g := ((P.complex ()).d n (n+1)).hom.comp (e n).toLinearMap)
        (h := (e (n+1)).toLinearMap.comp (((T.obj f X Y).complex ()).d n (n+1)).hom)
        (fun i j h => hd i j n h)) x)
    (fun n l q h x a => DFunLike.congr_fun
      (dgTensor_ext T f X Y n
        (g := (e q).toLinearMap.comp ((act (T.obj f X Y) n l q h).flip a))
        (h := ((act P n l q h).flip a).comp (e n).toLinearMap)
        (fun i j hh y z => ha i j n l q hh h y z a)) x)

end Iso

section InternalTensor

variable (E : StrictComparison.{u,v,t} k R) (X Y : compValue.{max v t} R)

private abbrev ordinaryTensorCofan (n : ℤ) :=
  isColimitCofanMkObjOfIsColimit (forget₂ (ModuleCat.{max v t} R) AddCommGrpCat)
    (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ModuleCat.of R (X.X p.1.1 ⊗[R] Y.X p.1.2))
    (fun p => CochainTensor.ι X Y p.1.1 p.1.2 n p.2)
    (CochainTensor.tensorCofanIsColimit X Y n)

private theorem ordinaryTensor_add_ext {Q : Type (max v t)} [AddCommGroup Q] {n : ℤ}
    {g h : (CochainTensor.tensor X Y).X n →+ Q}
    (hh : ∀ i j (e : i+j=n) (x : X.X i) (y : Y.X j),
      g (CochainTensor.pure X Y e x y) = h (CochainTensor.pure X Y e x y)) : g = h := by
  have e : AddCommGrpCat.ofHom g = AddCommGrpCat.ofHom h :=
    Cofan.IsColimit.hom_ext (ordinaryTensorCofan X Y n) _ _ (fun ⟨⟨i,j⟩, e⟩ => by
      apply AddCommGrpCat.hom_ext
      exact tensor_add_ext (hh i j e))
  exact congrArg AddCommGrpCat.Hom.hom e

private def ordinaryPair (i j n : ℤ) (h : i+j=n) :
    ((restriction.{u,v,t} k R).obj X).X i →ₗ[k] ((restriction.{u,v,t} k R).obj Y).X j →ₗ[k]
      ((restriction.{u,v,t} k R).obj (CochainTensor.tensor X Y)).X n := by
  let Z := (CochainTensor.tensor X Y).X n
  letI := Module.restrictScalars k R (X.X i)
  letI := Module.restrictScalars k R (Y.X j)
  letI := Module.restrictScalars k R Z
  letI := IsScalarTower.restrictScalars k R (X.X i)
  letI := IsScalarTower.restrictScalars k R (Y.X j)
  letI := IsScalarTower.restrictScalars k R Z
  let p := (TensorProduct.mk R (X.X i) (Y.X j)).compr₂ (CochainTensor.ι X Y i j n h).hom
  exact (LinearMap.restrictScalarsₗ k R (Y.X j) Z k).comp (p.restrictScalars k)

private abbrev ordinaryPairFromDG (i j n : ℤ) (h : i+j=n) :
    term (E.strict.obj X) i →ₗ[k] term (E.strict.obj Y) j →ₗ[k]
      ((restriction.{u,v,t} k R).obj (CochainTensor.tensor X Y)).X n := by
  letI := Module.restrictScalars k R (X.X i)
  letI := Module.restrictScalars k R (Y.X j)
  exact ((ordinaryPair (k := k) X Y i j n h).compl₂ (termEquiv E Y j).symm.toLinearMap).comp
    (termEquiv E X i).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryPair_balanced (i l j il lj n : ℤ) (hi : i+l=il) (hj : l+j=lj) (h : il+j=n)
    (x : term (E.strict.obj X) i) (a : (transported.{u,v,t} k R).complex.X l)
    (y : term (E.strict.obj Y) j) :
    ordinaryPairFromDG E X Y il j n h (act (E.strict.obj X) i l il hi x a) y =
      ordinaryPairFromDG E X Y i lj n (by omega) x
        (signedLeft (E.strict.obj Y) l j lj hj ((CommDGAlgebra.Hom.id (transported.{u,v,t} k R)).chainMap.f l a) y) := by
  by_cases hl : l = 0
  · subst l
    obtain ⟨r, rfl⟩ := E.scalar.surjective a
    obtain ⟨(x : X.X i), rfl⟩ := (termEquiv E X i).surjective x
    obtain ⟨(y : Y.X j), rfl⟩ := (termEquiv E Y j).surjective y
    have ei : i = il := by omega
    have ej : j = lj := by omega
    cases ei
    cases ej
    change ordinaryPairFromDG E X Y i j n h
        (act (E.strict.obj X) i 0 i (add_zero i) (termEquiv E X i x) (E.scalar r)) (termEquiv E Y j y) =
      ordinaryPairFromDG E X Y i j n h (termEquiv E X i x)
        (signedLeft (E.strict.obj Y) 0 j j (zero_add j) (E.scalar r) (termEquiv E Y j y))
    rw [Specs.DerivedFormalization.Affine.Tensor.signedLeft_apply, zero_mul, Int.negOnePow_zero, one_smul]
    rw [termEquiv_action E X, termEquiv_action E Y]
    simp only [ordinaryPairFromDG, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    change (CochainTensor.ι X Y i j n h) ((r • x) ⊗ₜ[R] y) =
      (CochainTensor.ι X Y i j n h) (x ⊗ₜ[R] (r • y))
    rw [TensorProduct.smul_tmul]
  · rw [transported_eq_zero l hl a]
    simp only [map_zero, LinearMap.zero_apply]

variable (T : ModuleTensor.{u,max v t} k)

/-- Descend the ordinary homogeneous pairing through the dg balancing relations. -/
private def internalToOrdinary (n : ℤ) :
    term (T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y)) n →ₗ[k]
      ((restriction.{u,v,t} k R).obj (CochainTensor.tensor X Y)).X n :=
  dgTensorLift T (𝟙 _) (E.strict.obj X) (E.strict.obj Y) n
    (fun i j h => ordinaryPairFromDG E X Y i j n h) (fun i l j il lj hi hj h => ordinaryPair_balanced E X Y i l j il lj n hi hj h)

private theorem internalToOrdinary_pure (i j n : ℤ) (h : i+j=n)
    (x : term (E.strict.obj X) i) (y : term (E.strict.obj Y) j) :
    internalToOrdinary E X Y T n (T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h x y) =
      CochainTensor.pure X Y h ((termEquiv E X i).symm x) ((termEquiv E Y j).symm y) := by
  rw [internalToOrdinary, dgTensorLift_tmul]
  rfl

private abbrev internalPairToDG (i j n : ℤ) (h : i+j=n) :
    X.X i →+ Y.X j →+ term (T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y)) n := by
  letI := Module.restrictScalars k R (X.X i)
  letI := Module.restrictScalars k R (Y.X j)
  exact (LinearMap.toAddMonoidHom'.comp
    (((dgPair T (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y) i j n h).compl₂
      (termEquiv E Y j).toLinearMap).comp (termEquiv E X i).toLinearMap).toAddMonoidHom)

set_option backward.isDefEq.respectTransparency false in
private theorem internalPairToDG_balanced (i j n : ℤ) (h : i+j=n)
    (r : R) (x : X.X i) (y : Y.X j) :
    internalPairToDG E X Y T i j n h (r • x) y = internalPairToDG E X Y T i j n h x (r • y) := by
  let A := transported.{u,v,t} k R
  change T.tmul (𝟙 A) i j n h (termEquiv E X i (r • x)) (termEquiv E Y j y) =
    T.tmul (𝟙 A) i j n h (termEquiv E X i x) (termEquiv E Y j (r • y))
  have hx : act (E.strict.obj X) i 0 i (add_zero i) (termEquiv E X i x) (E.scalar r) =
      termEquiv E X i (r • x) := E.action X i r x
  have hy : act (E.strict.obj Y) j 0 j (add_zero j) (termEquiv E Y j y) (E.scalar r) =
      termEquiv E Y j (r • y) := E.action Y j r y
  rw [← hx, ← hy]
  have hh := balance T (𝟙 A) (E.strict.obj X) (E.strict.obj Y) i 0 j i j n
    (add_zero i) (zero_add j) h (termEquiv E X i x) (E.scalar r) (termEquiv E Y j y)
  rw [Specs.DerivedFormalization.Affine.Tensor.signedLeft_apply, zero_mul, Int.negOnePow_zero, one_smul] at hh
  exact hh

/-- Construct the inverse additively using the ordinary coproduct and tensor relations. -/
private def internalFromOrdinary (n : ℤ) :
    (CochainTensor.tensor X Y).X n →+
      term (T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y)) n :=
  (Cofan.IsColimit.desc (ordinaryTensorCofan X Y n) fun ⟨⟨i,j⟩, h⟩ =>
    AddCommGrpCat.ofHom (TensorProduct.liftAddHom (internalPairToDG E X Y T i j n h)
      (internalPairToDG_balanced E X Y T i j n h))).hom

set_option maxHeartbeats 800000 in
private theorem internalFromOrdinary_pure (i j n : ℤ) (h : i+j=n) (x : X.X i) (y : Y.X j) :
    internalFromOrdinary E X Y T n (CochainTensor.pure X Y h x y) =
      T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h (termEquiv E X i x) (termEquiv E Y j y) := by
  let p : {p : ℤ × ℤ // p.1 + p.2 = n} := ⟨(i,j), h⟩
  exact ConcreteCategory.congr_hom (Cofan.IsColimit.inj_desc _
    (ordinaryTensorCofan X Y n) p) (x ⊗ₜ[R] y)

private def internalDegreeEquiv (n : ℤ) :
    term (T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y)) n ≃ₗ[k]
      term (E.strict.obj (CochainTensor.tensor X Y)) n := by
  let f := 𝟙 (transported.{u,v,t} k R)
  let M := E.strict.obj X
  let N := E.strict.obj Y
  let p := internalToOrdinary E X Y T n
  let q := internalFromOrdinary E X Y T n
  have hp : q.comp p.toAddMonoidHom = AddMonoidHom.id _ := by
    apply dgTensor_add_ext T f M N n
    intro i j h x y
    change q (p (T.tmul f i j n h x y)) = T.tmul f i j n h x y
    rw [internalToOrdinary_pure, internalFromOrdinary_pure]
    simp only [LinearEquiv.apply_symm_apply, f]
    rfl
  have hq : p.toAddMonoidHom.comp q = AddMonoidHom.id _ := by
    apply ordinaryTensor_add_ext X Y
    intro i j h x y
    change p (q (CochainTensor.pure X Y h x y)) = CochainTensor.pure X Y h x y
    rw [internalFromOrdinary_pure, internalToOrdinary_pure]
    simp only [LinearEquiv.symm_apply_apply]
  exact (LinearEquiv.ofBijective p ⟨
    (show Function.LeftInverse q p from fun x => DFunLike.congr_fun hp x).injective,
    (show Function.RightInverse q p from fun x => DFunLike.congr_fun hq x).surjective⟩).trans
    (termEquiv E (CochainTensor.tensor X Y) n)

private theorem internalDegreeEquiv_pure (i j n : ℤ) (h : i+j=n) (x : X.X i) (y : Y.X j) :
    internalDegreeEquiv E X Y T n (T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h
      (termEquiv E X i x) (termEquiv E Y j y)) =
      termEquiv E (CochainTensor.tensor X Y) n (CochainTensor.pure X Y h x y) := by
  change termEquiv E (CochainTensor.tensor X Y) n (internalToOrdinary E X Y T n
    (T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h (termEquiv E X i x) (termEquiv E Y j y))) = _
  rw [internalToOrdinary_pure]
  simp only [LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
private def internalIso (hT : T.Formulas (𝟙 (transported.{u,v,t} k R)) (E.strict.obj Y)) :
    T.obj (𝟙 (transported.{u,v,t} k R)) (E.strict.obj X) (E.strict.obj Y) ≅
      E.strict.obj (CochainTensor.tensor X Y) := by
  let A := transported.{u,v,t} k R
  let f : A ⟶ A := 𝟙 A
  let M := E.strict.obj X
  let N := E.strict.obj Y
  let P := E.strict.obj (CochainTensor.tensor X Y)
  let L := T.obj f M N
  let eq := internalDegreeEquiv E X Y T
  apply dgTensorIsoOfTerms T f M N P eq
  · intro i j n h x y
    obtain ⟨(x : X.X i), rfl⟩ := (termEquiv E X i).surjective x
    obtain ⟨(y : Y.X j), rfl⟩ := (termEquiv E Y j).surjective y
    dsimp only [eq, f, M, N, P, L]
    rw [internalDegreeEquiv_pure, termEquiv_d, CochainTensor.differential (R := R)]
    rw [hT.differential, termEquiv_d, termEquiv_d]
    simp only [Units.smul_def, map_add, map_zsmul]
    rw [(internalDegreeEquiv E X Y T (n+1)).map_add,
      map_zsmul (internalDegreeEquiv E X Y T (n+1)),
      internalDegreeEquiv_pure, internalDegreeEquiv_pure]
  · intro i j n l q h hq x y a
    by_cases hl : l = 0
    · subst l
      have eqn : n = q := by omega
      cases eqn
      obtain ⟨r, rfl⟩ := E.scalar.surjective a
      obtain ⟨(x : X.X i), rfl⟩ := (termEquiv E X i).surjective x
      obtain ⟨(y : Y.X j), rfl⟩ := (termEquiv E Y j).surjective y
      dsimp only [eq, f, M, N, P, L]
      rw [internalDegreeEquiv_pure, tensor_action_at T _ _ _ hT i j n 0 j n h (add_zero j) (add_zero n)]
      change internalDegreeEquiv E X Y T n (T.tmul (𝟙 A) i j n h (termEquiv E X i x)
        (act N j 0 j (add_zero j) (termEquiv E Y j y) (E.scalar r))) =
        act P n 0 n (add_zero n)
          (termEquiv E (CochainTensor.tensor X Y) n (CochainTensor.pure X Y h x y)) (E.scalar r)
      rw [termEquiv_action, termEquiv_action, internalDegreeEquiv_pure]
      apply congrArg (termEquiv E (CochainTensor.tensor X Y) n)
      change (CochainTensor.ι X Y i j n h).hom (x ⊗ₜ[R] (r • y)) =
        r • (CochainTensor.ι X Y i j n h).hom (x ⊗ₜ[R] y)
      rw [TensorProduct.tmul_smul, map_smul]
    · rw [transported_eq_zero l hl a]
      simp only [map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem internalIso_pure (hT : T.Formulas (𝟙 (transported.{u,v,t} k R)) (E.strict.obj Y))
    (i j n : ℤ) (h : i+j=n) (x : X.X i) (y : Y.X j) :
    ((internalIso E X Y T hT).inv.app ()).f n
      (termEquiv E (CochainTensor.tensor X Y) n (CochainTensor.pure X Y h x y)) =
      T.tmul (𝟙 (transported.{u,v,t} k R)) i j n h (termEquiv E X i x) (termEquiv E Y j y) := by
  change (internalDegreeEquiv E X Y T n).symm
      (termEquiv E (CochainTensor.tensor X Y) n (CochainTensor.pure X Y h x y)) = _
  rw [← internalDegreeEquiv_pure E X Y T i j n h x y, LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
theorem internalTensor : InternalTensor.{u,v,t} := by
  intro k _ _ R _ _ E T U hT
  let e : TensorComparison E T := fun X Y => (internalIso E X Y T (hT (E.strict.obj Y))).symm
  have hp : e.OnPure E T := fun X Y => internalIso_pure E X Y T (hT (E.strict.obj Y))
  refine ⟨e, hp, ?_, ?_⟩
  · intro X Y i j n h x y
    rw [U.tensor_on_pure]
    exact hp X Y i j n h x y
  · intro X X' Y Y' a b c hc
    apply dgHom_ext_at
    intro n w
    obtain ⟨w, rfl⟩ := (termEquiv E (CochainTensor.tensor X Y) n).surjective w
    let p := onOrdinaryTerms E (CochainTensor.tensor X Y)
      (E.strict.map (CochainTensor.map a b) ≫ (e X' Y').hom) n
    let q := onOrdinaryTerms E (CochainTensor.tensor X Y) ((e X Y).hom ≫ c) n
    change p w = q w
    refine DFunLike.congr_fun (ordinaryTensor_add_ext X Y (g := p) (h := q) ?_) w
    intro i j h x y
    change (((e X' Y').hom.app ()).f n) (((E.strict.map (CochainTensor.map a b)).app ()).f n
      (termEquiv E (CochainTensor.tensor X Y) n (CochainTensor.pure X Y h x y))) =
      (c.app ()).f n (((e X Y).hom.app ()).f n
        (termEquiv E (CochainTensor.tensor X Y) n (CochainTensor.pure X Y h x y)))
    rw [termEquiv_map, CochainTensor.map_on_pure]
    change ((e X' Y').hom.app ()).f n ((E.terms (CochainTensor.tensor X' Y')).hom.f n
      (CochainTensor.pure X' Y' h (a.f i x) (b.f j y))) =
        (c.app ()).f n (((e X Y).hom.app ()).f n ((E.terms (CochainTensor.tensor X Y)).hom.f n
          (CochainTensor.pure X Y h x y)))
    rw [hp, hp, hc]
    congr 1
    · exact (termEquiv_map E a i x).symm
    · exact (termEquiv_map E b j y).symm

end InternalTensor

section StrictExtension

variable [Algebra R S] [IsScalarTower k R S]
variable (E : StrictComparison.{u,v,t} k R) (F : StrictComparison.{u,v,t} k S)
variable (X : compValue.{max v t} R)

private abbrev extended (X : compValue.{max v t} R) :=
  (extend.{v,v,max v t} R S).obj X

private def extensionOrdinaryPair (n : ℤ) :
    ((restriction.{u,v,t} k R).obj X).X n →ₗ[k] S →ₗ[k]
      ((restriction.{u,v,t} k S).obj (extended X : compValue.{max v t} S)).X n := by
  refine LinearMap.mk₂ k (fun x s => s ⊗ₜ[R] (show X.X n from x))
    (fun x y s => TensorProduct.tmul_add s (show X.X n from x) (show X.X n from y)) ?_
    (fun x s z => TensorProduct.add_tmul s z (show X.X n from x)) ?_
  · intro c x s
    let x₀ : X.X n := x
    change s ⊗ₜ[R] ((algebraMap k R c) • x₀) = (algebraMap k S c) • (s ⊗ₜ[R] x₀)
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply k R S]
    exact TensorProduct.smul_tmul' (algebraMap k S c) s x₀
  · intro c x s
    let x₀ : X.X n := x
    change (c • s) ⊗ₜ[R] x₀ = (algebraMap k S c) • (s ⊗ₜ[R] x₀)
    rw [Algebra.smul_def]
    exact TensorProduct.smul_tmul' (algebraMap k S c) s x₀

/-- Only the degree-zero term of the regular target module contributes to the
ordinary scalar extension. -/
private def extensionPairFromDG (F : StrictComparison.{u,v,t} k S)
    (X : compValue.{max v t} R) (i j n : ℤ) (h : i+j=n) :
    term (E.strict.obj X) i →ₗ[k] (transported.{u,v,t} k S).complex.X j →ₗ[k]
      ((restriction.{u,v,t} k S).obj (extended X : compValue.{max v t} S)).X n := by
  by_cases hj : j = 0
  · subst j
    rw [add_zero] at h
    subst i
    exact ((extensionOrdinaryPair (k := k) X n).compl₂ F.scalar.toLinearEquiv.symm.toLinearMap).comp
      (termEquiv E X n).symm.toLinearMap
  · exact 0

private theorem extensionPairFromDG_apply (n : ℤ) (x : term (E.strict.obj X) n) (s : S) :
    extensionPairFromDG E F X n 0 n (add_zero n) x (F.scalar s) =
      TensorProduct.tmul R (M := S) (N := (X.X n : Type (max v t))) s ((termEquiv E X n).symm x) := by
  simp only [extensionPairFromDG, dite_true, LinearMap.comp_apply, LinearMap.compl₂_apply,
    extensionOrdinaryPair, LinearMap.mk₂_apply, LinearEquiv.coe_coe]
  exact congrArg (fun z : S => TensorProduct.tmul R (M := S) (N := (X.X n : Type (max v t))) z
    ((termEquiv E X n).symm x))
    (F.scalar.symm_apply_apply s)

private theorem extensionPair_balanced (i l j il lj n : ℤ) (hi : i+l=il) (hj : l+j=lj) (h : il+j=n)
    (x : term (E.strict.obj X) i) (a : (transported.{u,v,t} k R).complex.X l)
    (y : (transported.{u,v,t} k S).complex.X j) :
    extensionPairFromDG E F X il j n h (act (E.strict.obj X) i l il hi x a) y =
      extensionPairFromDG E F X i lj n (by omega) x
        (signedLeft (regular (transported.{u,v,t} k S)) l j lj hj
          ((scalarMap.{u,v,t} k R S).chainMap.f l a) y) := by
  by_cases hl : l = 0
  · subst l
    by_cases h0 : j = 0
    · subst j
      have ei : i = il := by omega
      have ej : 0 = lj := by omega
      have en : i = n := by omega
      cases ei
      cases ej
      cases en
      obtain ⟨r, rfl⟩ := E.scalar.surjective a
      obtain ⟨s, rfl⟩ := F.scalar.surjective y
      obtain ⟨(x : X.X i), rfl⟩ := (termEquiv E X i).surjective x
      have hm : signedLeft (regular (transported.{u,v,t} k S)) 0 0 0 rfl
          ((scalarMap.{u,v,t} k R S).chainMap.f 0 (E.scalar r)) (F.scalar s) = F.scalar (r • s) := by
        rw [Specs.DerivedFormalization.Affine.Tensor.signedLeft_apply, zero_mul, Int.negOnePow_zero, one_smul]
        change (transported.{u,v,t} k S).mul 0 0 0 rfl (F.scalar s)
          ((scalarMap.{u,v,t} k R S).chainMap.f 0 (E.scalar r)) = _
        rw [transportedMap_scalar E F (IsScalarTower.toAlgHom k R S), transported_mul_scalar]
        exact congrArg F.scalar ((mul_comm s ((IsScalarTower.toAlgHom k R S) r)).trans
          (Algebra.smul_def r s).symm)
      change extensionPairFromDG E F X i 0 i (add_zero i)
          (act (E.strict.obj X) i 0 i (add_zero i) (termEquiv E X i x) (E.scalar r)) (F.scalar s) =
        extensionPairFromDG E F X i 0 i (add_zero i) (termEquiv E X i x)
          (signedLeft (regular (transported.{u,v,t} k S)) 0 0 0 rfl
            ((scalarMap.{u,v,t} k R S).chainMap.f 0 (E.scalar r)) (F.scalar s))
      rw [hm, termEquiv_action, extensionPairFromDG_apply, extensionPairFromDG_apply]
      simpa only [LinearEquiv.symm_apply_apply] using (TensorProduct.smul_tmul (R := R) r s x).symm
    · rw [transported_eq_zero j h0 y]
      simp only [map_zero]
  · rw [transported_eq_zero l hl a]
    simp only [map_zero, LinearMap.zero_apply]

variable (T : ModuleTensor.{u,max v t} k)

private def extensionToOrdinary (F : StrictComparison.{u,v,t} k S) (X : compValue.{max v t} R)
    (T : ModuleTensor.{u,max v t} k) (n : ℤ) :
    term ((T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X)) n →ₗ[k]
      ((restriction.{u,v,t} k S).obj (extended X : compValue.{max v t} S)).X n :=
  dgTensorLift T (scalarMap.{u,v,t} k R S) (E.strict.obj X) (regular (transported.{u,v,t} k S)) n
    (fun i j h => extensionPairFromDG E F X i j n h)
    (fun i l j il lj hi hj h => extensionPair_balanced E F X i l j il lj n hi hj h)

private theorem extensionToOrdinary_pure (n : ℤ) (x : X.X n) (s : S) :
    extensionToOrdinary E F X T n (T.tmul (scalarMap.{u,v,t} k R S)
      (N := regular (transported.{u,v,t} k S)) n 0 n (add_zero n) (termEquiv E X n x) (F.scalar s)) =
      s ⊗ₜ[R] x := by
  rw [extensionToOrdinary, dgTensorLift_tmul, extensionPairFromDG_apply, LinearEquiv.symm_apply_apply]

private abbrev extensionPairToDG (n : ℤ) :
    S →+ X.X n →+ term ((T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X)) n := by
  letI := Module.restrictScalars k R (X.X n)
  exact (LinearMap.toAddMonoidHom'.comp
    (((dgPair T (scalarMap.{u,v,t} k R S) (E.strict.obj X)
      (regular (transported.{u,v,t} k S)) n 0 n (add_zero n)).compl₂
        F.scalar.toLinearEquiv.toLinearMap).comp (termEquiv E X n).toLinearMap).flip.toAddMonoidHom)

private theorem extensionPairToDG_balanced (n : ℤ) (r : R) (s : S) (x : X.X n) :
    extensionPairToDG E F X T n (r • s) x = extensionPairToDG E F X T n s (r • x) := by
  let A := transported.{u,v,t} k R
  let B := transported.{u,v,t} k S
  let f : A ⟶ B := scalarMap.{u,v,t} k R S
  let M := E.strict.obj X
  have h := balance T f M (regular B) n 0 0 n 0 n (add_zero n) rfl (add_zero n)
    (termEquiv E X n x) (E.scalar r) (F.scalar s)
  rw [Specs.DerivedFormalization.Affine.Tensor.signedLeft_apply, zero_mul, Int.negOnePow_zero,
    one_smul] at h
  change _ = T.tmul f (N := regular B) n 0 n (add_zero n) (termEquiv E X n x)
    (B.mul 0 0 0 rfl (F.scalar s) (f.chainMap.f 0 (E.scalar r))) at h
  rw [transportedMap_scalar E F (IsScalarTower.toAlgHom k R S), transported_mul_scalar, termEquiv_action] at h
  rw [mul_comm s] at h
  change T.tmul f (N := regular B) n 0 n (add_zero n) (termEquiv E X n x) (F.scalar (r • s)) =
    T.tmul f (N := regular B) n 0 n (add_zero n) (termEquiv E X n (r • x)) (F.scalar s)
  rw [Algebra.smul_def r s]
  exact h.symm

private def extensionFromOrdinary (n : ℤ) :
    (S ⊗[R] X.X n) →+ term ((T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X)) n :=
  TensorProduct.liftAddHom (extensionPairToDG E F X T n) (extensionPairToDG_balanced E F X T n)

private theorem extensionFromOrdinary_pure (n : ℤ) (x : X.X n) (s : S) :
    extensionFromOrdinary E F X T n (s ⊗ₜ[R] x) =
      T.tmul (scalarMap.{u,v,t} k R S) (N := regular (transported.{u,v,t} k S))
        n 0 n (add_zero n) (termEquiv E X n x) (F.scalar s) := rfl

private theorem tmul_zero_right {A B : CommDGAlgebra.{u,v} k} (T : ModuleTensor.{u,v} k)
    (f : A ⟶ B) (M : A.Module) (N : B.Module) (i j n : ℤ) (h : i+j=n) (x : term M i) :
    T.tmul f (N := N) i j n h x 0 = 0 := (dgPair T f M N i j n h x).map_zero

private def extensionDegreeEquiv (n : ℤ) :
    term ((T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X)) n ≃ₗ[k]
      term (F.strict.obj (extended X)) n := by
  let f := scalarMap.{u,v,t} k R S
  let M := E.strict.obj X
  let N := regular (transported.{u,v,t} k S)
  let p := extensionToOrdinary E F X T n
  let q := extensionFromOrdinary E F X T n
  have hp : q.comp p.toAddMonoidHom = AddMonoidHom.id _ := by
    apply dgTensor_add_ext T f M N n
    intro i j h x y
    change q (p (T.tmul f (N := N) i j n h x y)) = T.tmul f (N := N) i j n h x y
    by_cases hj : j = 0
    · subst j
      have he : i = n := by omega
      subst i
      obtain ⟨(x : X.X n), rfl⟩ := (termEquiv E X n).surjective x
      obtain ⟨y, rfl⟩ := F.scalar.surjective y
      dsimp only [p, q, f]
      rw [extensionToOrdinary_pure, extensionFromOrdinary_pure]
    · rw [transported_eq_zero j hj y, tmul_zero_right, map_zero]
      exact q.map_zero
  have hq : p.toAddMonoidHom.comp q = AddMonoidHom.id _ := by
    apply tensor_add_ext (R := R)
    intro s x
    change p (q (s ⊗ₜ[R] x)) = s ⊗ₜ[R] x
    dsimp only [p, q]
    rw [extensionFromOrdinary_pure, extensionToOrdinary_pure]
  exact (LinearEquiv.ofBijective p ⟨
    (show Function.LeftInverse q p from fun x => DFunLike.congr_fun hp x).injective,
    (show Function.RightInverse q p from fun x => DFunLike.congr_fun hq x).surjective⟩).trans
    (termEquiv F (extended X) n)

private theorem extensionDegreeEquiv_pure (n : ℤ) (x : X.X n) (s : S) :
    extensionDegreeEquiv E F X T n (T.tmul (scalarMap.{u,v,t} k R S)
      (N := regular (transported.{u,v,t} k S)) n 0 n (add_zero n) (termEquiv E X n x) (F.scalar s)) =
      termEquiv F (extended X) n (s ⊗ₜ[R] x) := by
  change termEquiv F (extended X) n (extensionToOrdinary E F X T n
    (T.tmul (scalarMap.{u,v,t} k R S) (N := regular (transported.{u,v,t} k S))
      n 0 n (add_zero n) (termEquiv E X n x) (F.scalar s))) = _
  rw [extensionToOrdinary_pure]

set_option backward.isDefEq.respectTransparency false in
private def extensionIso
    (hT : T.Formulas (scalarMap.{u,v,t} k R S) (regular (transported.{u,v,t} k S))) :
    (T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X) ≅ F.strict.obj (extended X) := by
  let A := transported.{u,v,t} k R
  let B := transported.{u,v,t} k S
  let f : A ⟶ B := scalarMap.{u,v,t} k R S
  let M := E.strict.obj X
  let N := regular B
  let P := F.strict.obj (extended X)
  apply dgTensorIsoOfTerms T f M N P (extensionDegreeEquiv E F X T)
  · intro i j n h x y
    by_cases hj : j = 0
    · subst j
      have hi : i = n := by omega
      cases hi
      obtain ⟨(x : X.X i), rfl⟩ := (termEquiv E X i).surjective x
      obtain ⟨s, rfl⟩ := F.scalar.surjective y
      dsimp only [f, M, N, P]
      rw [extensionDegreeEquiv_pure, termEquiv_d, hT.differential, termEquiv_d]
      have hz : ((N.complex ()).d 0 (0+1)) (F.scalar s) = 0 :=
        transported_eq_zero (0+1) (by decide) _
      rw [hz, tmul_zero_right, smul_zero, add_zero]
      rw [extensionDegreeEquiv_pure]
      rfl
    · rw [transported_eq_zero j hj y, tmul_zero_right]
      simp only [map_zero]
  · intro i j n l q h hq x y a
    by_cases hj : j = 0
    · subst j
      have hi : i = n := by omega
      cases hi
      by_cases hl : l = 0
      · subst l
        have eqn : i = q := by omega
        cases eqn
        obtain ⟨(x : X.X i), rfl⟩ := (termEquiv E X i).surjective x
        obtain ⟨s, rfl⟩ := F.scalar.surjective y
        obtain ⟨a, rfl⟩ := F.scalar.surjective a
        dsimp only [f, M, N, P]
        rw [extensionDegreeEquiv_pure, tensor_action_at T _ _ _ hT i 0 i 0 0 i (add_zero i) rfl (add_zero i)]
        change extensionDegreeEquiv E F X T i (T.tmul f (N := N)
            i 0 i (add_zero i) (termEquiv E X i x) (B.mul 0 0 0 rfl (F.scalar s) (F.scalar a))) =
          act P i 0 i (add_zero i) (termEquiv F (extended X) i (s ⊗ₜ[R] x)) (F.scalar a)
        rw [transported_mul_scalar, extensionDegreeEquiv_pure, termEquiv_action]
        congr 1
        change (s * a) ⊗ₜ[R] x = a • (s ⊗ₜ[R] x)
        rw [mul_comm s a]
        rfl
      · rw [transported_eq_zero l hl a]
        simp only [map_zero]
    · rw [transported_eq_zero j hj y, tmul_zero_right]
      simp only [map_zero, LinearMap.zero_apply]

private theorem extensionIso_pure
    (hT : T.Formulas (scalarMap.{u,v,t} k R S) (regular (transported.{u,v,t} k S)))
    (n : ℤ) (x : X.X n) (s : S) :
    ((extensionIso E F X T hT).inv.app ()).f n (termEquiv F (extended X) n (s ⊗ₜ[R] x)) =
      T.tmul (scalarMap.{u,v,t} k R S) (N := regular (transported.{u,v,t} k S))
        n 0 n (add_zero n) (termEquiv E X n x) (F.scalar s) := by
  change (extensionDegreeEquiv E F X T n).symm (termEquiv F (extended X) n (s ⊗ₜ[R] x)) = _
  rw [← extensionDegreeEquiv_pure E F X T n x s, LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
theorem scalarExtension : ScalarExtension.{u,v,t} := by
  intro k _ _ R S _ _ _ _ _ _ E F T hT
  let e := fun X : compValue.{max v t} R => (extensionIso E F X T hT).symm
  let r := scalarMap.{u,v,t} k R S
  let iso : (extend.{v,v,max v t} R S) ⋙ F.strict ≅ E.strict ⋙ T.baseChange r :=
    NatIso.ofComponents e (by
      intro X Y a
      let p := F.strict.map ((extend.{v,v,max v t} R S).map a) ≫ (e Y).hom
      let q := (e X).hom ≫ (T.baseChange r).map (E.strict.map a)
      change p = q
      apply extendHom_ext F (extended X)
      intro n w
      change onOrdinaryTerms F (extended X) p n w = onOrdinaryTerms F (extended X) q n w
      refine DFunLike.congr_fun (tensor_add_ext (R := R) (f := onOrdinaryTerms F (extended X) p n)
        (g := onOrdinaryTerms F (extended X) q n) ?_) w
      intro s x
      change (((e Y).hom.app ()).f n) (((F.strict.map ((extend.{v,v,max v t} R S).map a)).app ()).f n
          (termEquiv F (extended X) n (s ⊗ₜ[R] x))) =
        ((((T.baseChange r).map (E.strict.map a)).app ()).f n)
          (((e X).hom.app ()).f n (termEquiv F (extended X) n (s ⊗ₜ[R] x)))
      rw [termEquiv_map, extend_map_tmul]
      dsimp only [e, Iso.symm_hom]
      rw [extensionIso_pure, extensionIso_pure, hT.first (E.strict.map a), termEquiv_map])
  exact ⟨⟨iso, fun X n s x => extensionIso_pure E F X T hT n x s⟩⟩

end StrictExtension

set_option backward.isDefEq.respectTransparency false in
private abbrev toK {A : CommDGAlgebra.{u,v} k} (h : HomotopyCategoryLaws (dgCat A)) :
    letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory (dgCat A) h
    A.Module ⥤ Specs.DerivedFormalization.DG.HomComplex.homotopyCategory (dgCat A) :=
  RightDGModule.toHomotopyCategory (dgCat A)

set_option backward.isDefEq.respectTransparency false in
theorem localizedTensor : LocalizedTensor.{u,v,t} := by
  intro k _ _ R _ _ E T e hE _ h H
  dsimp only
  intro I X Y hX hY
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k R)) h
  letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k R)) h
  letI := I
  let A := transported.{u,v,t} k R
  let Q := quotient (dgCat A) h
  let L := (restrictedLocalization (dgCat A) h).asEquivalence
  let J := (kProjectiveObjects (dgCat A)).ι
  let P := E.strict.obj X
  let N := E.strict.obj Y
  let P₀ : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨P, hE X hX⟩
  let N₀ : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨N, hE Y hY⟩
  let ε := ((J.mapIso (L.unitIso.app P₀)).symm).prod ((J.mapIso (L.unitIso.app N₀)).symm)
  let d := (H.functor ⋙ Q).mapIso ε ≪≫ Q.mapIso (eqToIso (H.obj P N))
  exact ⟨d ≪≫ Q.mapIso ((toK h).mapIso (e X Y).symm), rfl⟩

section Extension

variable [Algebra R S] [IsScalarTower k R S]

set_option backward.isDefEq.respectTransparency false in
theorem localizedExtension : LocalizedExtension.{u,v,t} := by
  intro k _ _ R S _ _ _ _ _ _ E F T e hR hS W hE
  dsimp only
  intro P hP
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k R)) hR
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory (dgCat (transported.{u,v,t} k S)) hS
  letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k R)) hR
  letI := derivedCategoryInstance (dgCat (transported.{u,v,t} k S)) hS
  let QS := quotient (dgCat (transported.{u,v,t} k S)) hS
  exact ⟨W.onProjective _ (hE P hP) ≪≫ QS.mapIso ((toK hS).mapIso (e.iso.app P).symm), rfl⟩

end Extension

section Unit

set_option backward.isDefEq.respectTransparency false in
theorem scalarExtensionUnit : ScalarExtensionUnit.{u,v,t} := by
  intro k _ _ R _ _ E T e hT
  let A := transported.{u,v,t} k R
  let r : A ⟶ A := scalarMap.{u,v,t} k R R
  have er : r = 𝟙 A := scalarMap_id
  refine ⟨er, fun X => ?_⟩
  obtain ⟨a, ha⟩ := hT.identity (E.strict.obj X)
  refine ⟨a, ?_, ha⟩
  apply extendHom_ext E ((extend.{v,v,max v t} R R).obj X)
  intro n w
  refine DFunLike.congr_fun (tensor_add_ext (R := R) (f := onOrdinaryTerms E ((extend.{v,v,max v t} R R).obj X)
      (((e.iso.app X).hom ≫ eqToHom (congrArg (fun m => T.obj m (E.strict.obj X) (regular A)) er)) ≫ a.hom) n)
    (g := onOrdinaryTerms E ((extend.{v,v,max v t} R R).obj X) (E.strict.map (extendId R X).hom) n) ?_) w
  intro s x
  change (a.hom.app ()).f n
      (((eqToHom (congrArg (fun m => T.obj m (E.strict.obj X) (regular A)) er)).app ()).f n
        (((e.iso.hom.app X).app ()).f n
          (termEquiv E ((extend.{v,v,max v t} R R).obj X) n (s ⊗ₜ[R] x)))) =
    ((E.strict.map (extendId R X).hom).app ()).f n
      (termEquiv E ((extend.{v,v,max v t} R R).obj X) n (s ⊗ₜ[R] x))
  rw [show ((e.iso.hom.app X).app ()).f n
        (termEquiv E ((extend.{v,v,max v t} R R).obj X) n (s ⊗ₜ[R] x)) = _ from e.on_tmul X n s x,
    cast_tmul T er (E.strict.obj X) (regular A), ha, termEquiv_map, extendId_hom_tmul]
  exact E.action X n s x

end Unit

section Tower

variable [Algebra R S] [IsScalarTower k R S]
variable [Algebra R V] [Algebra S V] [IsScalarTower k R V] [IsScalarTower k S V]
variable [IsScalarTower R S V]

private theorem scalarMap_comp :
    scalarMap.{u,v,t} k R S ≫ scalarMap.{u,v,t} k S V = scalarMap.{u,v,t} k R V := by
  have h : CommAlgCat.ofHom (IsScalarTower.toAlgHom k R S) ≫
      CommAlgCat.ofHom (IsScalarTower.toAlgHom k S V) =
        CommAlgCat.ofHom (IsScalarTower.toAlgHom k R V) :=
    CommAlgCat.hom_ext (AlgHom.ext fun r => (IsScalarTower.algebraMap_apply R S V r).symm)
  exact ((stalkFunctor.{u,v,t} k).map_comp
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R S))
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k S V))).symm.trans
      (congrArg (stalkFunctor.{u,v,t} k).map h)

set_option backward.isDefEq.respectTransparency false in
private theorem tower_square
    (E : StrictComparison.{u,v,t} k R) (F : StrictComparison.{u,v,t} k S)
    (G : StrictComparison.{u,v,t} k V) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionComparison E F T) (f : ExtensionComparison F G T) (g : ExtensionComparison E G T)
    (hT : T.Formulas (scalarMap.{u,v,t} k S V) (regular (transported.{u,v,t} k V)))
    (X : compValue.{max v t} R)
    (a : (T.baseChange (scalarMap.{u,v,t} k S V)).obj
          ((T.baseChange (scalarMap.{u,v,t} k R S)).obj (E.strict.obj X)) ⟶
      (T.baseChange (scalarMap.{u,v,t} k R S ≫ scalarMap.{u,v,t} k S V)).obj (E.strict.obj X))
    (ha : TowerOnPure T (E.strict.obj X) a) :
    TowerSquare E T F G e f g scalarMap_comp X a := by
  dsimp only [TowerSquare]
  let A := transported.{u,v,t} k R
  let B := transported.{u,v,t} k S
  let C := transported.{u,v,t} k V
  let r : A ⟶ B := scalarMap.{u,v,t} k R S
  let s : B ⟶ C := scalarMap.{u,v,t} k S V
  let d : A ⟶ C := scalarMap.{u,v,t} k R V
  let X₁ := (extend.{v,v,max v t} R S).obj X
  let X₂ := (extend.{v,v,max v t} S V).obj X₁
  have ed : r ≫ s = d := scalarMap_comp
  apply extendHom_ext G X₂
  intro n w
  let p := onOrdinaryTerms G X₂ ((f.iso.app X₁).hom ≫ (T.baseChange s).map (e.iso.app X).hom ≫
    a ≫ eqToHom (congrArg (fun m => T.obj m (E.strict.obj X) (regular C)) ed)) n
  let q := onOrdinaryTerms G X₂ (G.strict.map (extendComp R S V X).hom ≫ (g.iso.app X).hom) n
  change p w = q w
  refine DFunLike.congr_fun (tensor_add_ext (R := S) (f := p) (g := q) ?_) w
  intro z y
  let m := (TensorProduct.mk S V (X₁.X n) z).toAddMonoidHom
  refine DFunLike.congr_fun (tensor_add_ext (R := R)
    (f := p.comp m) (g := q.comp m) ?_) y
  intro b x
  change ((eqToHom (congrArg (fun m => T.obj m (E.strict.obj X) (regular C)) ed)).app ()).f n
      ((a.app ()).f n ((((T.baseChange s).map (e.iso.app X).hom).app ()).f n
        (((f.iso.hom.app X₁).app ()).f n (termEquiv G X₂ n (z ⊗ₜ[S] (b ⊗ₜ[R] x)))))) =
    ((g.iso.hom.app X).app ()).f n (((G.strict.map (extendComp R S V X).hom).app ()).f n
      (termEquiv G X₂ n (z ⊗ₜ[S] (b ⊗ₜ[R] x))))
  rw [show ((f.iso.hom.app X₁).app ()).f n (termEquiv G X₂ n (z ⊗ₜ[S] (b ⊗ₜ[R] x))) =
      T.tmul s (N := regular C) n 0 n (add_zero n) (termEquiv F X₁ n (b ⊗ₜ[R] x)) (G.scalar z)
      from f.on_tmul X₁ n z (b ⊗ₜ[R] x)]
  rw [hT.first (e.iso.app X).hom n 0 n (add_zero n)]
  rw [show ((e.iso.app X).hom.app ()).f n (termEquiv F X₁ n (b ⊗ₜ[R] x)) =
      T.tmul r (N := regular B) n 0 n (add_zero n) (termEquiv E X n x) (F.scalar b)
      from e.on_tmul X n b x]
  rw [ha n 0 0 n n (add_zero n) (add_zero n), cast_tmul T ed (E.strict.obj X) (regular C),
    termEquiv_map, extendComp_hom_tmul]
  rw [show ((g.iso.hom.app X).app ()).f n
        (termEquiv G ((extend.{v,v,max v t} R V).obj X) n ((b • z) ⊗ₜ[R] x)) = _
      from g.on_tmul X n (b • z) x]
  congr 1
  change (transported.{u,v,t} k V).mul 0 0 0 rfl ((scalarMap.{u,v,t} k S V).chainMap.f 0
    (F.scalar b)) (G.scalar z) = G.scalar (b • z)
  rw [transportedMap_scalar F G (IsScalarTower.toAlgHom k S V), transported_mul_scalar]
  exact congrArg G.scalar (Algebra.smul_def b z).symm

set_option backward.isDefEq.respectTransparency false in
theorem scalarExtensionTower : ScalarExtensionTower.{u,v,t} := by
  intro k _ _ R S V _ _ _ _ _ _ _ _ _ _ _ _ _ E F G T e f g hT comparisons
  refine ⟨scalarMap_comp, fun X => ?_⟩
  obtain ⟨a, ha⟩ := comparisons.compose (scalarMap.{u,v,t} k R S)
    (scalarMap.{u,v,t} k S V) (E.strict.obj X)
  exact ⟨a, ha, tower_square E F G T e f g hT X a.hom ha⟩

set_option backward.isDefEq.respectTransparency false in
theorem localizedExtensionTower :
    LocalizedExtensionTower.{u,v,t} := by
  intro k _ _ R S V _ _ _ _ _ _ _ _ _ _ _ _ _ E F G T e f g hR hS hV W Y Z hT hE hc
  dsimp only
  obtain ⟨a, b, ha, hb⟩ := hc
  exact ⟨scalarMap_comp, a, b, fun X => tower_square E F G T e f g hT X _ (ha _),
    ha, fun P hP => hb _ (hE P hP)⟩

end Tower

end

end DerivedFormalization.Affine.OrdinaryDGTensorComparison
