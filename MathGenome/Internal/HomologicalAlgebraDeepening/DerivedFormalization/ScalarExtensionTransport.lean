import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ScalarExtensionTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ScalarExtensionModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorMonoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorTransport
/-! Conditional scalar-extension proofs for cochain models. -/

namespace DerivedFormalization.ScalarExtensionTransport

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.HomComplex
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.CochainRingTransport
  (representedExtension representedExtensionAdjunction)
open Specs.DerivedFormalization.CochainTensorTransport
  (adequateModelType closedAdjunctionType curryingType ringComparisonType)
open Specs.DerivedFormalization.ScalarExtensionTransport

universe u w z a

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

variable {R : Type u} {S : Type w} {T : Type z} {B C : Type a}
  [CommRing R] [CommRing S] [CommRing T] [CommRing B] [CommRing C]
  (d : S ≃+* B) (f : R →+* S)

local notation "L" => extension d f
local notation "U" => restriction d f
local notation "J" => representedExtensionAdjunction d f

private theorem unit_apply (X : compValue.{a} R) (i : ℤ) (x : X.X i) :
    ((extensionAdjunction d f).unit.app X).f i x = extendPure d f X i 1 x := by
  change ((1 : B) ⊗ₜ[R,d.toRingHom.comp f] x) = _
  exact congrArg (fun b : B => b ⊗ₜ[R,d.toRingHom.comp f] x) (d.map_one.symm)

private theorem extendPure_smul (X : compValue.{a} R) (i : ℤ) (s t : S) (x : X.X i) :
    s • extendPure d f X i t x = extendPure d f X i (s * t) x := by
  have h := ModuleCat.ExtendScalars.smul_tmul (d.toRingHom.comp f) (d s) (d t) x
  change _ = (d (s * t) ⊗ₜ[R,d.toRingHom.comp f] x)
  exact h.trans (congrArg (fun b : B => b ⊗ₜ[R,d.toRingHom.comp f] x) (d.map_mul s t).symm)

private theorem extendPure_map {X Y : compValue.{a} R} (b : X ⟶ Y)
    (i : ℤ) (s : S) (x : X.X i) :
    ((L).map b).f i (extendPure d f X i s x) = extendPure d f Y i s (b.f i x) :=
  rfl

private theorem extendPure_smul_source (X : compValue.{a} R) (i : ℤ)
    (s : S) (r : R) (x : X.X i) :
    extendPure d f X i s (r • x) = extendPure d f X i (s * f r) x := by
  let M := (ModuleCat.restrictScalars (d.toRingHom.comp f)).obj (ModuleCat.of B B)
  change (show M from d s) ⊗ₜ[R] (r • x) = (show M from d (s * f r)) ⊗ₜ[R] x
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have he : r • (show M from d s) = (show M from d (s * f r)) := by
    change d (f r) * d s = d (s * f r)
    rw [map_mul, mul_comm]
  rw [he]

private theorem extendPure_d (X : compValue.{a} R) (i j : ℤ) (s : S) (x : X.X i) :
    ((L).obj X).d i j (extendPure d f X i s x) = extendPure d f X j s (X.d i j x) :=
  rfl

section Native

variable {B' : Type (max w a)} [CommRing B'] (d' : S ≃+* B')

private theorem nativeExtension_on_pure (X : compValue.{max w a} R) (i : ℤ)
    (s : S) (x : X.X i) :
    ((nativeExtensionIso f d').hom.app X).f i (s ⊗ₜ[R,f] x) = extendPure d' f X i s x := by
  have hh := (cochainAdjunction (ModuleCat.extendRestrictScalarsAdj.{a} f))
    |>.unit_leftAdjointUniq_hom_app (extensionAdjunction d' f) X
  have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hh i) x
  change ((nativeExtensionIso f d').hom.app X).f i ((1 : S) ⊗ₜ[R,f] x) =
    ((extensionAdjunction d' f).unit.app X).f i x at h
  rw [unit_apply] at h
  calc
    _ = ((nativeExtensionIso f d').hom.app X).f i
          (s • (show (ModuleCat.extendScalars f).obj (X.X i) from (1 : S) ⊗ₜ[R,f] x)) := by
      have hs := ModuleCat.ExtendScalars.smul_tmul f s 1 x
      rw [mul_one] at hs
      exact congrArg (((nativeExtensionIso f d').hom.app X).f i) hs.symm
    _ = s • extendPure d' f X i 1 x := by rw [map_smul, h]
    _ = _ := by rw [extendPure_smul, mul_one]

end Native

theorem nativeExtension_conditional.{ru,su,au}
    (_ : adequateModelType.{ru,au}) (_ : closedAdjunctionType.{ru,au})
    (_ : curryingType.{ru,au}) (_ : ringComparisonType.{ru,au}) :
    nativeExtensionType.{ru,su,au} := by
  intro R S B _ _ _ d f X i s x
  exact nativeExtension_on_pure f d X i s x

section SignedHom

variable (P : compValue.{a} R) (E : compValue.{a} S)

local notation "M" => ModuleCat.restrictScalars f

private def transposeCochain (q : ℤ) (k : Cochain ((L).obj P) E q) :
    Cochain P ((U).obj E) q :=
  (Cochain.ofHom ((extensionAdjunction d f).unit.app P)).comp (k.map M) (zero_add q)

private theorem transposeCochain_v (q : ℤ) (k : Cochain ((L).obj P) E q)
    (i j : ℤ) (h : i + q = j) :
    (transposeCochain d f P E q k).v i j h = (J).homEquiv _ _ (k.v i j h) := by
  rw [transposeCochain, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.map_v,
    Adjunction.homEquiv_unit]
  rfl

private def untransposeCochain (q : ℤ) (k : Cochain P ((U).obj E) q) :
    Cochain ((L).obj P) E q :=
  Cochain.mk fun i j h => ((J).homEquiv _ _).symm (k.v i j h)

private def transposeCochainEquiv (q : ℤ) :
    ((U).obj (internalHomValue ((L).obj P) E)).X q ≃ₗ[R] (internalHomValue P ((U).obj E)).X q where
  toFun := transposeCochain d f P E q
  invFun := untransposeCochain d f P E q
  left_inv k := by
    apply Cochain.ext
    intro i j h
    rw [untransposeCochain, Cochain.mk_v, transposeCochain_v, Equiv.symm_apply_apply]
  right_inv k := by
    apply Cochain.ext
    intro i j h
    rw [transposeCochain_v, untransposeCochain, Cochain.mk_v, Equiv.apply_symm_apply]
  map_add' k l := by
    change Cochain ((L).obj P) E q at k l
    apply Cochain.ext
    intro i j h
    change (transposeCochain d f P E q (k + l)).v i j h =
      (transposeCochain d f P E q k + transposeCochain d f P E q l).v i j h
    simp only [transposeCochain_v, Cochain.add_v, Adjunction.homEquiv_unit,
      Functor.map_add, Preadditive.comp_add]
  map_smul' r k := by
    change Cochain ((L).obj P) E q at k
    apply Cochain.ext
    intro i j h
    change (transposeCochain d f P E q (f r • k)).v i j h =
      (r • transposeCochain d f P E q k).v i j h
    simp only [transposeCochain_v, Cochain.smul_v, Adjunction.homEquiv_unit]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private def signedHomIso :
    (U).obj (internalHomValue ((L).obj P) E) ≅ internalHomValue P ((U).obj E) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => (transposeCochainEquiv d f P E q).toModuleIso) ?_
  intro n m _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro k
  change δ n m (transposeCochain d f P E n k) = transposeCochain d f P E m (δ n m k)
  simp only [transposeCochain, δ_ofHom_comp, δ_map]

private theorem signedHom_on_eval {q i j : ℤ} (h : i + q = j)
    (k : Cochain ((L).obj P) E q) (x : P.X i) :
    (((signedHomIso d f P E).hom.f q k).v i j h) x =
      k.v i j h (extendPure d f P i 1 x) := by
  change (transposeCochain d f P E q k).v i j h x = _
  rw [transposeCochain_v, Adjunction.homEquiv_unit]
  change k.v i j h (((extensionAdjunction d f).unit.app P).f i x) = _
  rw [unit_apply]

private theorem signedHom_inverse_on_eval {q i j : ℤ} (h : i + q = j)
    (k : Cochain P ((U).obj E) q) (x : P.X i) (s : S) :
    ((signedHomIso d f P E).inv.f q k).v i j h (extendPure d f P i s x) =
      s • (show E.X j from k.v i j h x) := by
  let b : ((L).obj P).X i ⟶ E.X j := ((J).homEquiv _ _).symm (k.v i j h)
  change (untransposeCochain d f P E q k).v i j h (extendPure d f P i s x) = _
  rw [untransposeCochain, Cochain.mk_v]
  change b (extendPure d f P i s x) = _
  have he : (J).homEquiv (P.X i) (E.X j) b = k.v i j h := Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at he
  have hx := ConcreteCategory.congr_hom he x
  change b (((extensionAdjunction d f).unit.app P).f i x) = k.v i j h x at hx
  rw [unit_apply] at hx
  rw [← mul_one s, ← extendPure_smul, map_smul, hx]
  simp only [mul_one]

end SignedHom

section Cancellation

open Specs.DerivedFormalization.CochainTensor (tensor ι pure map isKFlat)

private def cancelModule (M : ModuleCat.{a} S) (N : ModuleCat.{a} R) :
    (ModuleCat.restrictScalars f).obj
        (ModuleCat.of S (M ⊗[S] (representedExtension d f).obj N)) ≅
      ModuleCat.of R (((ModuleCat.restrictScalars f).obj M) ⊗[R] N) := by
  let f₀ := d.toRingHom.comp f
  letI : Algebra R B := f₀.toAlgebra
  letI : Module B M := Module.compHom M d.symm.toRingHom
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R B M := IsScalarTower.of_algebraMap_smul fun r m => by
    change d.symm (d (f r)) • m = f r • m
    rw [RingEquiv.symm_apply_apply]
  let N₁ := (representedExtension d f).obj N
  let N₂ := (ModuleCat.extendScalars f₀).obj N
  letI : RingHomInvPair d.toRingHom d.symm.toRingHom :=
    ⟨by ext s; exact d.symm_apply_apply s, by ext b; exact d.apply_symm_apply b⟩
  letI : RingHomInvPair d.symm.toRingHom d.toRingHom :=
    ⟨by ext b; exact d.apply_symm_apply b, by ext s; exact d.symm_apply_apply s⟩
  let eM : M ≃ₛₗ[d.toRingHom] M :=
    { AddEquiv.refl M with
      map_smul' := fun s m => by
        change s • m = d.symm (d s) • m
        rw [RingEquiv.symm_apply_apply] }
  let eN : N₁ ≃ₛₗ[d.toRingHom] N₂ :=
    { (show N₁ ≃+ N₂ from AddEquiv.refl N₂) with map_smul' := fun _ _ => rfl }
  let e := TensorProduct.congr eM eN
  let k : M ⊗[B] N₂ ≃ₗ[B] M ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R B B M N
  let l : (ModuleCat.restrictScalars f).obj (ModuleCat.of S (M ⊗[S] N₁)) ≃ₗ[R]
      (ModuleCat.of R (((ModuleCat.restrictScalars f).obj M) ⊗[R] N)) :=
    { e.toAddEquiv.trans k.toAddEquiv with
      map_smul' := fun r y => by
        change k (e (f r • y)) = r • k (e y)
        rw [e.map_smulₛₗ, k.map_smul]
        exact IsScalarTower.algebraMap_smul B r (k (e y)) }
  exact l.toModuleIso

private theorem cancelModule_on_pure (M : ModuleCat.{a} S) (N : ModuleCat.{a} R)
    (x : M) (s : S) (y : N) :
    (cancelModule d f M N).hom (x ⊗ₜ[S]
      (show (representedExtension d f).obj N from d s ⊗ₜ[R,d.toRingHom.comp f] y)) =
      (show (ModuleCat.restrictScalars f).obj M from s • x) ⊗ₜ[R] y := by
  dsimp only [cancelModule, LinearEquiv.toModuleIso, AddEquiv.trans_apply,
    TensorProduct.congr_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  change (show (ModuleCat.restrictScalars f).obj M from d.symm (d s) • x) ⊗ₜ[R] y = _
  rw [RingEquiv.symm_apply_apply]

private theorem cancelModule_inverse_on_pure (M : ModuleCat.{a} S) (N : ModuleCat.{a} R)
    (x : M) (y : N) :
    (cancelModule d f M N).inv ((show (ModuleCat.restrictScalars f).obj M from x) ⊗ₜ[R] y) =
      x ⊗ₜ[S] (show (representedExtension d f).obj N from d (1 : S) ⊗ₜ[R,d.toRingHom.comp f] y) := by
  apply (ConcreteCategory.bijective_of_isIso (cancelModule d f M N).hom).1
  rw [cancelModule_on_pure, one_smul]
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom (cancelModule d f M N).inv_hom_id
      ((show (ModuleCat.restrictScalars f).obj M from x) ⊗ₜ[R] y)

variable (E : compValue.{a} S) (P : compValue.{a} R)

private def cancelSummands (n : ℤ) :
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ModuleCat.of R (((U).obj E).X p.1.1 ⊗[R] P.X p.1.2)) ≅
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ModuleCat.of S (E.X p.1.1 ⊗[S] ((L).obj P).X p.1.2)) ⋙ ModuleCat.restrictScalars f :=
  Discrete.natIso fun p => (cancelModule d f (E.X p.as.1.1) (P.X p.as.1.2)).symm

private def restrictedTensorColimit (n : ℤ) :
    IsColimit ((Cocone.precompose (cancelSummands d f E P n).hom).obj
      ((ModuleCat.restrictScalars f).mapCocone
        (Specs.DerivedFormalization.CochainTensor.cofan E ((L).obj P) n))) := by
  letI : (ModuleCat.restrictScalars.{a} f).IsLeftAdjoint :=
    (Specs.DerivedFormalization.CochainRingTransport.representedCoextensionAdjunction d f).isLeftAdjoint
  exact (IsColimit.precomposeHomEquiv _ _).symm
    (isColimitOfPreserves (ModuleCat.restrictScalars f)
      (CochainTensor.tensorCofanIsColimit E ((L).obj P) n))

private def cancelTerm (n : ℤ) :
    (tensor ((U).obj E) P).X n ≅ ((U).obj (tensor E ((L).obj P))).X n :=
  (CochainTensor.tensorCofanIsColimit ((U).obj E) P n).coconePointUniqueUpToIso
    (restrictedTensorColimit d f E P n)

private theorem cancelTerm_on_pure {i j n : ℤ} (h : i + j = n)
    (x : E.X i) (y : P.X j) :
    (cancelTerm d f E P n).hom (pure ((U).obj E) P h x y) =
      pure E ((L).obj P) h x (extendPure d f P j 1 y) := by
  have he := IsColimit.comp_coconePointUniqueUpToIso_hom
    (CochainTensor.tensorCofanIsColimit ((U).obj E) P n)
    (restrictedTensorColimit d f E P n) (Discrete.mk ⟨(i, j), h⟩)
  have ht := ConcreteCategory.congr_hom he
    ((show ((U).obj E).X i from x) ⊗ₜ[R] y)
  change (cancelTerm d f E P n).hom (pure ((U).obj E) P h x y) =
    ι E ((L).obj P) i j n h
      ((cancelModule d f (E.X i) (P.X j)).inv ((show ((U).obj E).X i from x) ⊗ₜ[R] y)) at ht
  rw [cancelModule_inverse_on_pure] at ht
  exact ht

private def cancelIso :
    (U).obj (tensor E ((L).obj P)) ≅ tensor ((U).obj E) P :=
  (HomologicalComplex.Hom.isoOfComponents (cancelTerm d f E P) (by
    intro n m hnm
    have hs : n + 1 = m := hnm
    subst m
    apply CochainTensor.term_hom_ext
    intro i j h x y
    change (tensor E ((L).obj P)).d n (n + 1)
        ((cancelTerm d f E P n).hom (pure ((U).obj E) P h x y)) =
      (cancelTerm d f E P (n + 1)).hom
        ((tensor ((U).obj E) P).d n (n + 1) (pure ((U).obj E) P h x y))
    rw [cancelTerm_on_pure, CochainTensor.differential, CochainTensor.differential]
    simp only [Units.smul_def, map_add, map_zsmul, cancelTerm_on_pure, extendPure_d]
    rfl)).symm

private theorem cancelIso_inverse_on_pure {i j n : ℤ} (h : i + j = n)
    (x : E.X i) (y : P.X j) :
    (cancelIso d f E P).inv.f n (pure ((U).obj E) P h x y) =
      pure E ((L).obj P) h x (extendPure d f P j 1 y) :=
  cancelTerm_on_pure d f E P h x y

private theorem cancelIso_on_pure {i j n : ℤ} (h : i + j = n)
    (x : E.X i) (s : S) (y : P.X j) :
    (cancelIso d f E P).hom.f n (pure E ((L).obj P) h x (extendPure d f P j s y)) =
      pure ((U).obj E) P h (show ((U).obj E).X i from s • x) y := by
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (cancelIso d f E P).inv_hom_id n)
    (pure ((U).obj E) P h (show ((U).obj E).X i from s • x) y)
  change (cancelIso d f E P).hom.f n ((cancelIso d f E P).inv.f n
    (pure ((U).obj E) P h (show ((U).obj E).X i from s • x) y)) = _ at hh
  rw [cancelIso_inverse_on_pure] at hh
  have hb : pure E ((L).obj P) h (s • x) (extendPure d f P j 1 y) =
      pure E ((L).obj P) h x (extendPure d f P j s y) := by
    unfold Specs.DerivedFormalization.CochainTensor.pure
    apply congrArg (ι E ((L).obj P) i j n h)
    rw [TensorProduct.smul_tmul, extendPure_smul, mul_one]
  rw [hb] at hh
  exact hh

end Cancellation

theorem modelStability_conditional.{ru,su,au}
    (_ : adequateModelType.{ru,au}) (_ : closedAdjunctionType.{ru,au})
    (_ : curryingType.{ru,au}) (_ : ringComparisonType.{ru,au}) :
    modelStabilityType.{ru,su,au} := by
  intro R S B _ _ _ d f
  let acyclic (E : compValue.{au} S) :
      ((restriction d f).obj E).Acyclic ↔ E.Acyclic :=
    ScalarExtensionModels.restrict_acyclic_iff f E
  refine ⟨{
    cancel := cancelIso d f
    cancel_on_pure := by intro E P i j n h x s y; exact cancelIso_on_pure d f E P h x s y
    cancel_natural := ?_
    homIso := signedHomIso d f
    hom_on_eval := by intro P E q i j h k x; exact signedHom_on_eval d f P E h k x
    hom_inverse_on_eval := by intro P E q i j h k x s; exact signedHom_inverse_on_eval d f P E h k x s
    hom_natural := ?_
    acyclic_iff := acyclic
    preserves_kFlat := ?_
    preserves_kProjective := ?_ }⟩
  · intro E E' P P' b p
    have he : (cancelIso d f E P).inv ≫
        (restriction d f).map (CochainTensor.map b ((extension d f).map p)) =
        CochainTensor.map ((restriction d f).map b) p ≫ (cancelIso d f E' P').inv := by
      apply CochainTensor.hom_ext
      intro i j n h x y
      change (CochainTensor.map b ((extension d f).map p)).f n
          ((cancelIso d f E P).inv.f n (CochainTensor.pure _ _ h x y)) =
        (cancelIso d f E' P').inv.f n
          ((CochainTensor.map ((restriction d f).map b) p).f n (CochainTensor.pure _ _ h x y))
      rw [cancelIso_inverse_on_pure, CochainTensor.map_on_pure, CochainTensor.map_on_pure,
        extendPure_map, cancelIso_inverse_on_pure]
      rfl
    calc
      _ = (cancelIso d f E P).hom ≫ ((cancelIso d f E P).inv ≫
          (restriction d f).map (CochainTensor.map b ((extension d f).map p))) ≫
            (cancelIso d f E' P').hom := by simp
      _ = _ := by rw [he]; simp
  · intro P P' E E' p b
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply Cochain.ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((signedHomIso d f P' E').hom.f q
        ((internalHomMapValue ((extension d f).map p) b).f q k)).v i j h x =
      ((internalHomMapValue p ((restriction d f).map b)).f q
        ((signedHomIso d f P E).hom.f q k)).v i j h x
    rw [signedHom_on_eval]
    change (((Cochain.ofHom ((extension d f).map p)).comp k (zero_add q)).comp
      (Cochain.ofHom b) (add_zero q)).v i j h (extendPure d f P' i 1 x) =
      (((Cochain.ofHom p).comp ((signedHomIso d f P E).hom.f q k) (zero_add q)).comp
        (Cochain.ofHom ((restriction d f).map b)) (add_zero q)).v i j h x
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      ConcreteCategory.comp_apply, extendPure_map, signedHom_on_eval]
    rfl
  · intro P hP E hE
    apply (acyclic _).1
    have h := hP ((restriction d f).obj E) ((acyclic E).2 hE)
    intro n
    exact (h n).of_iso (cancelIso d f E P).symm
  · intro P hP
    apply (isKProjective_iff_internalHom_acyclic _).2
    intro E hE
    apply (acyclic _).1
    have h := (isKProjective_iff_internalHom_acyclic P).1 hP _ ((acyclic E).2 hE)
    intro n
    exact (h n).of_iso (signedHomIso d f P E).symm

section Diagonal

open Specs.DerivedFormalization.CochainRingTransport
  (complexFunctorValue conjugateValue complexRestrictionIsoValue adjunctionCompatible)

variable {A : Type a} [CommRing A] (e : R ≃+* A)

theorem diagonalExtensionComparison :
    ∃ α : L ⋙ complexFunctorValue d ≅ complexFunctorValue e ⋙ diagonalExtension e d f,
      adjunctionCompatible (extensionAdjunction d f) (diagonalAdjunction e d f)
        α.inv (complexRestrictionIsoValue e d f).hom ∧
      ∀ (X : compValue.{a} R) (i : ℤ) (s : S) (x : X.X i),
      (α.hom.app X).f i (extendPure d f X i s x) =
        (show ((diagonalExtension e d f).obj ((complexFunctorValue e).obj X)).X i from
          d s ⊗ₜ[A,conjugateValue e d f] (show ((complexFunctorValue e).obj X).X i from x)) := by
  obtain ⟨α, _, hp, hu, hc⟩ :=
    CochainRingTransport.representedExtensionMate e d f
  refine ⟨NatIso.mapHomologicalComplex α (.up ℤ), ⟨?_, ?_⟩, ?_⟩
  · intro X
    apply HomologicalComplex.hom_ext
    intro i
    exact hu (X.X i)
  · intro Y
    apply HomologicalComplex.hom_ext
    intro i
    exact hc (Y.X i)
  · intro X i s x
    exact hp (X.X i) s x

end Diagonal

section DiagonalTensor

open Specs.DerivedFormalization.CochainTensor (tensor pure ι cofan)
open Specs.DerivedFormalization.CochainTensorMonoidal (cochainMonoidalValue)

attribute [local instance] cochainMonoidalValue

variable {A : Type a} [CommRing A] (k : A →+* B)

private abbrev diagonalModuleExtension : ModuleCat.{a} A ⥤ ModuleCat.{a} B :=
  ModuleCat.extendScalars k

private abbrev diagonalCochainExtension : compValue.{a} A ⥤ compValue.{a} B :=
  (diagonalModuleExtension k).mapHomologicalComplex (.up ℤ)

local notation "F₀" => diagonalModuleExtension k
local notation "F" => diagonalCochainExtension k

private theorem extendedTensorTerm_hom_ext {X Y : compValue.{a} A} {n : ℤ}
    {N : ModuleCat.{a} B} {b b' : (F₀).obj ((tensor X Y).X n) ⟶ N}
    (h : ∀ i j (h : i + j = n) (x : X.X i) (y : Y.X j),
      b ((1 : B) ⊗ₜ[A,k] pure X Y h x y) = b' ((1 : B) ⊗ₜ[A,k] pure X Y h x y)) :
    b = b' := by
  apply ((ModuleCat.extendRestrictScalarsAdj.{a} k).homEquiv _ _).injective
  apply CochainTensor.term_hom_ext
  intro i j hij x y
  exact h i j hij x y

variable (X Y : compValue.{a} A)

private def diagonallyExtendedSummands (n : ℤ) :
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ModuleCat.of A (X.X p.1.1 ⊗[A] Y.X p.1.2)) ⋙ F₀ ≅
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ModuleCat.of B (((F).obj X).X p.1.1 ⊗[B] ((F).obj Y).X p.1.2)) :=
  Discrete.natIso fun p => (Functor.Monoidal.μIso (F₀) (X.X p.as.1.1) (Y.X p.as.1.2)).symm

private def diagonalTensorTerm (n : ℤ) :
    ((F).obj (tensor X Y)).X n ≅ (tensor ((F).obj X) ((F).obj Y)).X n :=
  (isColimitOfPreserves (F₀) (CochainTensor.tensorCofanIsColimit X Y n)).coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv (diagonallyExtendedSummands k X Y n) _).symm
      (CochainTensor.tensorCofanIsColimit ((F).obj X) ((F).obj Y) n))

private theorem diagonalTensorTerm_on_one {i j n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (diagonalTensorTerm k X Y n).hom ((1 : B) ⊗ₜ[A,k] pure X Y h x y) =
      pure ((F).obj X) ((F).obj Y) h ((1 : B) ⊗ₜ[A,k] x) ((1 : B) ⊗ₜ[A,k] y) := by
  have he := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves (F₀) (CochainTensor.tensorCofanIsColimit X Y n))
    ((IsColimit.precomposeHomEquiv (diagonallyExtendedSummands k X Y n) _).symm
      (CochainTensor.tensorCofanIsColimit ((F).obj X) ((F).obj Y) n))
    (Discrete.mk ⟨(i, j), h⟩)
  have hh := ConcreteCategory.congr_hom he
    ((1 : B) ⊗ₜ[A,k] (x ⊗ₜ[A] y))
  change (diagonalTensorTerm k X Y n).hom ((1 : B) ⊗ₜ[A,k] pure X Y h x y) =
    ι ((F).obj X) ((F).obj Y) i j n h
      (Functor.OplaxMonoidal.δ (F₀) (X.X i) (Y.X j) ((1 : B) ⊗ₜ[A,k] (x ⊗ₜ[A] y))) at hh
  exact hh

/-- The diagonal cochain tensor comparison in the direction of the left adjoint's
oplax structure. -/
def diagonalTensorIso :
    (F).obj (tensor X Y) ≅ tensor ((F).obj X) ((F).obj Y) := by
  refine HomologicalComplex.Hom.isoOfComponents (diagonalTensorTerm k X Y) ?_
  intro n m hnm
  have hs : n + 1 = m := hnm
  subst m
  apply extendedTensorTerm_hom_ext k
  intro i j h x y
  change (tensor ((F).obj X) ((F).obj Y)).d n (n + 1)
      ((diagonalTensorTerm k X Y n).hom ((1 : B) ⊗ₜ[A,k] pure X Y h x y)) =
    (diagonalTensorTerm k X Y (n + 1)).hom
      ((1 : B) ⊗ₜ[A,k] (tensor X Y).d n (n + 1) (pure X Y h x y))
  rw [diagonalTensorTerm_on_one, CochainTensor.differential, CochainTensor.differential]
  let b := (ModuleCat.restrictScalars k).obj (ModuleCat.of B B)
  have hz (v : (tensor X Y).X (n + 1)) :
      ((1 : B) ⊗ₜ[A,k] ((i.negOnePow : ℤ) • v)) =
      (i.negOnePow : ℤ) • ((1 : B) ⊗ₜ[A,k] v) :=
    map_zsmul (TensorProduct.mk A b ((tensor X Y).X (n + 1)) (show b from (1 : B))) _ v
  simp only [Units.smul_def, TensorProduct.tmul_add, hz, map_add, map_zsmul]
  rw [diagonalTensorTerm_on_one k X Y (by omega : i + 1 + j = n + 1),
    diagonalTensorTerm_on_one k X Y (by omega : i + (j + 1) = n + 1)]
  rfl

theorem diagonalTensorIso_on_one {i j n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (diagonalTensorIso k X Y).hom.f n ((1 : B) ⊗ₜ[A,k] pure X Y h x y) =
      pure ((F).obj X) ((F).obj Y) h ((1 : B) ⊗ₜ[A,k] x) ((1 : B) ⊗ₜ[A,k] y) :=
  diagonalTensorTerm_on_one k X Y h x y

open Specs.DerivedFormalization.CochainTensorMonoidal (tensorUnitValue tensorUnitZeroValue)
open HomologicalComplex (single singleMapHomologicalComplex)
open private left_triple_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorMonoidal

private def diagonalUnitIso : (F).obj (tensorUnitValue A) ≅ tensorUnitValue B :=
  (singleMapHomologicalComplex (F₀) (.up ℤ) 0).app (ModuleCat.of A A) ≪≫
    (single (ModuleCat.{a} B) (.up ℤ) 0).mapIso (Functor.Monoidal.εIso (F₀)).symm

private theorem diagonalUnitIso_on_one :
    (diagonalUnitIso k).hom.f 0 ((1 : B) ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A)) =
      (tensorUnitZeroValue B).inv (1 : B) := by
  simp only [diagonalUnitIso, Iso.trans_hom, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  change ((tensorUnitZeroValue B).inv) (Functor.OplaxMonoidal.η (F₀)
    ((F₀).map (tensorUnitZeroValue A).hom ((1 : B) ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A)))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, Iso.inv_hom_id_apply]
  congr 1
  let := k.toAlgebra
  change (TensorProduct.AlgebraTensorModule.rid A B B) ((1 : B) ⊗ₜ[A] (1 : A)) = 1
  rw [TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]

private theorem leftUnitor_inv_on_element {K : Type a} [CommRing K]
    (X : compValue.{a} K) (i : ℤ) (x : X.X i) :
    (λ_ X).inv.f i x = pure (tensorUnitValue K) X (zero_add i) ((tensorUnitZeroValue K).inv (1 : K)) x := by
  have he := DerivedFormalization.cochainTensorLeftUnitor_apply X i (1 : K) x
  rw [one_smul] at he
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (λ_ X).hom_inv_id i)
    (pure (tensorUnitValue K) X (zero_add i) ((tensorUnitZeroValue K).inv (1 : K)) x)
  change (λ_ X).inv.f i ((λ_ X).hom.f i _) = _ at hh
  change _ = _ at hh
  convert hh using 1
  · exact congrArg ((λ_ X).inv.f i) he.symm
  · rfl

private theorem rightUnitor_inv_on_element {K : Type a} [CommRing K]
    (X : compValue.{a} K) (i : ℤ) (x : X.X i) :
    (ρ_ X).inv.f i x = pure X (tensorUnitValue K) (add_zero i) x ((tensorUnitZeroValue K).inv (1 : K)) := by
  have he := DerivedFormalization.cochainTensorRightUnitor_apply X i x (1 : K)
  rw [one_smul] at he
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (ρ_ X).hom_inv_id i)
    (pure X (tensorUnitValue K) (add_zero i) x ((tensorUnitZeroValue K).inv (1 : K)))
  change (ρ_ X).inv.f i ((ρ_ X).hom.f i _) = _ at hh
  change _ = _ at hh
  convert hh using 1
  · exact congrArg ((ρ_ X).inv.f i) he.symm
  · rfl

private theorem diagonalTensorMap_on_pure {K : Type a} [CommRing K]
    {X X' Y Y' : compValue.{a} K} (p : X ⟶ X') (q : Y ⟶ Y')
    {i j n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (p ⊗ₘ q).f n (pure X Y h x y) = pure X' Y' h (p.f i x) (q.f j y) :=
  CochainTensor.map_on_pure p q i j n h x y

private theorem diagonalExtension_map_on_pure {X Y : compValue.{a} A} (p : X ⟶ Y)
    (i : ℤ) (s : B) (x : X.X i) :
    ((F).map p).f i (s ⊗ₜ[A,k] x) = s ⊗ₜ[A,k] p.f i x :=
  rfl

private theorem extendedTensor_hom_ext {X Y : compValue.{a} A}
    {Z : compValue.{a} B} {p q : (F).obj (tensor X Y) ⟶ Z}
    (h : ∀ i j n (h : i + j = n) (x : X.X i) (y : Y.X j),
      p.f n ((1 : B) ⊗ₜ[A,k] pure X Y h x y) =
      q.f n ((1 : B) ⊗ₜ[A,k] pure X Y h x y)) :
    p = q := by
  apply HomologicalComplex.hom_ext
  intro n
  exact extendedTensorTerm_hom_ext k fun i j hij x y => h i j n hij x y

private theorem extendedTriple_hom_ext {X Y Z : compValue.{a} A}
    {W : compValue.{a} B} {p q : (F).obj (tensor (tensor X Y) Z) ⟶ W}
    (h : ∀ i j l n (h : i + j + l = n) (x : X.X i) (y : Y.X j) (z : Z.X l),
      p.f n ((1 : B) ⊗ₜ[A,k] pure (tensor X Y) Z h (pure X Y rfl x y) z) =
      q.f n ((1 : B) ⊗ₜ[A,k] pure (tensor X Y) Z h (pure X Y rfl x y) z)) :
    p = q := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ((ModuleCat.extendRestrictScalarsAdj.{a} k).homEquiv _ _).injective
  apply left_triple_ext
  intro i j l hij x y z
  exact h i j l n hij x y z

private def diagonalCoreMonoidal : (F).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (diagonalUnitIso k).symm
    (fun X Y => (diagonalTensorIso k X Y).symm)
    (μIso_inv_natural_left := by
      intro X Y p Z
      apply extendedTensor_hom_ext k
      intro i j n h x y
      simp only [Iso.symm_inv]
      rw [← tensorHom_id, ← tensorHom_id]
      change (CochainTensor.map ((F).map p) (𝟙 ((F).obj Z))).f n
          ((diagonalTensorIso k X Z).hom.f n ((1 : B) ⊗ₜ[A,k] pure X Z h x y)) =
        (diagonalTensorIso k Y Z).hom.f n
          ((1 : B) ⊗ₜ[A,k] (CochainTensor.map p (𝟙 Z)).f n (pure X Z h x y))
      rw [diagonalTensorIso_on_one, CochainTensor.map_on_pure, CochainTensor.map_on_pure]
      simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply]
      rw [diagonalExtension_map_on_pure, diagonalTensorIso_on_one])
    (μIso_inv_natural_right := by
      intro X Y Z p
      apply extendedTensor_hom_ext k
      intro i j n h x y
      simp only [Iso.symm_inv]
      rw [← id_tensorHom, ← id_tensorHom]
      change (CochainTensor.map (𝟙 ((F).obj Z)) ((F).map p)).f n
          ((diagonalTensorIso k Z X).hom.f n ((1 : B) ⊗ₜ[A,k] pure Z X h x y)) =
        (diagonalTensorIso k Z Y).hom.f n
          ((1 : B) ⊗ₜ[A,k] (CochainTensor.map (𝟙 Z) p).f n (pure Z X h x y))
      rw [diagonalTensorIso_on_one, CochainTensor.map_on_pure, CochainTensor.map_on_pure]
      simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply]
      rw [diagonalExtension_map_on_pure, diagonalTensorIso_on_one])
    (oplax_associativity := by
      intro X Y Z
      apply extendedTriple_hom_ext k
      intro i j l n h x y z
      have h' : i + (j + l) = n := by omega
      simp only [Iso.symm_inv]
      rw [← tensorHom_id, ← id_tensorHom]
      simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
      erw [diagonalTensorIso_on_one k (tensor X Y) Z h,
        diagonalTensorMap_on_pure _ _ h, diagonalTensorIso_on_one k X Y rfl,
        diagonalExtension_map_on_pure k _ n]
      simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply]
      erw [DerivedFormalization.cochainTensorAssociator_apply _ _ _ i j l rfl h rfl h',
        DerivedFormalization.cochainTensorAssociator_apply _ _ _ i j l rfl h rfl h',
        diagonalTensorIso_on_one k X (tensor Y Z) h',
        diagonalTensorMap_on_pure _ _ h', diagonalTensorIso_on_one k Y Z rfl]
      rfl)
    (oplax_left_unitality := by
      intro X
      apply HomologicalComplex.hom_ext
      intro i
      apply ((ModuleCat.extendRestrictScalarsAdj.{a} k).homEquiv (X.X i) _).injective
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (λ_ ((F).obj X)).inv.f i ((1 : B) ⊗ₜ[A,k] x) =
        (CochainTensor.map (diagonalUnitIso k).hom (𝟙 ((F).obj X))).f i
          ((diagonalTensorIso k (tensorUnitValue A) X).hom.f i
            ((1 : B) ⊗ₜ[A,k] (λ_ X).inv.f i x))
      rw [leftUnitor_inv_on_element, leftUnitor_inv_on_element, diagonalTensorIso_on_one,
        CochainTensor.map_on_pure, diagonalUnitIso_on_one]
      rfl)
    (oplax_right_unitality := by
      intro X
      apply HomologicalComplex.hom_ext
      intro i
      apply ((ModuleCat.extendRestrictScalarsAdj.{a} k).homEquiv (X.X i) _).injective
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (ρ_ ((F).obj X)).inv.f i ((1 : B) ⊗ₜ[A,k] x) =
        (CochainTensor.map (𝟙 ((F).obj X)) (diagonalUnitIso k).hom).f i
          ((diagonalTensorIso k X (tensorUnitValue A)).hom.f i
            ((1 : B) ⊗ₜ[A,k] (ρ_ X).inv.f i x))
      rw [rightUnitor_inv_on_element, rightUnitor_inv_on_element, diagonalTensorIso_on_one,
        CochainTensor.map_on_pure, diagonalUnitIso_on_one]
      rfl)



open Specs.DerivedFormalization.CochainTensorMonoidal (HasKoszulBraiding)

@[instance_reducible]
private def diagonalBraided
    (sA : SymmetricCategory (compValue.{a} A)) (sB : SymmetricCategory (compValue.{a} B))
    (hA : HasKoszulBraiding sA) (hB : HasKoszulBraiding sB) :
    letI := sA
    letI := sB
    (F).Braided := by
  letI := sA
  letI := sB
  refine { toMonoidal := (diagonalCoreMonoidal k).toMonoidal, braided := ?_ }
  intro X Y
  change (diagonalTensorIso k X Y).inv ≫ (F).map (β_ X Y).hom =
    (β_ ((F).obj X) ((F).obj Y)).hom ≫ (diagonalTensorIso k Y X).inv
  rw [← cancel_epi (diagonalTensorIso k X Y).hom, Iso.hom_inv_id_assoc,
    ← cancel_mono (diagonalTensorIso k Y X).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply extendedTensor_hom_ext k
  intro i j n h x y
  have h' : j + i = n := by omega
  change (diagonalTensorIso k Y X).hom.f n
      ((1 : B) ⊗ₜ[A,k] (β_ X Y).hom.f n (pure X Y h x y)) =
    (β_ ((F).obj X) ((F).obj Y)).hom.f n
      ((diagonalTensorIso k X Y).hom.f n ((1 : B) ⊗ₜ[A,k] pure X Y h x y))
  rw [diagonalTensorIso_on_one]
  rw [show (β_ X Y).hom.f n (pure X Y h x y) =
      (i * j).negOnePow • pure Y X h' y x from hA X Y i j h x y,
    show (β_ ((F).obj X) ((F).obj Y)).hom.f n
      (pure ((F).obj X) ((F).obj Y) h ((1 : B) ⊗ₜ[A,k] x) ((1 : B) ⊗ₜ[A,k] y)) =
      (i * j).negOnePow • pure ((F).obj Y) ((F).obj X) h'
        ((1 : B) ⊗ₜ[A,k] y) ((1 : B) ⊗ₜ[A,k] x) from
        hB ((F).obj X) ((F).obj Y) i j h _ _]
  let b := (ModuleCat.restrictScalars k).obj (ModuleCat.of B B)
  have hz : ((1 : B) ⊗ₜ[A,k] (((i * j).negOnePow : ℤ) • pure Y X h' y x)) =
      ((i * j).negOnePow : ℤ) • ((1 : B) ⊗ₜ[A,k] pure Y X h' y x) :=
    map_zsmul (TensorProduct.mk A b ((tensor Y X).X n) (show b from (1 : B))) _ _
  simp only [Units.smul_def, hz, map_zsmul]
  rw [diagonalTensorIso_on_one]

private theorem diagonalTensorIso_inv_on_pure (X Y : compValue.{a} A) {i j n : ℤ}
    (h : i + j = n) (s t : B) (x : X.X i) (y : Y.X j) :
    (diagonalTensorIso k X Y).inv.f n
      (pure ((F).obj X) ((F).obj Y) h (s ⊗ₜ[A,k] x) (t ⊗ₜ[A,k] y)) =
    (show ((F).obj (tensor X Y)).X n from (s * t) ⊗ₜ[A,k] pure X Y h x y) := by
  have h₁ : s • (show ((F).obj X).X i from (1 : B) ⊗ₜ[A,k] x) =
      (show ((F).obj X).X i from s ⊗ₜ[A,k] x) := by
    simpa only [mul_one] using ModuleCat.ExtendScalars.smul_tmul k s 1 x
  have h₂ : t • (show ((F).obj Y).X j from (1 : B) ⊗ₜ[A,k] y) =
      (show ((F).obj Y).X j from t ⊗ₜ[A,k] y) := by
    simpa only [mul_one] using ModuleCat.ExtendScalars.smul_tmul k t 1 y
  have h₃ : (s * t) • (show ((F).obj (tensor X Y)).X n from (1 : B) ⊗ₜ[A,k] pure X Y h x y) =
      (show ((F).obj (tensor X Y)).X n from (s * t) ⊗ₜ[A,k] pure X Y h x y) := by
    simpa only [mul_one] using ModuleCat.ExtendScalars.smul_tmul k (s * t) 1 (pure X Y h x y)
  have hh : pure ((F).obj X) ((F).obj Y) h
      (s • (show ((F).obj X).X i from (1 : B) ⊗ₜ[A,k] x))
      (t • (show ((F).obj Y).X j from (1 : B) ⊗ₜ[A,k] y)) =
      (s * t) • pure ((F).obj X) ((F).obj Y) h ((1 : B) ⊗ₜ[A,k] x) ((1 : B) ⊗ₜ[A,k] y) := by
    unfold Specs.DerivedFormalization.CochainTensor.pure
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← smul_smul, map_smul, map_smul]
  have he := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (diagonalTensorIso k X Y).hom_inv_id n) ((1 : B) ⊗ₜ[A,k] pure X Y h x y)
  have hb : (diagonalTensorIso k X Y).inv.f n
      (pure ((F).obj X) ((F).obj Y) h ((1 : B) ⊗ₜ[A,k] x) ((1 : B) ⊗ₜ[A,k] y)) =
      (show ((F).obj (tensor X Y)).X n from (1 : B) ⊗ₜ[A,k] pure X Y h x y) :=
    (congrArg ((diagonalTensorIso k X Y).inv.f n) (diagonalTensorIso_on_one k X Y h x y)).symm.trans he
  calc
    _ = (diagonalTensorIso k X Y).inv.f n (pure ((F).obj X) ((F).obj Y) h
        (s • (show ((F).obj X).X i from (1 : B) ⊗ₜ[A,k] x))
        (t • (show ((F).obj Y).X j from (1 : B) ⊗ₜ[A,k] y))) :=
      congrArg ((diagonalTensorIso k X Y).inv.f n)
        (congrArg₂ (pure ((F).obj X) ((F).obj Y) h) h₁.symm h₂.symm)
    _ = _ := by rw [hh, map_smul, hb, h₃]

private theorem diagonalUnitIso_inv_on_pure (b : B) :
    (diagonalUnitIso k).inv.f 0 ((tensorUnitZeroValue B).inv b) =
    (show ((F).obj (tensorUnitValue A)).X 0 from
      b ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A)) := by
  have hh : b • (show ((F).obj (tensorUnitValue A)).X 0 from
      (1 : B) ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A)) =
      (show ((F).obj (tensorUnitValue A)).X 0 from
        b ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A)) := by
    simpa only [mul_one] using
      ModuleCat.ExtendScalars.smul_tmul k b 1 ((tensorUnitZeroValue A).inv (1 : A))
  have he := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (diagonalUnitIso k).hom_inv_id 0)
    ((1 : B) ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A))
  change (diagonalUnitIso k).inv.f 0
      ((diagonalUnitIso k).hom.f 0 ((1 : B) ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A))) =
    (show ((F).obj (tensorUnitValue A)).X 0 from
      (1 : B) ⊗ₜ[A,k] (tensorUnitZeroValue A).inv (1 : A)) at he
  rw [diagonalUnitIso_on_one] at he
  calc
    _ = (diagonalUnitIso k).inv.f 0 (b • (tensorUnitZeroValue B).inv (1 : B)) := by
      rw [← map_smul]
      exact congrArg (fun s : B => (diagonalUnitIso k).inv.f 0 ((tensorUnitZeroValue B).inv s))
        (mul_one b).symm
    _ = _ := by rw [map_smul, he, hh]


end DiagonalTensor

section MonoidalTransport

open Functor.LaxMonoidal

variable {C₀ D₀ D₁ : Type*} [Category* C₀] [Category* D₀] [Category* D₁]
  [MonoidalCategory C₀] [MonoidalCategory D₀] [MonoidalCategory D₁]
  [BraidedCategory C₀] [BraidedCategory D₀] [BraidedCategory D₁]

set_option linter.style.haveILetI false in
private theorem braidedOfPostcompEquivalence
    (H : D₀ ≌ D₁) [H.functor.Braided] {P : C₀ ⥤ D₀} {Q : C₀ ⥤ D₁}
    [Q.Braided] (α : P ⋙ H.functor ≅ Q) :
    ∃ m : P.Braided, letI := m; NatTrans.IsMonoidal α.hom := by
  letI := H.inverseMonoidal
  haveI : H.IsMonoidal := inferInstance
  let i : P ≅ Q ⋙ H.inverse :=
    P.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft P H.unitIso ≪≫
      (Functor.associator P H.functor H.inverse).symm ≪≫ Functor.isoWhiskerRight α H.inverse
  let m₀ : P.Monoidal := Functor.Monoidal.transport i.symm
  letI := m₀
  haveI : NatTrans.IsMonoidal i.symm.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport i.symm
  haveI : NatTrans.IsMonoidal i.hom := inferInstanceAs (NatTrans.IsMonoidal i.symm.inv)
  haveI : NatTrans.IsMonoidal H.counitIso.hom := inferInstanceAs (NatTrans.IsMonoidal H.counit)
  let θ : P ⋙ H.functor ≅ Q :=
    Functor.isoWhiskerRight i H.functor ≪≫ Functor.associator Q H.inverse H.functor ≪≫
      Functor.isoWhiskerLeft Q H.counitIso ≪≫ Q.rightUnitor
  haveI hθ : NatTrans.IsMonoidal θ.hom := by
    change NatTrans.IsMonoidal (Functor.whiskerRight i.hom H.functor ≫
      (Functor.associator Q H.inverse H.functor).hom ≫
      Functor.whiskerLeft Q H.counitIso.hom ≫ Q.rightUnitor.hom)
    infer_instance
  have hα : θ.hom = α.hom := by
    apply NatTrans.ext
    funext X
    simp only [θ, i, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp,
      Functor.map_comp, Category.assoc]
    have hn := H.counitIso.hom.naturality (α.hom.app X)
    change H.functor.map (H.inverse.map (α.hom.app X)) ≫ H.counitIso.hom.app (Q.obj X) =
      H.counitIso.hom.app (H.functor.obj (P.obj X)) ≫ α.hom.app X at hn
    change H.functor.map (H.unitIso.hom.app (P.obj X)) ≫
      H.functor.map (H.inverse.map (α.hom.app X)) ≫
      (H.counitIso.hom.app (Q.obj X) ≫ 𝟙 (Q.obj X)) = α.hom.app X
    calc
      _ = H.functor.map (H.unitIso.hom.app (P.obj X)) ≫
          H.functor.map (H.inverse.map (α.hom.app X)) ≫ H.counitIso.hom.app (Q.obj X) :=
        congrArg (fun z => H.functor.map (H.unitIso.hom.app (P.obj X)) ≫
          H.functor.map (H.inverse.map (α.hom.app X)) ≫ z)
          (Category.comp_id (H.counitIso.hom.app (Q.obj X)))
      _ = _ := (congrArg (fun z => H.functor.map (H.unitIso.hom.app (P.obj X)) ≫ z) hn).trans
        (H.functor_unit_comp_assoc _ _)
  haveI : NatTrans.IsMonoidal α.hom := hα ▸ hθ
  haveI : NatTrans.IsMonoidal α.symm.hom := inferInstanceAs (NatTrans.IsMonoidal α.inv)
  letI : (P ⋙ H.functor).LaxBraided := Functor.LaxBraided.ofNatIso α.symm
  let m : P.Braided :=
    { toMonoidal := m₀
      braided := by
        intro X Y
        apply H.functor.map_injective
        rw [Functor.map_comp, Functor.map_comp, Functor.map_braiding H.functor (P.obj X) (P.obj Y)]
        apply (cancel_epi (μ H.functor (P.obj X) (P.obj Y))).mp
        simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
        simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map, Category.assoc]
          using (Functor.LaxBraided.braided (F := P ⋙ H.functor) X Y) }
  exact ⟨m, hα ▸ hθ⟩

end MonoidalTransport

section MonoidalSquares

open Functor.LaxMonoidal (ε μ)

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  {P : C₁ ⥤ D₁} {H : D₁ ⥤ D₂} {K : C₁ ⥤ C₂} {Q : C₂ ⥤ D₂}
  [P.LaxMonoidal] [H.LaxMonoidal] [K.LaxMonoidal] [Q.LaxMonoidal]
  (α : P ⋙ H ≅ K ⋙ Q) [NatTrans.IsMonoidal α.hom]

private theorem tensorator_square (X Y : C₁) {M : C₁} {N : D₁}
    (p : M ≅ X ⊗ Y) (q : N ≅ P.obj X ⊗ P.obj Y)
    (s : K.obj X ⊗ K.obj Y ≅ K.obj M) (t : H.obj (P.obj X) ⊗ H.obj (P.obj Y) ≅ H.obj N)
    (hp : μ K X Y = s.hom ≫ K.map p.hom)
    (hq : μ H (P.obj X) (P.obj Y) = t.hom ≫ H.map q.hom) :
    t.hom ≫ H.map (q.hom ≫ μ P X Y ≫ P.map p.inv) ≫ α.hom.app M =
    (α.hom.app X ⊗ₘ α.hom.app Y) ≫ μ Q (K.obj X) (K.obj Y) ≫ Q.map s.hom := by
  calc
    _ = μ (P ⋙ H) X Y ≫ (P ⋙ H).map p.inv ≫ α.hom.app M := by
      simp only [Functor.map_comp, Functor.comp_map, Category.assoc, Functor.LaxMonoidal.comp_μ, hq,
        Functor.comp_obj]
    _ = μ (P ⋙ H) X Y ≫ α.hom.app (X ⊗ Y) ≫ (K ⋙ Q).map p.inv := by
      rw [α.hom.naturality]
    _ = _ := by
      rw [NatTrans.IsMonoidal.tensor_assoc]
      simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map, hp,
        Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]

private theorem unitator_square {M : C₁} {N : D₁}
    (p : M ≅ 𝟙_ C₁) (q : N ≅ 𝟙_ D₁)
    (s : 𝟙_ C₂ ≅ K.obj M) (t : 𝟙_ D₂ ≅ H.obj N)
    (hp : ε K = s.hom ≫ K.map p.hom)
    (hq : ε H = t.hom ≫ H.map q.hom) :
    t.hom ≫ H.map (q.hom ≫ ε P ≫ P.map p.inv) ≫ α.hom.app M =
    ε Q ≫ Q.map s.hom := by
  calc
    _ = ε (P ⋙ H) ≫ (P ⋙ H).map p.inv ≫ α.hom.app M := by
      simp only [Functor.map_comp, Functor.comp_map, Category.assoc, Functor.LaxMonoidal.comp_ε, hq]
    _ = ε (P ⋙ H) ≫ α.hom.app (𝟙_ C₁) ≫ (K ⋙ Q).map p.inv := by
      rw [α.hom.naturality]
    _ = _ := by
      rw [NatTrans.IsMonoidal.unit_assoc]
      simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_map, hp,
        Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]

end MonoidalSquares

section RepresentedUnit

open Specs.DerivedFormalization.CochainTensorMonoidal (tensorUnitValue tensorUnitZeroValue)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit representedUnitZero)
open Specs.DerivedFormalization.CochainRingTransport
  (complexFunctorValue rankOneValue rankOneComparisonValue moduleEquivalenceValue)

variable {A : Type a} [CommRing A] (e : R ≃+* A)

private theorem rankOneComparison_on_element (b : A) :
    (rankOneComparisonValue e).hom.f 0 ((representedUnitZero e).inv b) =
      (tensorUnitZeroValue A).inv b := by
  simp only [rankOneComparisonValue, Iso.trans_hom, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  change (tensorUnitZeroValue A).inv _ = _
  rfl

private theorem rankOneComparison_inverse_on_element (b : A) :
    (rankOneComparisonValue e).inv.f 0 ((tensorUnitZeroValue A).inv b) =
      (representedUnitZero e).inv b :=
  (congrArg ((rankOneComparisonValue e).inv.f 0) (rankOneComparison_on_element e b)).symm.trans
    (ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (rankOneComparisonValue e).hom_inv_id 0)
      ((representedUnitZero e).inv b))

end RepresentedUnit

section OriginalMonoidal

open Specs.DerivedFormalization.CochainTensor (tensor pure map)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel representedUnit representedUnitZero)
open Specs.DerivedFormalization.CochainTensorMonoidal
  (cochainMonoidalValue tensorUnitValue tensorUnitZeroValue)
open Specs.DerivedFormalization.CochainRingTransport
  (complexFunctorValue complexEquivalenceValue conjugateValue rankOneComparisonValue)
open Functor.LaxMonoidal (ε μ)
open Functor.OplaxMonoidal (δ η)

attribute [local instance] cochainMonoidalValue

private theorem adjunction_on_element (X : compValue.{a} R) (Y : compValue.{a} S)
    (p : ((L).obj X) ⟶ Y) (i : ℤ) (x : X.X i) :
    ((extensionAdjunction d f).homEquiv X Y p).f i x = p.f i (extendPure d f X i 1 x) := by
  rw [Adjunction.homEquiv_unit]
  change p.f i (((extensionAdjunction d f).unit.app X).f i x) = _
  rw [unit_apply]

private theorem counit_on_one (X : compValue.{a} S) (i : ℤ) (x : X.X i) :
    ((extensionAdjunction d f).counit.app X).f i
      (extendPure d f ((U).obj X) i 1 (show ((U).obj X).X i from x)) = x := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    ((extensionAdjunction d f).right_triangle_components X) i) (show ((U).obj X).X i from x)
  change ((extensionAdjunction d f).counit.app X).f i
    (((extensionAdjunction d f).unit.app ((U).obj X)).f i x) = x at h
  rw [unit_apply] at h
  exact h

private theorem representedUnitElement {A : Type a} [CommRing A] (e : R ≃+* A) (r : A) :
    (representedUnitZero e).inv r = e.symm r • (representedUnitZero e).inv (1 : A) := by
  rw [← map_smul]
  apply congrArg (representedUnitZero e).inv
  change r = e (e.symm r) * 1
  rw [RingEquiv.apply_symm_apply, mul_one]

set_option linter.style.haveILetI false in
theorem monoidalComparison_conditional.{ru,su,au}
    (_ : adequateModelType.{ru,au}) (_ : closedAdjunctionType.{ru,au})
    (_ : curryingType.{ru,au}) (_ : ringComparisonType.{ru,au}) :
    monoidalComparisonType.{ru,su,au} := by
  intro R S A B _ _ _ _ e d f MR MS
  letI := MR.chainMonoidal
  letI := MS.chainMonoidal
  letI := MR.chainSymmetric
  letI := MS.chainSymmetric
  letI := MR.nativeSymmetric
  letI := MS.nativeSymmetric
  letI := MR.chainTransport
  letI : (complexFunctorValue d).Braided := MS.chainTransport
  letI : (complexEquivalenceValue d).functor.Braided := MS.chainTransport
  let k := conjugateValue e d f
  let FN := diagonalExtension e d f
  let FR := complexFunctorValue e
  let FS := complexFunctorValue d
  let L₀ := extension d f
  let U₀ := restriction d f
  let j := extensionAdjunction d f
  let bN : FN.Braided := diagonalBraided k MR.nativeSymmetric MS.nativeSymmetric
    MR.nativeKoszul MS.nativeKoszul
  letI := bN
  obtain ⟨α, hAdj, hPure⟩ := diagonalExtensionComparison (e := e) (d := d) (f := f)
  obtain ⟨bL, hα⟩ := braidedOfPostcompEquivalence (complexEquivalenceValue d) α
  letI := bL
  haveI : NatTrans.IsMonoidal α.hom := hα
  let lU : U₀.LaxMonoidal := j.rightAdjointLaxMonoidal
  letI := lU
  let t (X Y : compValue.{au} R) :=
    MS.tensorModel (L₀.obj X) (L₀.obj Y) ≪≫ Functor.Monoidal.μIso L₀ X Y ≪≫
      L₀.mapIso (MR.tensorModel X Y).symm
  let v := MS.unitModel ≪≫ Functor.Monoidal.εIso L₀ ≪≫ L₀.mapIso MR.unitModel.symm
  have pt (X Y : compValue.{au} R) {i j n : ℤ} (h : i + j = n)
      (s u : S) (x : X.X i) (y : Y.X j) :
      (t X Y).hom.f n (pure (L₀.obj X) (L₀.obj Y) h (extendPure d f X i s x) (extendPure d f Y j u y)) =
        extendPure d f (tensor X Y) n (s * u) (pure X Y h x y) := by
    have hsq := tensorator_square α X Y (MR.tensorModel X Y)
      (MS.tensorModel (L₀.obj X) (L₀.obj Y)) (MR.tensorIso X Y) (MS.tensorIso (L₀.obj X) (L₀.obj Y))
      (MR.tensorModel_transport X Y) (MS.tensorModel_transport (L₀.obj X) (L₀.obj Y))
    let xs : (L₀.obj X).X i := extendPure d f X i s x
    let yu : (L₀.obj Y).X j := extendPure d f Y j u y
    have hf := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hsq n)
      (pure (FS.obj (L₀.obj X)) (FS.obj (L₀.obj Y)) h xs yu)
    change (α.hom.app (tensor X Y)).f n
        ((t X Y).hom.f n ((MS.tensorIso (L₀.obj X) (L₀.obj Y)).hom.f n
          (pure (FS.obj (L₀.obj X)) (FS.obj (L₀.obj Y)) h xs yu))) =
      (FN.map (MR.tensorIso X Y).hom).f n
        ((μ FN (FR.obj X) (FR.obj Y)).f n
          ((α.hom.app X ⊗ₘ α.hom.app Y).f n
            (pure (FS.obj (L₀.obj X)) (FS.obj (L₀.obj Y)) h xs yu))) at hf
    change (α.hom.app (tensor X Y)).f n
        ((t X Y).hom.f n ((MS.tensorIso (L₀.obj X) (L₀.obj Y)).hom.f n
          (pure (FS.obj (L₀.obj X)) (FS.obj (L₀.obj Y)) h xs yu))) =
      (FN.map (MR.tensorIso X Y).hom).f n
        ((μ FN (FR.obj X) (FR.obj Y)).f n
          ((map (α.hom.app X) (α.hom.app Y)).f n
            (pure (FS.obj (L₀.obj X)) (FS.obj (L₀.obj Y)) h xs yu))) at hf
    rw [MS.tensor_on_pure] at hf
    have hm := CochainTensor.map_on_pure (α.hom.app X) (α.hom.app Y) i j n h
      (show ((L₀ ⋙ FS).obj X).X i from xs) (show ((L₀ ⋙ FS).obj Y).X j from yu)
    erw [hm] at hf
    change (α.hom.app (tensor X Y)).f n ((t X Y).hom.f n (pure (L₀.obj X) (L₀.obj Y) h xs yu)) =
      (FN.map (MR.tensorIso X Y).hom).f n
        ((μ FN (FR.obj X) (FR.obj Y)).f n
          (pure (FN.obj (FR.obj X)) (FN.obj (FR.obj Y)) h
            ((α.hom.app X).f i xs) ((α.hom.app Y).f j yu))) at hf
    dsimp only [xs, yu] at hf
    rw [hPure, hPure] at hf
    have hNative := diagonalTensorIso_inv_on_pure k (FR.obj X) (FR.obj Y) h (d s) (d u)
      (show (FR.obj X).X i from x) (show (FR.obj Y).X j from y)
    change (μ FN (FR.obj X) (FR.obj Y)).f n
      (pure (FN.obj (FR.obj X)) (FN.obj (FR.obj Y)) h
        (d s ⊗ₜ[A,k] (show (FR.obj X).X i from x))
        (d u ⊗ₜ[A,k] (show (FR.obj Y).X j from y))) =
      (show (FN.obj (tensor (FR.obj X) (FR.obj Y))).X n from (d s * d u) ⊗ₜ[A,k]
        pure (FR.obj X) (FR.obj Y) h x y) at hNative
    rw [hNative] at hf
    change _ = (show (FN.obj (FR.obj (tensor X Y))).X n from
      (d s * d u) ⊗ₜ[A,k] (MR.tensorIso X Y).hom.f n (pure (FR.obj X) (FR.obj Y) h x y)) at hf
    rw [MR.tensor_on_pure] at hf
    apply (ConcreteCategory.bijective_of_isIso ((α.hom.app (tensor X Y)).f n)).1
    rw [hPure]
    exact hf.trans (congrArg (fun b : B => b ⊗ₜ[A,k]
      (show (FR.obj (tensor X Y)).X n from pure X Y h x y)) (d.map_mul s u).symm)
  have pv (b : B) :
      v.hom.f 0 ((representedUnitZero d).inv b) =
        extendPure d f (representedUnit e) 0 (d.symm b) ((representedUnitZero e).inv (1 : A)) := by
    have hsq := unitator_square α MR.unitModel MS.unitModel
      (rankOneComparisonValue e).symm (rankOneComparisonValue d).symm
      MR.unitModel_transport MS.unitModel_transport
    have hf := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hsq 0)
      ((tensorUnitZeroValue B).inv b)
    change (α.hom.app (representedUnit e)).f 0
      (v.hom.f 0 ((rankOneComparisonValue d).inv.f 0 ((tensorUnitZeroValue B).inv b))) =
      (FN.map (rankOneComparisonValue e).inv).f 0
        ((diagonalUnitIso k).inv.f 0 ((tensorUnitZeroValue B).inv b)) at hf
    rw [rankOneComparison_inverse_on_element, diagonalUnitIso_inv_on_pure] at hf
    change _ = (show (FN.obj (FR.obj (representedUnit e))).X 0 from b ⊗ₜ[A,k]
      (rankOneComparisonValue e).inv.f 0 ((tensorUnitZeroValue A).inv (1 : A))) at hf
    rw [rankOneComparison_inverse_on_element] at hf
    apply (ConcreteCategory.bijective_of_isIso ((α.hom.app (representedUnit e)).f 0)).1
    rw [hPure]
    exact hf.trans (congrArg (fun s : B => s ⊗ₜ[A,k] (show (FR.obj (representedUnit e)).X 0 from
      (representedUnitZero e).inv (1 : A))) (d.apply_symm_apply b).symm)
  have prt (X Y : compValue.{au} S) {i l n : ℤ} (h : i + l = n) (x : X.X i) (y : Y.X l) :
      (((MR.tensorModel (U₀.obj X) (U₀.obj Y)).hom ≫ μ U₀ X Y ≫ U₀.map (MS.tensorModel X Y).inv)).f n
        (pure (U₀.obj X) (U₀.obj Y) h x y) = pure X Y h x y := by
    let counit := j.counit
    let p := MR.tensorModel (U₀.obj X) (U₀.obj Y)
    let q := MS.tensorModel X Y
    have hq : (counit.app X ⊗ₘ counit.app Y) ≫ q.inv =
        (MS.tensorModel (L₀.obj (U₀.obj X)) (L₀.obj (U₀.obj Y))).inv ≫ map (counit.app X) (counit.app Y) := by
      apply (cancel_epi (MS.tensorModel (L₀.obj (U₀.obj X)) (L₀.obj (U₀.obj Y))).hom).mp
      rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← MS.tensorModel_natural, Category.assoc]
      change map (counit.app X) (counit.app Y) ≫ q.hom ≫ q.inv = _
      rw [Iso.hom_inv_id, Category.comp_id]
    have hEq : p.hom ≫ μ U₀ X Y ≫ U₀.map q.inv =
        (j.homEquiv _ _) ((t (U₀.obj X) (U₀.obj Y)).inv ≫ map (counit.app X) (counit.app Y)) := by
      change p.hom ≫ (j.homEquiv _ _) (δ L₀ (U₀.obj X) (U₀.obj Y) ≫
          (counit.app X ⊗ₘ counit.app Y)) ≫ U₀.map q.inv = _
      rw [← Category.assoc, ← Adjunction.homEquiv_naturality_left,
        ← Adjunction.homEquiv_naturality_right]
      congr 1
      simp only [t, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Functor.Monoidal.μIso_inv,
        Category.assoc, hq]
      rfl
    change (p.hom ≫ μ U₀ X Y ≫ U₀.map q.inv).f n (pure (U₀.obj X) (U₀.obj Y) h x y) = _
    rw [hEq]
    let I := pure (U₀.obj X) (U₀.obj Y) h x y
    erw [adjunction_on_element d f (tensor (U₀.obj X) (U₀.obj Y)) (tensor X Y)
      ((t (U₀.obj X) (U₀.obj Y)).inv ≫ map (counit.app X) (counit.app Y)) n I]
    let vgen := pure (L₀.obj (U₀.obj X)) (L₀.obj (U₀.obj Y)) h
      (extendPure d f (U₀.obj X) i 1 x) (extendPure d f (U₀.obj Y) l 1 y)
    have hgen : (t (U₀.obj X) (U₀.obj Y)).hom.f n vgen =
        extendPure d f (tensor (U₀.obj X) (U₀.obj Y)) n 1 I := by
      simpa only [one_mul] using pt (U₀.obj X) (U₀.obj Y) h 1 1 x y
    change (map (counit.app X) (counit.app Y)).f n
      ((t (U₀.obj X) (U₀.obj Y)).inv.f n (extendPure d f (tensor (U₀.obj X) (U₀.obj Y)) n 1 I)) = _
    rw [← hgen]
    have hinv := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (t (U₀.obj X) (U₀.obj Y)).hom_inv_id n) vgen
    change (t (U₀.obj X) (U₀.obj Y)).inv.f n ((t (U₀.obj X) (U₀.obj Y)).hom.f n vgen) = vgen at hinv
    rw [hinv]
    exact (CochainTensor.map_on_pure (counit.app X) (counit.app Y) i l n h
      (extendPure d f (U₀.obj X) i 1 x) (extendPure d f (U₀.obj Y) l 1 y)).trans
      (congrArg₂ (pure X Y h) (counit_on_one d f X i x) (counit_on_one d f Y l y))
  have prv (r : A) :
      (MR.unitModel.hom ≫ ε U₀ ≫ U₀.map MS.unitModel.inv).f 0 ((representedUnitZero e).inv r) =
        (representedUnitZero d).inv (k r) := by
    have hEq : MR.unitModel.hom ≫ ε U₀ ≫ U₀.map MS.unitModel.inv = (j.homEquiv _ _) v.inv := by
      change MR.unitModel.hom ≫ (j.homEquiv _ _) (η L₀) ≫ U₀.map MS.unitModel.inv = _
      rw [← Category.assoc, ← Adjunction.homEquiv_naturality_left,
        ← Adjunction.homEquiv_naturality_right]
      rfl
    rw [hEq, adjunction_on_element]
    have hv := pv (k r)
    have hs : extendPure d f (representedUnit e) 0 1 ((representedUnitZero e).inv r) =
        extendPure d f (representedUnit e) 0 (d.symm (k r)) ((representedUnitZero e).inv (1 : A)) := by
      rw [representedUnitElement (e := e) r, extendPure_smul_source, one_mul]
      exact congrArg (fun s : S => extendPure d f (representedUnit e) 0 s
        ((representedUnitZero e).inv (1 : A))) (d.symm_apply_apply (f (e.symm r))).symm
    rw [hs, ← hv]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom v.hom_inv_id 0)
      ((representedUnitZero d).inv (k r))
  let M : MonoidalChange e d f MR MS :=
    { extensionBraided := bL
      restrictionLax := lU
      mates := inferInstance
      tensor_on_pure := fun X Y _ _ _ h s t x y => pt X Y h s t x y
      unit_on_pure := pv
      restrict_tensor_on_pure := fun X Y _ _ _ h x y => prt X Y h x y
      restrict_unit_on_pure := prv }
  exact ⟨M, ⟨{
    nativeBraided := bN
    comparison := α
    comparison_adjunction := hAdj
    comparison_on_pure := hPure
    native_tensor_on_pure := fun X Y _ _ _ h s t x y => diagonalTensorIso_inv_on_pure k X Y h s t x y
    native_unit_on_pure := diagonalUnitIso_inv_on_pure k
    monoidal := hα }⟩⟩

end OriginalMonoidal

section Transitivity

open Specs.DerivedFormalization.CochainRingTransport
  (complexFunctorValue conjugateValue restrictionComp conjugateComp)

variable {A : Type a} [CommRing A] (e : R ≃+* A) (c : T ≃+* C) (g : S →+* T)

private theorem composition_on_one (X : compValue.{a} R) (i : ℤ) (x : X.X i) :
    ((compositionIso d f c g).hom.app X).f i
      (extendPure c g ((L).obj X) i 1 (extendPure d f X i 1 x)) =
    extendPure c (g.comp f) X i 1 x := by
  let β := (Functor.mapHomologicalComplexCompIso (Iso.refl
      (ModuleCat.restrictScalars.{a} g ⋙ ModuleCat.restrictScalars.{a} f)) (.up ℤ)) ≪≫
    NatIso.mapHomologicalComplex (restrictionComp.{a} f g) (.up ℤ)
  let adj := ((extensionAdjunction d f).comp (extensionAdjunction c g)).ofNatIsoRight β
  have he := adj.unit_leftAdjointUniq_hom_app (extensionAdjunction c (g.comp f)) X
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom he i) x
  change ((compositionIso d f c g).hom.app X).f i ((adj.unit.app X).f i x) =
    ((extensionAdjunction c (g.comp f)).unit.app X).f i x at hh
  have hu : (adj.unit.app X).f i x =
      extendPure c g ((L).obj X) i 1 (extendPure d f X i 1 x) := by
    change ((extensionAdjunction c g).unit.app ((L).obj X)).f i
        (((extensionAdjunction d f).unit.app X).f i x) = _
    rw [unit_apply, unit_apply]
  rw [hu, unit_apply] at hh
  exact hh

theorem composition_on_pure (X : compValue.{a} R) (i : ℤ) (s : S) (t : T) (x : X.X i) :
    ((compositionIso d f c g).hom.app X).f i
      (extendPure c g ((L).obj X) i t (extendPure d f X i s x)) =
    extendPure c (g.comp f) X i (t * g s) x := by
  have hs := extendPure_smul d f X i s 1 x
  rw [mul_one] at hs
  rw [← hs, extendPure_smul_source]
  have h₁ := extendPure_smul c g ((L).obj X) i (t * g s) 1 (extendPure d f X i 1 x)
  have h₂ := extendPure_smul c (g.comp f) X i (t * g s) 1 x
  rw [mul_one] at h₁ h₂
  rw [← h₁, ← h₂, map_smul, composition_on_one]

private theorem diagonalComposition_on_one (X : compValue.{a} A) (i : ℤ) (x : X.X i) :
    ((diagonalCompositionIso e d f c g).hom.app X).f i
      ((1 : C) ⊗ₜ[B,conjugateValue d c g] ((1 : B) ⊗ₜ[A,conjugateValue e d f] x)) =
    (show ((diagonalExtension e c (g.comp f)).obj X).X i from
      (1 : C) ⊗ₜ[A,conjugateValue e c (g.comp f)] x) := by
  let β := (Functor.mapHomologicalComplexCompIso (Iso.refl
      (ModuleCat.restrictScalars.{a} (conjugateValue d c g) ⋙
        ModuleCat.restrictScalars.{a} (conjugateValue e d f))) (.up ℤ)) ≪≫
    NatIso.mapHomologicalComplex (conjugateComp e d c f g) (.up ℤ)
  let adj := ((diagonalAdjunction e d f).comp (diagonalAdjunction d c g)).ofNatIsoRight β
  have he := adj.unit_leftAdjointUniq_hom_app (diagonalAdjunction e c (g.comp f)) X
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom he i) x
  exact hh

private theorem doubleExtension_term_hom_ext {X : compValue.{a} R} {i : ℤ}
    {N : ModuleCat.{a} T} {b b' : ((extension c g).obj ((L).obj X)).X i ⟶ N}
    (h : ∀ x : X.X i,
      b (extendPure c g ((L).obj X) i 1 (extendPure d f X i 1 x)) =
      b' (extendPure c g ((L).obj X) i 1 (extendPure d f X i 1 x))) : b = b' := by
  let adj := (representedExtensionAdjunction d f).comp (representedExtensionAdjunction c g)
  apply (adj.homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [Adjunction.homEquiv_unit, ConcreteCategory.comp_apply]
  change b (((extensionAdjunction c g).unit.app ((L).obj X)).f i
    (((extensionAdjunction d f).unit.app X).f i x)) =
    b' (((extensionAdjunction c g).unit.app ((L).obj X)).f i
    (((extensionAdjunction d f).unit.app X).f i x))
  rw [unit_apply, unit_apply]
  exact h x


open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)

theorem composition_respects_diagonal
    {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}
    {F : MonoidalChange e d f MR MS} {G : MonoidalChange d c g MS MT}
    {GF : MonoidalChange e c (g.comp f) MR MT}
    (DF : DiagonalComparison e d f MR MS F) (DG : DiagonalComparison d c g MS MT G)
    (DGF : DiagonalComparison e c (g.comp f) MR MT GF) (X : compValue.{a} R) :
    (complexFunctorValue c).map ((compositionIso d f c g).hom.app X) ≫
      DGF.comparison.hom.app X =
    DG.comparison.hom.app ((L).obj X) ≫
      (diagonalExtension d c g).map (DF.comparison.hom.app X) ≫
      (diagonalCompositionIso e d f c g).hom.app ((complexFunctorValue e).obj X) := by
  apply HomologicalComplex.hom_ext
  intro i
  let K := Specs.DerivedFormalization.CochainRingTransport.moduleEquivalenceValue c
  apply K.inverse.map_injective
  apply (cancel_epi (K.unitIso.hom.app (((extension c g).obj ((L).obj X)).X i))).mp
  apply doubleExtension_term_hom_ext d f c g
  intro x
  let z := extendPure c g ((L).obj X) i 1 (extendPure d f X i 1 x)
  change (DGF.comparison.hom.app X).f i (((compositionIso d f c g).hom.app X).f i z) =
    ((diagonalCompositionIso e d f c g).hom.app ((complexFunctorValue e).obj X)).f i
      (((diagonalExtension d c g).map (DF.comparison.hom.app X)).f i
        ((DG.comparison.hom.app ((L).obj X)).f i z))
  dsimp only [z]
  rw [composition_on_one, DGF.comparison_on_pure, DG.comparison_on_pure, map_one]
  change _ =
    ((diagonalCompositionIso e d f c g).hom.app ((complexFunctorValue e).obj X)).f i
      ((1 : C) ⊗ₜ[B,conjugateValue d c g]
        ((DF.comparison.hom.app X).f i (extendPure d f X i 1 x)))
  rw [DF.comparison_on_pure, map_one, diagonalComposition_on_one]

open Specs.DerivedFormalization.CochainTensor (tensor pure map)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit representedUnitZero)
open Functor.OplaxMonoidal (δ)
open Functor.LaxMonoidal (ε μ)

local notation "Lg" => extension c g
local notation "Lgf" => extension c (g.comp f)

private theorem doubleExtendedTensor_hom_ext
    {X Y : compValue.{a} R} {Z : compValue.{a} T}
    {p q : (Lg).obj ((L).obj (tensor X Y)) ⟶ Z}
    (h : ∀ i j n (h : i + j = n) (x : X.X i) (y : Y.X j),
      let v := extendPure c g ((L).obj (tensor X Y)) n 1
        (extendPure d f (tensor X Y) n 1 (pure X Y h x y))
      p.f n v = q.f n v) :
    p = q := by
  apply HomologicalComplex.hom_ext
  intro n
  let adj := (representedExtensionAdjunction d f).comp (representedExtensionAdjunction c g)
  apply (adj.homEquiv _ _).injective
  apply CochainTensor.term_hom_ext
  intro i j hij x y
  simp only [Adjunction.homEquiv_unit, ConcreteCategory.comp_apply]
  let K := tensor X Y
  change p.f n (((extensionAdjunction c g).unit.app ((L).obj K)).f n
      (((extensionAdjunction d f).unit.app K).f n (pure X Y hij x y))) =
    q.f n (((extensionAdjunction c g).unit.app ((L).obj K)).f n
      (((extensionAdjunction d f).unit.app K).f n (pure X Y hij x y)))
  rw [unit_apply, unit_apply]
  exact h i j n hij x y

private def rawTensoratorIso {MR : AdequateModel e} {MS : AdequateModel d}
    (F : MonoidalChange e d f MR MS) (X Y : compValue.{a} R) :
    tensor ((L).obj X) ((L).obj Y) ≅ (L).obj (tensor X Y) :=
  letI := MR.chainMonoidal
  letI := MS.chainMonoidal
  letI := MR.chainSymmetric
  letI := MS.chainSymmetric
  letI := F.extensionBraided
  MS.tensorModel ((L).obj X) ((L).obj Y) ≪≫ Functor.Monoidal.μIso L X Y ≪≫
    (L).mapIso (MR.tensorModel X Y).symm

private theorem rawTensorator_inv_on_one {MR : AdequateModel e} {MS : AdequateModel d}
    (F : MonoidalChange e d f MR MS) (X Y : compValue.{a} R) {i j n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (rawTensoratorIso (e := e) (d := d) (f := f) F X Y).inv.f n
      (extendPure d f (tensor X Y) n 1 (pure X Y h x y)) =
    pure ((L).obj X) ((L).obj Y) h (extendPure d f X i 1 x) (extendPure d f Y j 1 y) := by
  let α := rawTensoratorIso (e := e) (d := d) (f := f) F X Y
  let v := pure ((L).obj X) ((L).obj Y) h (extendPure d f X i 1 x) (extendPure d f Y j 1 y)
  have hv : α.hom.f n v = extendPure d f (tensor X Y) n 1 (pure X Y h x y) := by
    have hv := F.tensor_on_pure X Y h 1 1 x y
    rw [one_mul] at hv
    exact hv
  exact (congrArg (α.inv.f n) hv).symm.trans
    (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom α.hom_inv_id n) v)

private def rawUnitator {MR : AdequateModel e} {MS : AdequateModel d}
    (F : MonoidalChange e d f MR MS) :
    representedUnit d ⟶ (L).obj (representedUnit e) :=
  letI := MR.chainMonoidal
  letI := MS.chainMonoidal
  letI := MR.chainSymmetric
  letI := MS.chainSymmetric
  letI := F.extensionBraided
  (MS.unitModel ≪≫ Functor.Monoidal.εIso L ≪≫ (L).mapIso MR.unitModel.symm).hom

private theorem rawUnitator_on_pure {MR : AdequateModel e} {MS : AdequateModel d}
    (F : MonoidalChange e d f MR MS) (b : B) :
    (rawUnitator (e := e) (d := d) (f := f) F).f 0 ((representedUnitZero d).inv b) =
      extendPure d f (representedUnit e) 0 (d.symm b) ((representedUnitZero e).inv (1 : A)) :=
  F.unit_on_pure b

private theorem compareRawTensorators
    {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}
    (F : MonoidalChange e d f MR MS) (G : MonoidalChange d c g MS MT)
    (GF : MonoidalChange e c (g.comp f) MR MT) (X Y : compValue.{a} R) :
    (compositionIso d f c g).hom.app (tensor X Y) ≫
      (rawTensoratorIso (e := e) (d := c) (f := g.comp f) GF X Y).inv =
    (Lg).map (rawTensoratorIso (e := e) (d := d) (f := f) F X Y).inv ≫
      (rawTensoratorIso (e := d) (d := c) (f := g) G ((L).obj X) ((L).obj Y)).inv ≫
        map ((compositionIso d f c g).hom.app X) ((compositionIso d f c g).hom.app Y) := by
  apply doubleExtendedTensor_hom_ext d f c g
  intro i j n h x y
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  erw [composition_on_one d f c g (tensor X Y) n (pure X Y h x y),
    rawTensorator_inv_on_one (e := e) (d := c) (f := g.comp f) GF X Y h x y,
    extendPure_map, rawTensorator_inv_on_one (e := e) (d := d) (f := f) F X Y h x y,
    rawTensorator_inv_on_one (e := d) (d := c) (f := g) G ((L).obj X) ((L).obj Y) h,
    CochainTensor.map_on_pure, composition_on_one d f c g X i x, composition_on_one d f c g Y j y]

private theorem compareRawUnitators
    {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}
    (F : MonoidalChange e d f MR MS) (G : MonoidalChange d c g MS MT)
    (GF : MonoidalChange e c (g.comp f) MR MT) :
    rawUnitator (e := d) (d := c) (f := g) G ≫ (Lg).map (rawUnitator (e := e) (d := d) (f := f) F) ≫
      (compositionIso d f c g).hom.app (representedUnit e) =
    rawUnitator (e := e) (d := c) (f := g.comp f) GF := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (representedUnitZero c).inv).2 x
    change C at b
    simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
    erw [rawUnitator_on_pure, extendPure_map, rawUnitator_on_pure,
      composition_on_pure d f c g (representedUnit e) 0,
      rawUnitator_on_pure]
    simp only [map_one, mul_one]
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i h).eq_of_src

private theorem normalizedDelta {MR : AdequateModel e} {MS : AdequateModel d}
    (F : MonoidalChange e d f MR MS) (X Y : compValue.{a} R) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := F.extensionBraided
    (L).map (MR.tensorModel X Y).hom ≫ δ L X Y =
      (rawTensoratorIso (e := e) (d := d) (f := f) F X Y).inv ≫
        (MS.tensorModel ((L).obj X) ((L).obj Y)).hom := by
  dsimp only [rawTensoratorIso, Iso.trans_inv, Functor.Monoidal.μIso_inv, Functor.mapIso_inv]
  simp only [Iso.symm_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
private theorem normalizedEpsilon {MR : AdequateModel e} {MS : AdequateModel d}
    (F : MonoidalChange e d f MR MS) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := F.extensionBraided
    MS.unitModel.hom ≫ ε L =
      rawUnitator (e := e) (d := d) (f := f) F ≫ (L).map MR.unitModel.hom := by
  dsimp only [rawUnitator, Iso.trans_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom]
  simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option linter.style.haveILetI false in
theorem composition_isMonoidal
    (MR : AdequateModel e) (MS : AdequateModel d) (MT : AdequateModel c)
    (F : MonoidalChange e d f MR MS) (G : MonoidalChange d c g MS MT)
    (GF : MonoidalChange e c (g.comp f) MR MT) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MT.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := MT.chainSymmetric
    letI := F.extensionBraided
    letI := G.extensionBraided
    letI := GF.extensionBraided
    NatTrans.IsMonoidal (compositionIso d f c g).hom := by
  letI := MR.chainMonoidal
  letI := MS.chainMonoidal
  letI := MT.chainMonoidal
  letI := MR.chainSymmetric
  letI := MS.chainSymmetric
  letI := MT.chainSymmetric
  letI := F.extensionBraided
  letI := G.extensionBraided
  letI := GF.extensionBraided
  let τ := (compositionIso d f c g).hom
  constructor
  · apply (cancel_epi MT.unitModel.hom).mp
    change MT.unitModel.hom ≫ (ε (Lg) ≫ (Lg).map (ε L)) ≫ τ.app (𝟙_ (compValue.{a} R)) =
      MT.unitModel.hom ≫ ε Lgf
    rw [Category.assoc (ε (Lg)), normalizedEpsilon_assoc (d := c) (f := g) (e := d) G,
      ← Functor.map_comp_assoc, normalizedEpsilon (d := d) (f := f) (e := e) F,
      Functor.map_comp, Category.assoc,
      normalizedEpsilon (d := c) (f := g.comp f) (e := e) GF]
    have hnat := τ.naturality MR.unitModel.hom
    change (Lg).map ((L).map MR.unitModel.hom) ≫ τ.app _ =
      τ.app (representedUnit e) ≫ (Lgf).map MR.unitModel.hom at hnat
    rw [hnat]
    simpa only [Category.assoc] using
      congrArg (fun p => p ≫ (Lgf).map MR.unitModel.hom)
        (compareRawUnitators (e := e) (d := d) (f := f) (c := c) (g := g) F G GF)
  · intro X Y
    have hd : (δ (L ⋙ Lg) X Y) ≫ (τ.app X ⊗ₘ τ.app Y) =
        τ.app (X ⊗ Y) ≫ δ Lgf X Y := by
      apply (cancel_epi ((L ⋙ Lg).map (MR.tensorModel X Y).hom)).mp
      change (Lg).map ((L).map (MR.tensorModel X Y).hom) ≫
          ((Lg).map (δ L X Y) ≫ δ Lg ((L).obj X) ((L).obj Y)) ≫ (τ.app X ⊗ₘ τ.app Y) =
        (Lg).map ((L).map (MR.tensorModel X Y).hom) ≫ τ.app (X ⊗ Y) ≫ δ Lgf X Y
      rw [← Category.assoc, ← Functor.map_comp_assoc,
        normalizedDelta (d := d) (f := f) (e := e) F, Functor.map_comp, Category.assoc,
        Category.assoc, ← Category.assoc ((Lg).map (MS.tensorModel ((L).obj X) ((L).obj Y)).hom),
        normalizedDelta (d := c) (f := g) (e := d) G, Category.assoc,
        ← MT.tensorModel_natural]
      have hnat := τ.naturality (MR.tensorModel X Y).hom
      change (Lg).map ((L).map (MR.tensorModel X Y).hom) ≫ τ.app _ =
        τ.app (tensor X Y) ≫ (Lgf).map (MR.tensorModel X Y).hom at hnat
      rw [reassoc_of% hnat, normalizedDelta (d := c) (f := g.comp f) (e := e) GF]
      simpa only [Category.assoc] using
        congrArg (fun p => p ≫ (MT.tensorModel ((Lgf).obj X) ((Lgf).obj Y)).hom)
          (compareRawTensorators (e := e) (d := d) (f := f) (c := c) (g := g) F G GF X Y).symm
    apply (cancel_epi (δ (L ⋙ Lg) X Y)).mp
    apply (cancel_mono (δ Lgf X Y)).mp
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    exact hd.symm

theorem composition_conditional.{ru,su,tu,au}
    (_ : adequateModelType.{ru,au}) (_ : closedAdjunctionType.{ru,au})
    (_ : curryingType.{ru,au}) (_ : ringComparisonType.{ru,au}) :
    compositionType.{ru,su,tu,au} := by
  intro R S T A B C _ _ _ _ _ _ e d c f g
  exact ⟨composition_on_pure d f c g,
    composition_isMonoidal (e := e) (d := d) (f := f) (c := c) (g := g),
    fun DF DG DGF X => composition_respects_diagonal (e := e) (d := d) (f := f)
      (c := c) (g := g) DF DG DGF X⟩

end Transitivity

end

end DerivedFormalization.ScalarExtensionTransport

universe v8_closure_045d8982090b844a_u0 v8_closure_045d8982090b844a_u1 v8_closure_045d8982090b844a_u2 v8_closure_045d8982090b844a_u3
theorem _root_.«DerivedFormalization».«ScalarExtensionTransport».«composition» : _root_.«Specs».«DerivedFormalization».«ScalarExtensionTransport».«compositionType».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2, v8_closure_045d8982090b844a_u3} :=
  @_root_.«DerivedFormalization».«ScalarExtensionTransport».«composition_conditional».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2, v8_closure_045d8982090b844a_u3} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u3}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u3}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u3}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u3})
theorem _root_.«DerivedFormalization».«ScalarExtensionTransport».«modelStability» : _root_.«Specs».«DerivedFormalization».«ScalarExtensionTransport».«modelStabilityType».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2} :=
  @_root_.«DerivedFormalization».«ScalarExtensionTransport».«modelStability_conditional».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2})
theorem _root_.«DerivedFormalization».«ScalarExtensionTransport».«monoidalComparison» : _root_.«Specs».«DerivedFormalization».«ScalarExtensionTransport».«monoidalComparisonType».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2} :=
  @_root_.«DerivedFormalization».«ScalarExtensionTransport».«monoidalComparison_conditional».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2})
theorem _root_.«DerivedFormalization».«ScalarExtensionTransport».«nativeExtension» : _root_.«Specs».«DerivedFormalization».«ScalarExtensionTransport».«nativeExtensionType».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2} :=
  @_root_.«DerivedFormalization».«ScalarExtensionTransport».«nativeExtension_conditional».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u1, v8_closure_045d8982090b844a_u2} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_045d8982090b844a_u0, v8_closure_045d8982090b844a_u2})
