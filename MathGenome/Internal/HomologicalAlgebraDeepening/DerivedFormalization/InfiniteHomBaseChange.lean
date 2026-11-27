import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.InfiniteHomBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomComparisonMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedScalarExtension
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Batteries.Tactic.OpenPrivate

/-! The infinite free source in the Hom base-change example. -/

namespace DerivedFormalization.InfiniteHomBaseChange

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
open Specs.DerivedFormalization.InfiniteHomBaseChange

universe u

set_option linter.style.haveILetI false
set_option maxHeartbeats 650000

noncomputable section

attribute [local instance] HasDerivedCategory.standard

private theorem coefficientMap_tmul {k : Type u} [Field k] (s : Polynomial k)
    (a : ℕ → k) (n : ℕ) : coefficientMap k (s ⊗ₜ[k] a) n = s * Polynomial.C (a n) := rfl

theorem coefficientBound : CoefficientBound.{u} := by
  intro k _ x
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    refine ⟨s.natDegree, fun n => ?_⟩
    rw [coefficientMap_tmul, mul_comm]
    exact Polynomial.natDegree_C_mul_le (a n) s
  | add x y hx hy =>
    obtain ⟨Nx, hx⟩ := hx
    obtain ⟨Ny, hy⟩ := hy
    refine ⟨max Nx Ny, fun n => ?_⟩
    rw [map_add, Pi.add_apply]
    exact Polynomial.natDegree_add_le_of_le (hx n) (hy n)

theorem missingSequence : MissingSequence.{u} := by
  intro k _ h
  obtain ⟨x, hx⟩ := h
  obtain ⟨N, hN⟩ := coefficientBound k x
  have h := hN (N + 1)
  rw [hx, Polynomial.natDegree_X_pow] at h
  omega

section Comparison

open Specs.DerivedFormalization.Cochains (compValue derivedValue qValue)
open Specs.DerivedFormalization.CochainTensor (tensor isKFlat)
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.DerivedHomAdjunction (Closed Presentation tensorComparison homComparison)
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)
open Specs.DerivedFormalization.DerivedHomComparisonMaps (evaluationValue baseChangeValue)
open Specs.DerivedFormalization.DerivedScalarExtension (Extension MonoidalExtension)
open Specs.DerivedFormalization.ScalarExtensionTransport (extension MonoidalChange)

open private presentationOf overIntoInjective homComparison_natural
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction
open private transpose_precomp from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomComparisonMaps

variable {R S : Type u} [CommRing R] [CommRing S]
  {MR : AdequateModel (RingEquiv.refl R)} {MS : AdequateModel (RingEquiv.refl S)}
  {TR : Specs.DerivedFormalization.DerivedTensor.Model MR}
  {TS : Specs.DerivedFormalization.DerivedTensor.Model MS}
  {HR : Models.{u,u} R} {HS : Models.{u,u} S}

set_option backward.isDefEq.respectTransparency false in
private theorem curry_on_projective (c : Closed TR HR)
    {Z X Y : derivedValue.{u} R}
    (A : Presentation Z) (P : Presentation X) (B : Presentation Y)
    (hP : isKFlat P.complex) (hp : P.complex.IsKProjective)
    (g : tensor A.complex P.complex ⟶ B.complex) :
    c.equiv Z X Y ((tensorComparison TR A P hP).hom ≫ (qValue R).map g ≫ B.iso.hom) =
      A.iso.inv ≫ (qValue R).map ((MR.rawClosed P.complex).adj.homEquiv _ _ g) ≫
        homComparison HR P B := by
  let J := presentationOf (HR.injective Y)
  have hj : J.complex.IsKInjective := HR.isInjective Y
  obtain ⟨i, hi⟩ := overIntoInjective B J hj (𝟙 Y)
  have hi' : (qValue R).map i ≫ J.iso.hom = B.iso.hom := by
    simpa [Presentation.Over] using hi
  have hn := homComparison_natural HR P P B J (Or.inl hp) (Or.inr hj)
    (x := 𝟙 X) (𝟙 P.complex) i (by simp [Presentation.Over]) hi
  change (qValue R).map (internalHomMapValue (𝟙 P.complex) i) ≫ homComparison HR P J =
    homComparison HR P B ≫ (rHomValue HR).map (𝟙 _) at hn
  rw [(rHomValue HR).map_id, Category.comp_id] at hn
  have hc := c.on_models A P J hP hj (g ≫ i)
  have hr := (MR.rawClosed P.complex).adj.homEquiv_naturality_right g i
  change (MR.rawClosed P.complex).adj.homEquiv A.complex J.complex (g ≫ i) =
    (MR.rawClosed P.complex).adj.homEquiv A.complex B.complex g ≫
      internalHomMapValue (𝟙 P.complex) i at hr
  simp only [(qValue R).map_comp, Category.assoc, hi', hr, hn] at hc
  exact hc

local notation "present" => stalkPresentation

private theorem flat_tensorComparison {Z X : derivedValue.{u} R}
    (A : Presentation Z) (P : Presentation X)
    (hA : isKFlat A.complex) (hP : isKFlat P.complex) :
    letI := TR.monoidal
    (tensorComparison TR A P hP).hom =
      (A.iso.inv ⊗ₘ P.iso.inv) ≫ (TR.toDescent.flatComparison A.complex P.complex hA hP).hom := by
  letI := TR.monoidal
  have h : TR.compare A.complex P.complex (Or.inr hP) =
      TR.toDescent.flatComparison A.complex P.complex hA hP :=
    TR.compare_flat _ _ hA hP
  rw [tensorComparison, Iso.trans_hom, h]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_on_model (c : Closed TR HR) (P Y : compValue.{u} R)
    (hP : isKFlat P) (hp : P.IsKProjective) (hH : isKFlat (internalHomValue P Y)) :
    letI := TR.monoidal
    let Q := qValue R
    let H := internalHomValue P Y
    (homComparison HR (present P) (present Y) ⊗ₘ 𝟙 (Q.obj P)) ≫
        evaluationValue c (Q.obj P) (Q.obj Y) =
      (TR.toDescent.flatComparison H P hH hP).hom ≫
        Q.map ((MR.rawClosed P).adj.counit.app Y) := by
  letI := TR.monoidal
  let Q := qValue.{u} R
  let H := internalHomValue P Y
  let ev : tensor H P ⟶ Y := (MR.rawClosed P).adj.counit.app Y
  let rt := TR.toDescent.flatComparison H P hH hP
  let a := homComparison HR (present P) (present Y)
  let v := evaluationValue c (Q.obj P) (Q.obj Y)
  have ht : (tensorComparison TR (present H) (present P) hP).hom = rt.hom := by
    have h := flat_tensorComparison (TR := TR) (present H) (present P) hH hP
    simpa only [stalkPresentation, Iso.refl_inv, id_tensorHom_id, Category.id_comp] using h
  have he : (MR.rawClosed P).adj.homEquiv H Y ev = 𝟙 H := by
    exact (Equiv.eq_symm_apply (e := (MR.rawClosed P).adj.homEquiv H Y)).1
      ((MR.rawClosed P).adj.homEquiv_symm_id Y).symm
  have hc := curry_on_projective c (present H) (present P) (present Y) hP hp ev
  have hc' : c.equiv (Q.obj H) (Q.obj P) (Q.obj Y) (rt.hom ≫ Q.map ev) = a := by
    simp only [ht, stalkPresentation, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
      Category.comp_id, he, (qValue R).map_id] at hc
    exact hc
  have hv := transpose_precomp c a v
  change c.equiv (Q.obj H) (Q.obj P) (Q.obj Y) ((a ⊗ₘ 𝟙 _) ≫ v) =
    a ≫ c.equiv _ _ _ ((c.equiv _ _ _).symm (𝟙 _)) at hv
  rw [LinearEquiv.apply_symm_apply, Category.comp_id] at hv
  exact (c.equiv (Q.obj H) (Q.obj P) (Q.obj Y)).injective (hv.trans hc'.symm)

variable {f : R →+* S}
  {F : MonoidalChange (RingEquiv.refl R) (RingEquiv.refl S) f MR MS}
  {L : Extension (RingEquiv.refl S) f}

local notation "E" => extension (RingEquiv.refl S) f
local notation "Q" => qValue R
local notation "Q'" => qValue S
local notation "Hom" => internalHomValue


set_option backward.isDefEq.respectTransparency false in
private theorem extension_model_natural {X Y : compValue.{u} R}
    (hX : isKFlat X) (hY : isKFlat Y) (g : X ⟶ Y) :
    L.derived.map ((Q).map g) ≫ (L.toLift.model Y hY).hom =
      (L.toLift.model X hX).hom ≫ (Q').map ((E).map g) := by
  exact L.factors.hom.naturality
    (show (⟨X, hX⟩ : (Specs.DerivedFormalization.DerivedScalarExtension.flatComplexes R).FullSubcategory) ⟶ ⟨Y, hY⟩
      from ObjectProperty.homMk g)

set_option backward.isDefEq.respectTransparency false in
private theorem derived_comparison_on_models (cR : Closed TR HR) (cS : Closed TS HS)
    (m : MonoidalExtension TR.toDescent TS.toDescent F L)
    (P Y : compValue.{u} R) (hp : P.IsKProjective)
    (hP : isKFlat P) (hY : isKFlat Y) (hH : isKFlat (Hom P Y))
    (hT : isKFlat (tensor (Hom P Y) P)) :
    L.derived.map (homComparison HR (present P) (present Y)) ≫
        baseChangeValue cR cS m ((Q).obj P) ((Q).obj Y) =
      (L.toLift.model (Hom P Y) hH).hom ≫ (Q').map (chainComparison F P Y) ≫
        homComparison HS (extendedPresentation L P hP) (extendedPresentation L Y hY) := by
  letI := MR.chainMonoidal
  letI := MS.chainMonoidal
  letI := MR.chainSymmetric
  letI := MS.chainSymmetric
  letI := F.extensionBraided
  letI := TR.monoidal
  letI := TS.monoidal
  letI := TR.symmetric
  letI := TS.symmetric
  letI := m.braided
  let H := Hom P Y
  let ev : tensor H P ⟶ Y := (MR.rawClosed P).adj.counit.app Y
  let aH := L.toLift.model H hH
  let aP := L.toLift.model P hP
  let aY := L.toLift.model Y hY
  let aT := L.toLift.model (tensor H P) hT
  let b := MS.tensorModel ((E).obj H) ((E).obj P) ≪≫ Functor.Monoidal.μIso E H P ≪≫
    (E).mapIso (MR.tensorModel H P).symm
  let rt := TR.toDescent.flatComparison H P hH hP
  let st := TS.toDescent.flatComparison ((E).obj H) ((E).obj P)
    (L.preservesFlat H hH) (L.preservesFlat P hP)
  let rh := homComparison HR (present P) (present Y)
  let X := (Q).obj P
  let V := (Q).obj Y
  let W := (rHomValue HR).obj (op X, V)
  let D := L.derived
  change D.map rh ≫ cS.equiv _ _ _
    (Functor.LaxMonoidal.μ D W X ≫ D.map (evaluationValue cR X V)) = _
  rw [← transpose_precomp cS, ← D.map_id X,
    Functor.LaxMonoidal.μ_natural_assoc, ← D.map_comp,
    evaluation_on_model cR P Y hP hp hH, D.map_comp]
  have ht := congrArg Iso.hom (m.tensor_on_models H P hH hP hT)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom, tensorIso_hom] at ht
  change Functor.LaxMonoidal.μ D ((Q).obj H) X ≫ D.map rt.hom ≫ aT.hom =
    (aH.hom ⊗ₘ aP.hom) ≫ st.hom ≫ (Q').map b.hom at ht
  have hn : D.map ((Q).map ev) = aT.hom ≫ (Q').map ((E).map ev) ≫ aY.inv := by
    apply (cancel_mono aY.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (extension_model_natural (L := L) hT hY ev)
  rw [hn, reassoc_of% ht, ← (Q').map_comp_assoc]
  have hc := curry_on_projective cS (extendedPresentation L H hH)
    (extendedPresentation L P hP) (extendedPresentation L Y hY)
    (L.preservesFlat P hP) (L.preservesProjective P hp) (b.hom ≫ (E).map ev)
  have htc : (tensorComparison TS (extendedPresentation L H hH)
      (extendedPresentation L P hP) (L.preservesFlat P hP)).hom =
      (aH.hom ⊗ₘ aP.hom) ≫ st.hom :=
    flat_tensorComparison (TR := TS) (extendedPresentation L H hH)
      (extendedPresentation L P hP) (L.preservesFlat H hH) (L.preservesFlat P hP)
  simp only [htc, Category.assoc] at hc
  exact hc

end Comparison

section DegreeZero

open HomologicalComplex
open CochainComplex.HomComplex (Cochain)
open Specs.DerivedFormalization.Cochains (compValue stalkValue)
open Specs.DerivedFormalization.CochainModels (internalHomValue)
open Specs.DerivedFormalization.CochainTensor (isKFlat)
open Specs.DerivedFormalization.ScalarExtensionTransport (extension extendPure)


private theorem stalk_concentrated {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    DegreeZero ((stalkValue R).obj M) :=
  fun i hi => isZero_single_obj_X (.up ℤ) 0 M i hi

private theorem extend_concentrated {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {C : compValue.{u} R} (h : DegreeZero C) :
    DegreeZero ((extension (RingEquiv.refl S) f).obj C) :=
  fun i hi => (Specs.DerivedFormalization.CochainRingTransport.representedExtension
    (RingEquiv.refl S) f).map_isZero (h i hi)

private theorem hom_concentrated {R : Type u} [CommRing R] {C D : compValue.{u} R}
    (hC : DegreeZero C) (hD : DegreeZero D) :
    DegreeZero (internalHomValue C D) := by
  intro i hi
  apply ModuleCat.isZero_iff_subsingleton.2
  constructor
  intro f g
  apply Cochain.ext
  intro p q hpq
  by_cases hp : p = 0
  · apply (hD q (by omega)).eq_of_tgt
  · exact (hC p hp).eq_of_src _ _

private theorem concentrated_kProjective {k : Type u} [Field k] {C : compValue.{u} k}
    (h : DegreeZero C) : C.IsKProjective := by
  letI (i : ℤ) : Projective (C.X i) := by
    letI : Module.Free k (C.X i) := Module.Free.of_divisionRing k (C.X i)
    letI : Module.Projective k (C.X i) := Module.Projective.of_free
    exact ModuleCat.projective_of_categoryTheory_projective (C.X i)
  letI : C.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff C 0).2
    (fun i hi => h i (by omega))
  exact CochainComplex.isKProjective_of_projective C 0

private def homTermZero {R : Type u} [CommRing R] {C D : compValue.{u} R}
    (hC : DegreeZero C) : (internalHomValue C D).X 0 ≃ₗ[R] (C.X 0 ⟶ D.X 0) :=
  LinearEquiv.ofBijective
    { toFun := fun v : Cochain C D 0 => v.v 0 0 rfl
      map_add' := fun v w => Cochain.add_v v w _ _ _
      map_smul' := fun r v => Cochain.smul_v r v _ _ _ }
    ⟨by
      intro f g h
      apply Cochain.ext
      intro p q hpq
      by_cases hp : p = 0
      · obtain rfl : q = 0 := by omega
        subst p
        exact h
      · exact (hC p hp).eq_of_src _ _,
      fun f => ⟨Cochain.single f 0, Cochain.single_v f 0 rfl⟩⟩

variable (k : Type u) [Field k]

local notation "S" => Polynomial k
local notation "Ex" => extension (RingEquiv.refl (Polynomial k)) (scalarMap k)
local notation "H" => internalHomValue (P k) (Y k)


private abbrev pZero : (P k).X 0 ≅ ModuleCat.of k (ℕ →₀ k) :=
  singleObjXSelf (.up ℤ) 0 _


private def basisEval (Z : compValue.{u} k) :
    (internalHomValue (P k) Z).X 0 ≃ₗ[k] (ℕ → Z.X 0) :=
  (homTermZero (stalk_concentrated _)).trans
    ((Linear.homCongr k (pZero k) (Iso.refl (Z.X 0))).trans
      (ModuleCat.homLinearEquiv.trans (Finsupp.llift (Z.X 0) k k ℕ).symm))

private theorem basisEval_apply (Z : compValue.{u} k)
    (v : (internalHomValue (P k) Z).X 0) (n : ℕ) :
    basisEval k Z v n = v.v 0 0 rfl (basisVector k n) := by
  simp only [basisEval, LinearEquiv.trans_apply, Finsupp.llift_symm_apply,
    Linear.homCongr_apply]
  rfl

private def sourceTerm : (H).X 0 ≃ₗ[k] (ℕ → k) :=
  (basisEval k (Y k)).trans (LinearEquiv.piCongrRight (fun _ => (yZero k).toLinearEquiv))

private def extendedSourceTerm : ((Ex).obj H).X 0 ≃ₗ[S] S ⊗[k] (ℕ → k) :=
  (polynomialTensorTerm k H 0).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) (sourceTerm k))

open Specs.DerivedFormalization.ScalarExtensionTransport (restriction ModelStability)

private theorem polynomialTensorTerm_tmul (C : compValue.{u} k) (i : ℤ) (s : S) (z : C.X i) :
    polynomialTensorTerm k C i (extendPure (RingEquiv.refl S) (scalarMap k) C i s z) =
      s ⊗ₜ[k] z := rfl

private theorem extendedSourceTerm_tmul (s : S) (v : (H).X 0) :
    extendedSourceTerm k (extendPure (RingEquiv.refl S) (scalarMap k) H 0 s v) =
      s ⊗ₜ[k] (fun n => (yZero k).hom (v.v 0 0 rfl (basisVector k n))) := by
  simp only [extendedSourceTerm, LinearEquiv.trans_apply, polynomialTensorTerm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  rfl

private theorem extendedYTerm_tmul (s : S) (v : (Y k).X 0) :
    extendedYTerm k (extendPure (RingEquiv.refl S) (scalarMap k) (Y k) 0 s v) =
      Polynomial.C ((yZero k).hom v) * s := by
  simp only [extendedYTerm, LinearEquiv.trans_apply, polynomialTensorTerm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul, Polynomial.smul_eq_C_mul]
  rfl

private def targetTerm : (extendedTarget k).X 0 ≃ₗ[S] (ℕ → S) := by
  let U := restriction (RingEquiv.refl S) (scalarMap k)
  let Z := (Ex).obj (Y k)
  let c := Classical.choice (DerivedFormalization.ScalarExtensionTransport.modelStability
    (RingEquiv.refl S) (scalarMap k))
  let t := (eval (ModuleCat.{u} k) (.up ℤ) 0).mapIso (c.homIso (P k) Z)
  let equiv : (extendedTarget k).X 0 ≃ (ℕ → S) :=
    t.toLinearEquiv.toEquiv.trans ((basisEval k (U.obj Z)).toEquiv.trans
      (Equiv.piCongrRight (fun _ => (extendedYTerm k).toEquiv)))
  let x := fun n => extendPure (RingEquiv.refl S) (scalarMap k) (P k) 0 1 (basisVector k n)
  let v := homTermZero (D := Z) (extend_concentrated (scalarMap k)
    (show DegreeZero (P k) from stalk_concentrated _))
  let g : (extendedTarget k).X 0 →ₗ[S] (ℕ → S) :=
    (LinearMap.pi fun n => (extendedYTerm k).toLinearMap.comp (LinearMap.applyₗ (x n))).comp
      (ModuleCat.homLinearEquiv.toLinearMap.comp v.toLinearMap)
  refine LinearEquiv.ofBijective g ?_
  have h : (g : _ → _) = equiv := by
    funext v n
    change extendedYTerm k (v.v 0 0 rfl (x n)) =
      extendedYTerm k (basisEval k (U.obj Z) (t.hom v) n)
    rw [basisEval_apply]
    exact congrArg (extendedYTerm k) ((c.hom_on_eval (P k) Z rfl v (basisVector k n)).symm)
  rw [h]
  exact equiv.bijective

private theorem targetTerm_apply (v : (extendedTarget k).X 0) (n : ℕ) :
    targetTerm k v n = extendedYTerm k
      (v.v 0 0 rfl (extendPure (RingEquiv.refl S) (scalarMap k) (P k) 0 1 (basisVector k n))) := rfl

open Specs.DerivedFormalization.CochainTensor (pure tensor)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange)

variable {MR : AdequateModel (RingEquiv.refl k)}
  {MS : AdequateModel (RingEquiv.refl (Polynomial k))}
  (F : MonoidalChange (RingEquiv.refl k) (RingEquiv.refl (Polynomial k)) (scalarMap k) MR MS)

open private extendPure_map from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ScalarExtensionTransport

set_option backward.isDefEq.respectTransparency false in
private theorem chainComparison_on_pure (s : S) (v : (H).X 0) (x : (P k).X 0) :
    (((chainComparison F (P k) (Y k)).f 0)
       (extendPure (RingEquiv.refl S) (scalarMap k) H 0 s v)).v 0 0 rfl
        (extendPure (RingEquiv.refl S) (scalarMap k) (P k) 0 1 x) =
      extendPure (RingEquiv.refl S) (scalarMap k) (Y k) 0 s (v.v 0 0 rfl x) := by
  letI := MR.chainMonoidal
  letI := MS.chainMonoidal
  letI := MR.chainSymmetric
  letI := MS.chainSymmetric
  letI := F.extensionBraided
  let X := (Ex).obj H
  let P' := (Ex).obj (P k)
  let Y' := (Ex).obj (Y k)
  let y := extendPure (RingEquiv.refl S) (scalarMap k) H 0 s v
  let z := extendPure (RingEquiv.refl S) (scalarMap k) (P k) 0 1 x
  let b := MS.tensorModel X P' ≪≫ Functor.Monoidal.μIso Ex H (P k) ≪≫
    (Ex).mapIso (MR.tensorModel H (P k)).symm
  let ev : tensor H (P k) ⟶ Y k := (MR.rawClosed (P k)).adj.counit.app (Y k)
  have h := (MS.rawClosed P').on_pure X Y' (b.hom ≫ (Ex).map ev) 0 0 y z
  change (((chainComparison F (P k) (Y k)).f 0) y).v 0 0 rfl z =
    ((Ex).map ev).f 0 (b.hom.f 0 (pure X P' rfl y z)) at h
  change (((chainComparison F (P k) (Y k)).f 0) y).v 0 0 rfl z = _
  rw [h]
  have hb : b.hom.f 0 (pure X P' rfl y z) =
      extendPure (RingEquiv.refl S) (scalarMap k) (tensor H (P k)) 0 (s * 1)
        (pure H (P k) rfl v x) := F.tensor_on_pure H (P k) rfl s 1 v x
  rw [hb, mul_one, extendPure_map]
  exact congrArg (extendPure (RingEquiv.refl S) (scalarMap k) (Y k) 0 s)
    ((MR.rawClosed (P k)).counit_on_pure (Y k) 0 0 v x)

private theorem chain_on_coefficients (z : (extendedSource k).X 0) :
    targetTerm k ((chainComparison F (P k) (Y k)).f 0 z) =
      coefficientMap k (extendedSourceTerm k z) := by
  let f := (targetTerm k).toLinearMap.comp ((chainComparison F (P k) (Y k)).f 0).hom
  let g := (coefficientMap k).comp (extendedSourceTerm k).toLinearMap
  let e := polynomialTensorTerm k H 0
  obtain ⟨z, rfl⟩ := e.symm.surjective z
  change f (e.symm z) = g (e.symm z)
  have he : f.comp e.symm.toLinearMap = g.comp e.symm.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s v
    have hr : e.symm (s ⊗ₜ[k] v) = extendPure (RingEquiv.refl S) (scalarMap k) H 0 s v :=
      e.symm_apply_eq.mpr (polynomialTensorTerm_tmul k H 0 s v).symm
    change f (e.symm (s ⊗ₜ[k] v)) = g (e.symm (s ⊗ₜ[k] v))
    rw [hr]
    funext n
    dsimp only [f, g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change targetTerm k ((chainComparison F (P k) (Y k)).f 0
      (extendPure (RingEquiv.refl S) (scalarMap k) H 0 s v)) n =
      coefficientMap k (extendedSourceTerm k (extendPure (RingEquiv.refl S) (scalarMap k) H 0 s v)) n
    rw [extendedSourceTerm_tmul, coefficientMap_tmul, targetTerm_apply,
      chainComparison_on_pure, extendedYTerm_tmul, mul_comm]
  exact LinearMap.congr_fun he z

end DegreeZero

section Cohomology

open HomologicalComplex
open Specs.DerivedFormalization.Cochains (compValue qValue cohomologyFactorsValue
  derivedCohomologyValue)
open Specs.DerivedFormalization.CochainTensor (tensor isKFlat)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.CochainModels (internalHomValue)
open Specs.DerivedFormalization.DerivedHomAdjunction (homComparison)
open Specs.DerivedFormalization.DerivedHomComparisonMaps (baseChangeValue)
open Specs.DerivedFormalization.ScalarExtensionTransport (extension)

open private kFlat_iff_monoidal from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedTensor
open private homComparisonIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction

private theorem tensor_kFlat {R : Type u} [CommRing R]
    (M : AdequateModel (RingEquiv.refl R)) {X Y : compValue.{u} R}
    (hX : isKFlat X) (hY : isKFlat Y) : isKFlat (tensor X Y) := by
  let T := M.chainMonoidal.toMonoidalCategoryStruct
  let xy := @MonoidalCategoryStruct.tensorObj _ _ T X Y
  have hFlat : isKFlat xy := (kFlat_iff_monoidal M xy).2 fun E hE n =>
    ((kFlat_iff_monoidal M _).1 hY _
      ((kFlat_iff_monoidal M _).1 hX E hE) n).of_iso (@MonoidalCategoryStruct.associator _ _ T E X Y)
  have hIso : tensor X Y ≅ xy := M.tensorModel X Y
  intro E hE n
  let a := M.tensorModel E (tensor X Y) ≪≫
    @MonoidalCategory.tensorIso _ _ M.chainMonoidal _ _ _ _ (Iso.refl E) hIso
  exact ((kFlat_iff_monoidal M _).1 hFlat E hE n).of_iso a.symm

private theorem termCohomology_natural {R : Type u} [CommRing R]
    {C D : compValue.{u} R} (hC : DegreeZero C) (hD : DegreeZero D) (g : C ⟶ D) :
    (termCohomologyIso C hC).hom ≫ homologyMap g 0 = g.f 0 ≫ (termCohomologyIso D hD).hom := by
  let j := (ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)
  let c := C.iCyclesIso 0 1 j ((hC 1 (by decide)).eq_of_tgt _ _)
  let d := D.iCyclesIso 0 1 j ((hD 1 (by decide)).eq_of_tgt _ _)
  have hc : c.inv ≫ cyclesMap g 0 = g.f 0 ≫ d.inv := by
    apply (cancel_mono d.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change c.inv ≫ cyclesMap g 0 ≫ D.iCycles 0 = g.f 0
    rw [cyclesMap_i]
    change c.inv ≫ c.hom ≫ g.f 0 = g.f 0
    exact c.inv_hom_id_assoc _
  change (c.inv ≫ C.homologyπ 0) ≫ homologyMap g 0 = g.f 0 ≫ d.inv ≫ D.homologyπ 0
  rw [Category.assoc, homologyπ_naturality, reassoc_of% hc]

private theorem termToDerived_natural {R : Type u} [CommRing R]
    {C D : compValue.{u} R} (hC : DegreeZero C) (hD : DegreeZero D) (g : C ⟶ D) :
    (termToDerived C hC).hom ≫ (derivedCohomologyValue R 0).map ((qValue R).map g) =
      g.f 0 ≫ (termToDerived D hD).hom := by
  have h := (cohomologyFactorsValue R 0).inv.naturality g
  change homologyMap g 0 ≫ (cohomologyFactorsValue R 0).inv.app D =
    (cohomologyFactorsValue R 0).inv.app C ≫
      (derivedCohomologyValue R 0).map ((qValue R).map g) at h
  change ((termCohomologyIso C hC).hom ≫ (cohomologyFactorsValue R 0).inv.app C) ≫
    (derivedCohomologyValue R 0).map ((qValue R).map g) =
    g.f 0 ≫ (termCohomologyIso D hD).hom ≫ (cohomologyFactorsValue R 0).inv.app D
  erw [Category.assoc, ← h, reassoc_of% termCohomology_natural hC hD g]

set_option backward.isDefEq.respectTransparency false in
theorem counterexample : Counterexample.{u} := by
  intro k _ MR MS TR TS HR HS F L cR cS m
  let S := Polynomial k
  let E := extension (RingEquiv.refl S) (scalarMap k)
  let H := internalHomValue (P k) (Y k)
  let hP₀ : DegreeZero (P k) := stalk_concentrated _
  let hY₀ : DegreeZero (Y k) := stalk_concentrated _
  let hH₀ : DegreeZero H := hom_concentrated hP₀ hY₀
  let hp := concentrated_kProjective hP₀
  let hP : isKFlat (P k) := L.projectiveFlat _ hp
  let hY : isKFlat (Y k) := L.projectiveFlat _ (concentrated_kProjective hY₀)
  let hH : isKFlat H := L.projectiveFlat _ (concentrated_kProjective hH₀)
  let hsrc : DegreeZero (extendedSource k) := extend_concentrated (scalarMap k) hH₀
  let hdst : DegreeZero (extendedTarget k) :=
    hom_concentrated (extend_concentrated (scalarMap k) hP₀) (extend_concentrated (scalarMap k) hY₀)
  let hT := tensor_kFlat MR hH hP
  let a := sourceCohomologyMap k (L := L) HR hH hsrc
  let b := targetCohomologyMap k (L := L) HS hP hY hdst
  let C := derivedCohomologyValue S 0
  let β₀ := baseChangeValue cR cS m ((qValue k).obj (P k)) ((qValue k).obj (Y k))
  let β := C.map β₀
  let g := chainComparison F (P k) (Y k)
  let homR := homComparison HR (stalkPresentation (P k)) (stalkPresentation (Y k))
  let homS := homComparison HS (extendedPresentation L (P k) hP) (extendedPresentation L (Y k) hY)
  let a₀ := (L.toLift.model H hH).inv ≫ L.derived.map homR
  haveI : IsIso homR := inferInstanceAs
    (IsIso (homComparisonIso HR (stalkPresentation (P k)) (stalkPresentation (Y k)) (Or.inl hp)).hom)
  haveI : IsIso homS := inferInstanceAs
    (IsIso (homComparisonIso HS (extendedPresentation L (P k) hP) (extendedPresentation L (Y k) hY)
      (Or.inl (L.preservesProjective _ hp))).hom)
  haveI : IsIso a := inferInstanceAs (IsIso ((termToDerived (extendedSource k) hsrc).hom ≫ C.map a₀))
  haveI : IsIso b := inferInstanceAs (IsIso ((termToDerived (extendedTarget k) hdst).hom ≫ C.map homS))
  have hm := derived_comparison_on_models cR cS m (P k) (Y k) hp hP hY hH hT
  change L.derived.map homR ≫ β₀ = (L.toLift.model H hH).hom ≫ (qValue S).map g ≫ homS at hm
  have hm' : a₀ ≫ β₀ = (qValue S).map g ≫ homS := by
    dsimp only [a₀]
    rw [Category.assoc, hm, Iso.inv_hom_id_assoc]
  have hc : a ≫ β = g.f 0 ≫ b := by
    change ((termToDerived (extendedSource k) hsrc).hom ≫ C.map a₀) ≫ C.map β₀ =
      g.f 0 ≫ (termToDerived (extendedTarget k) hdst).hom ≫ C.map homS
    rw [Category.assoc, ← C.map_comp, hm', C.map_comp,
      reassoc_of% termToDerived_natural hsrc hdst g]
  refine ⟨hp, hY, hH, hsrc, hdst, extendedSourceTerm k, targetTerm k, extendedSourceTerm_tmul k,
    targetTerm_apply k, inferInstance, inferInstance, ?_, ?_⟩
  · intro x
    have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hc) x
    change β (a x) = b (g.f 0 x) at h
    rw [h, ← chain_on_coefficients k F x, LinearEquiv.symm_apply_apply]
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := (asIso a).toLinearEquiv.surjective x
    change a z = x at hz
    subst x
    have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hc) z
    change β (a z) = b (g.f 0 z) at h
    change β (a z) = b ((targetTerm k).symm (fun n => Polynomial.X ^ n)) at hx
    have hEq := (asIso b).toLinearEquiv.injective (h.symm.trans hx)
    apply missingSequence k
    refine ⟨extendedSourceTerm k z, ?_⟩
    rw [← chain_on_coefficients k F z]
    change g.f 0 z = (targetTerm k).symm (fun n => Polynomial.X ^ n) at hEq
    rw [hEq, LinearEquiv.apply_symm_apply]

theorem existsCounterexample : ExistsCounterexample.{u} := by
  intro k _
  let S := Polynomial k
  obtain ⟨MR⟩ := DerivedFormalization.CochainTensorTransport.adequateModel (RingEquiv.refl k)
  obtain ⟨MS⟩ := DerivedFormalization.CochainTensorTransport.adequateModel (RingEquiv.refl S)
  obtain ⟨TR⟩ := DerivedFormalization.DerivedTensor.existsModel MR
  obtain ⟨TS⟩ := DerivedFormalization.DerivedTensor.existsModel MS
  let HR := DerivedFormalization.DerivedHomModels.models.{u,u} k
  let HS := DerivedFormalization.DerivedHomModels.models.{u,u} S
  obtain ⟨cR⟩ := DerivedFormalization.DerivedHomAdjunction.closed TR HR
  obtain ⟨cS⟩ := DerivedFormalization.DerivedHomAdjunction.closed TS HS
  obtain ⟨NR⟩ := DerivedFormalization.DerivedScalarExtension.ringTensor TR.toDescent
  obtain ⟨NS⟩ := DerivedFormalization.DerivedScalarExtension.ringTensor TS.toDescent
  obtain ⟨F, _, L, m, _⟩ :=
    DerivedFormalization.DerivedScalarExtension.existsExtension (scalarMap k) NR NS
  refine ⟨MR, MS, TR, TS, HR, HS, F, L, cR, cS, m, ?_⟩
  intro hs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ := counterexample k cR cS m
  exact h (hs _)

end Cohomology

end

end DerivedFormalization.InfiniteHomBaseChange
