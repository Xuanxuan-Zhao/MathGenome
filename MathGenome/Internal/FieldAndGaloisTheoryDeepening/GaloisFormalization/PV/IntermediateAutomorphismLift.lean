import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.RelativePicardVessiotTensor
import Mathlib.RingTheory.SimpleModule.Basic
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateAutomorphismLift

namespace GaloisFormalization.PV

open scoped Matrix TensorProduct nonZeroDivisors
open Matrix (GeneralLinearGroup)
open Algebra.TensorProduct (includeLeft includeLeftRingHom includeRight)
open LinearSystem (determinantInverse)

noncomputable section

open private determinantInverse_map matrixGeneratedSubalgebra_le_iff
  finiteType_of_matrixGenerated
  matrixGeneratedSubalgebra_of_fundamental fundamental_map
  matrixUnit_over_generatedSubalgebra from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTensor
open private mapGL_injective from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
open private constantsIn from MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor
open private intermediateSubring_structure from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing
open private range_eq_of_image_matrix injective_of_operatorSimple tensorHom_commutes
  matrixAutomorphism_eq from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
open private matrixGeneratedSubalgebra_map_eq_top relativeTensor_adjoin_eq_top
  from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.RelativePicardVessiotTensor

universe u v

set_option backward.isDefEq.respectTransparency false

private theorem semisimple_of_intermediateFieldStructure
    {kind : OperatorKind} {F : Type v} [CommRing F] (EF : Operator kind F)
    (hF : Specs.intermediateFieldStructure EF) : IsSemisimpleRing F := by
  cases kind with
  | differential =>
    let : Field F := IsField.toField hF
    exact show IsSemisimpleRing F from inferInstance
  | difference =>
    obtain ⟨ι, L, hL, hι, _, e, _⟩ := hF
    let := hL
    let := hι
    exact e.symm.isSemisimpleRing

/-- A splitting of the copy of the semisimple base in the right factor remains
a splitting after tensoring with any left factor. -/
private theorem tensorLeft_injective {F Q B : Type*}
    [CommRing F] [CommRing Q] [CommRing B] [Algebra F Q] [Algebra F B]
    [IsSemisimpleRing F] (hFB : Function.Injective (algebraMap F B)) :
    Function.Injective (includeLeftRingHom : Q →+* Q ⊗[F] B) := by
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property
    (Algebra.linearMap F B) hFB (LinearMap.id : F →ₗ[F] F)
  have hr1 : r 1 = 1 := by
    simpa using DFunLike.congr_fun hr (1 : F)
  have hs : Function.LeftInverse
      (fun t => TensorProduct.rid F Q (r.lTensor Q t))
      (includeLeftRingHom : Q →+* Q ⊗[F] B) := by
    intro q
    change TensorProduct.rid F Q (r.lTensor Q (q ⊗ₜ[F] (1 : B))) = q
    simp [hr1]
  exact hs.injective

set_option maxHeartbeats 1000000 in
private theorem specializeRelativeTensor {kind : OperatorKind}
    {K F Q B : Type*} [Field K] [CommRing F] [CommRing Q] [CommRing B]
    [Algebra K F] [Algebra K Q] [Algebra K B] [Algebra F Q] [Algebra F B]
    [IsScalarTower K F Q] [IsScalarTower K F B] [IsSemisimpleRing F] {n : ℕ}
    (δ : OperatorField kind K) {A : LinearSystem kind K n}
    {EF : Operator kind F} {T : Operator kind Q} {EB : Operator kind B}
    (hk : δ.IsBaseField) (hδQ : δ.IsExtension T) (hFQ : EF.IsAlgebra T)
    (hFB : EF.IsExtension EB) (hs : T.IsSimple)
    (hC : letI : Algebra δ.constantSubfield Q := Algebra.compHom Q δ.constantSubfield.subtype
          T.HasConstantField (C := δ.constantSubfield))
    {YQ : GL (Fin n) Q} {YB : GL (Fin n) B}
    (hYQ : A.IsFundamental T YQ) (hYB : A.IsFundamental EB YB)
    (hgen : matrixGeneratedSubalgebra F YB = ⊤) :
    ∃ (ψ : B →+* Q) (g : GL (Fin n) δ.constantSubfield),
      EB.Commutes T ψ ∧
      (∀ x : F, ψ (algebraMap F B x) = algebraMap F Q x) ∧
      GeneralLinearGroup.map ψ YB = YQ * GeneralLinearGroup.map (constantsIn δ) g := by
  let C := δ.constantSubfield
  let : IsAlgClosed C := hk.2
  let : Nontrivial Q := hs.1
  let : Algebra C Q := Algebra.compHom Q δ.constantSubfield.subtype
  let P := Q ⊗[F] B
  let : Algebra C P := Algebra.compHom P (algebraMap C Q)
  let : SMul C Q := Algebra.toSMul
  let : SMul C P := Algebra.toSMul
  let : IsScalarTower C Q P := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K P := Algebra.compHom P (algebraMap K F)
  let l : Q →ₐ[F] P := includeLeft
  let r : B →ₐ[F] P := includeRight
  let lK : Q →ₐ[K] P :=
    { l.toRingHom with
      commutes' := fun x => by
        change l (algebraMap K Q x) = algebraMap F P (algebraMap K F x)
        rw [IsScalarTower.algebraMap_apply K F Q, l.commutes] }
  let rK : B →ₐ[K] P :=
    { r.toRingHom with
      commutes' := fun x => by
        change r (algebraMap K B x) = algebraMap F P (algebraMap K F x)
        rw [IsScalarTower.algebraMap_apply K F B, r.commutes] }
  let EP := Operator.tensor hFQ hFB.1
  have hl : T.IsExtension EP :=
    ⟨Operator.tensor_commutes_includeLeft hFQ hFB.1, tensorLeft_injective hFB.2⟩
  have hr : EB.Commutes EP r := Operator.tensor_commutes_includeRight hFQ hFB.1
  let : Nontrivial P := hl.2.nontrivial
  let Y₁ := GeneralLinearGroup.map l.toRingHom YQ
  let Y₂ := GeneralLinearGroup.map r.toRingHom YB
  let Z := Specs.relativeTensorRatio F YQ YB
  have hYZ : Y₂ = Y₁ * Z := by
    change Y₂ = Y₁ * (Y₁⁻¹ * Y₂)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hδP : δ.IsExtension EP := by
    have heq : algebraMap K P = l.toRingHom.comp (algebraMap K Q) :=
      (RingHom.ext fun x => lK.commutes x).symm
    unfold Operator.IsExtension Operator.IsAlgebra
    rw [heq]
    exact ⟨hl.1.comp hδQ.1, hl.2.comp hδQ.2⟩
  obtain ⟨W, hW, _⟩ := A.fundamentalRightMultiplier δ hk EP hδP Y₁ Y₂
    (fundamental_map lK hl.1 hYQ)
    (fundamental_map rK hr hYB)
  have hZ : GeneralLinearGroup.map EP.constantSubring.subtype W = Z :=
    mul_left_cancel (hW.symm.trans hYZ)
  let D := matrixGeneratedSubalgebra C Z
  let S : Subalgebra C P :=
    { EP.constantSubring with
      algebraMap_mem' := fun c =>
        (Operator.mem_constantSubring EP _).mpr
          ((show T.Commutes EP l.toRingHom from hl.1).isConstant
            ((hC _).mpr ⟨c, rfl⟩)) }
  have hDS : D ≤ S := (matrixGeneratedSubalgebra_le_iff Z S).mpr (by
    rw [← hZ]
    refine ⟨fun i j => (W.val i j).property, ?_⟩
    rw [determinantInverse_map]
    exact (determinantInverse W).property)
  have hD (d : D) : EP.IsConstant (d : P) :=
    (Operator.mem_constantSubring EP _).mp (hDS d.property)
  let : Nontrivial D := inferInstance
  let : Algebra.FiniteType C D := Algebra.FiniteType.adjoin_of_finite
    ((Set.finite_range _).insert _)
  obtain ⟨f⟩ := existsAlgHom C D
  obtain ⟨ZD, hZD⟩ := matrixUnit_over_generatedSubalgebra (C := C) Z
  obtain ⟨U, hU, _⟩ := Operator.tensor_constant_existsUnique (R := C) (T := D) hC.isAlgebra
  obtain ⟨e, he⟩ := Operator.constantTensorMulIsEquiv D hs hC hl hU hD
    (relativeTensor_adjoin_eq_top (C := C) YQ YB hgen)
  change Operator kind (Q ⊗[C] D) at U
  change Operator.AlgEquiv Q U EP at e
  change e.val.toAlgHom = Operator.constantTensorMul D at he
  let q : Q ⊗[C] D →ₐ[Q] Q := Specs.evaluateConstantTensor f
  let m : P →ₐ[Q] Q := q.comp e.val.symm.toAlgHom
  have hq : U.Commutes T q := by
    apply tensorHom_commutes hU q.toRingHom
    · rw [show q.toRingHom.comp includeLeftRingHom = RingHom.id Q from
        RingHom.ext fun x => q.commutes x]
      intro x
      rfl
    · intro d
      let c := f d
      have hc : T.IsConstant (algebraMap C Q c) := (hC _).mpr ⟨c, rfl⟩
      change q (1 ⊗ₜ[C] Operator.trivial kind D d) = T (q (1 ⊗ₜ[C] d))
      simp only [q, Specs.evaluateConstantTensor, Algebra.TensorProduct.lift_tmul,
        AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply, one_mul]
      cases kind with
      | differential =>
        change T (algebraMap C Q c) = 0 at hc
        simp [Operator.trivial_differential_apply, hc, c]
      | difference => exact hc.symm
  have hm : EP.Commutes T m :=
    hq.comp (Operator.Commutes.inverse (f := e.val.toEquiv) e.property)
  have hml : m.toRingHom.comp l.toRingHom = RingHom.id Q :=
    RingHom.ext (fun x => m.commutes x)
  let ψ := m.toRingHom.comp r.toRingHom
  refine ⟨ψ, GeneralLinearGroup.map f.toRingHom ZD, hm.comp hr, ?_, ?_⟩
  · intro x
    change m (r (algebraMap F B x)) = algebraMap F Q x
    have h := congrArg (fun f : F →+* P => m (f x))
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := F) (A := Q) (B := B))
    exact h.symm.trans (m.commutes (algebraMap F Q x))
  · have hmd : m.toRingHom.comp D.val.toRingHom = (algebraMap C Q).comp f.toRingHom := by
      apply RingHom.ext
      intro d
      have hed : e.val ((1 : Q) ⊗ₜ[C] d) = (d : P) := by
        change e.val.toAlgHom ((1 : Q) ⊗ₜ[C] d) = (d : P)
        rw [he, Operator.constantTensorMul_tmul, map_one, one_mul]
      change m (d : P) = algebraMap C Q (f d)
      rw [← hed]
      change q (e.val.symm (e.val _)) = _
      rw [AlgEquiv.symm_apply_apply]
      simp [q, Specs.evaluateConstantTensor]
    have h := congrArg (GeneralLinearGroup.map m.toRingHom) hYZ
    rw [map_mul, ← hZD] at h
    change GeneralLinearGroup.map ψ YB =
      GeneralLinearGroup.map (m.toRingHom.comp l.toRingHom) YQ *
        GeneralLinearGroup.map (m.toRingHom.comp D.val.toRingHom) ZD at h
    rw [hml, hmd, GeneralLinearGroup.map_id, MonoidHom.id_apply] at h
    exact h

/-- A specialization with the indicated matrix image already induces an
automorphism of the original simple solution ring. -/
private theorem lift_of_specialization {kind : OperatorKind}
    {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    {δ : OperatorField kind K} {E : Operator kind R} {T : Operator kind (TotalQuotientRing R)}
    (Y : GL (Fin n) R) (hgen : matrixGeneratedSubalgebra K Y = ⊤)
    (hs : E.IsSimple) (hET : E.Commutes T (algebraMap R (TotalQuotientRing R))) :
    let Q := TotalQuotientRing R
    let : Algebra K Q := inferInstanceAs (Algebra K (FractionRing R))
    ∀ (j : R →ₐ[K] Q) (g : GL (Fin n) δ.constantSubfield), E.Commutes T j →
      GeneralLinearGroup.map j.toRingHom Y =
        GeneralLinearGroup.map (algebraMap R Q) Y * GeneralLinearGroup.map (constantsIn δ) g →
      ∃ a : matrixGaloisGroup δ E Y, ∀ r : R,
        matrixFractionAutomorphism δ E Y a (algebraMap R Q r) = j r := by
  intro Q _ j g hj hmat
  let : Nontrivial R := hs.1
  let i : R →ₐ[K] Q := { algebraMap R Q with commutes' := fun _ => rfl }
  have hi : Function.Injective i := IsFractionRing.injective R Q
  let gK := GeneralLinearGroup.map δ.constantSubfield.subtype g
  have hrange : j.range = i.range := range_eq_of_image_matrix hgen j i gK hmat
  let a := AlgEquiv.ofInjective j
    (injective_of_operatorSimple hs j.toRingHom hj)
  let b := AlgEquiv.ofInjective i hi
  let τ := a.trans ((Subalgebra.equivOfEq _ _ hrange).trans b.symm)
  have hτ (r : R) : i (τ r) = j r := by
    exact congrArg Subtype.val (b.apply_symm_apply (Subalgebra.equivOfEq _ _ hrange (a r)))
  have hτop : E.Commutes E τ := by
    intro r
    apply hi
    calc
      i (τ (E r)) = j (E r) := hτ _
      _ = T (j r) := hj r
      _ = T (i (τ r)) := congrArg T (hτ r).symm
      _ = i (E (τ r)) := (hET (τ r)).symm
  have hτmat : GeneralLinearGroup.map τ.toRingHom Y =
      Y * GeneralLinearGroup.map (constantsIn δ) g := by
    apply mapGL_injective i.toRingHom hi
    rw [map_mul]
    change GeneralLinearGroup.map (i.toRingHom.comp τ.toRingHom) Y =
      GeneralLinearGroup.map i.toRingHom Y *
        GeneralLinearGroup.map (i.toRingHom.comp (constantsIn δ)) g
    rw [show i.toRingHom.comp τ.toRingHom = j.toRingHom from RingHom.ext hτ]
    exact hmat
  let G := matrixGaloisGroup δ E Y
  let aG : G := ⟨g, ⟨⟨τ, hτop⟩, hτmat⟩⟩
  have ha : matrixAutomorphism δ E Y aG = ⟨τ, hτop⟩ :=
    (matrixAutomorphism_eq Y hgen aG _).2 hτmat
  refine ⟨aG, fun r => ?_⟩
  change Operator.fractionRingEquiv (matrixAutomorphism δ E Y aG).val.toRingEquiv
      (algebraMap R Q r) = j r
  rw [ha, Operator.fractionRingEquiv_algebraMap]
  exact hτ r

private theorem agree_on_intermediate {R B Q : Type*}
    [CommRing R] [CommRing B] [CommRing Q] [Algebra R Q] [IsFractionRing R Q] [Algebra B Q]
    (i : R →+* B) (hi : ∀ r, algebraMap B Q (i r) = algebraMap R Q r)
    (hB : Function.Injective (algebraMap B Q)) (ψ : B →+* Q) (a : Q ≃+* Q)
    (ha : ∀ r, a (algebraMap R Q r) = ψ (i r)) (b : B) :
    a (algebraMap B Q b) = ψ b := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj R⁰ (algebraMap B Q b)
  have hb : b * i (s : R) = i r := by
    apply hB
    rw [map_mul, hi, hi]
    exact hrs
  apply ((IsLocalization.map_units Q s).map a.toRingHom).mul_right_cancel
  change a (algebraMap B Q b) * a (algebraMap R Q (s : R)) =
    ψ b * a (algebraMap R Q (s : R))
  rw [← map_mul, hrs, ha, ha, ← map_mul, hb]

set_option maxHeartbeats 1000000 in
/-- An automorphism of an intermediate total ring extends by specializing the
tensor whose left structure map is twisted by that automorphism. -/
theorem intermediateAutomorphismLift : Specs.intermediateAutomorphismLift.{u, v} := by
  intro kind K R _ _ _ n δ A E T Y hk hpv hY
  change OperatorField kind K at δ
  change Operator kind R at E
  change LinearSystem kind K n at A
  change Operator kind (TotalQuotientRing R) at T
  change δ.IsBaseField at hk
  change IsPicardVessiotTotalExtension δ A E T at hpv
  change A.IsFundamental E Y at hY
  let Q := TotalQuotientRing R
  let : Algebra K Q := inferInstanceAs (Algebra K (FractionRing R))
  let : SMul K Q := Algebra.toSMul
  let : SMul R Q := Algebra.toSMul
  let : IsScalarTower K R Q := IsScalarTower.of_algebraMap_eq' rfl
  have hAlg : inferInstanceAs (Algebra K (FractionRing R)) =
      Algebra.compHom Q (algebraMap K R) := by
    apply Algebra.algebra_ext
    intro k
    rfl
  dsimp only
  rw [← hAlg]
  intro F hF EF hEF τ
  let : CommRing (F : Type v) := Subalgebra.toCommRing F
  change Operator kind (F : Type v) at EF
  change EF.IsAlgebra T at hEF
  change operatorAutomorphisms K EF at τ
  let YQ := GeneralLinearGroup.map (algebraMap R Q) Y
  let B := relativePicardVessiotSubalgebra F YQ
  let : CommRing (B : Type v) := Subalgebra.toCommRing B
  obtain ⟨EF', EB, _, i, hFT, hFB, _, hEB, hi, _, _, _, hs, _⟩ :=
    relativePicardVessiotTensor δ A E T Y hk hpv hY F hF
  change T.IsSimple at hs
  change Operator kind (F : Type v) at EF'
  change Operator kind (B : Type v) at EB
  change R →+* B at i
  change EF'.IsExtension T at hFT
  change EF'.IsExtension EB at hFB
  change E.Commutes EB i at hEB
  change ∀ r, (i r : Q) = algebraMap R Q r at hi
  let : Algebra K B := Algebra.compHom B (algebraMap K F)
  let : IsScalarTower K F B := IsScalarTower.of_algebraMap_eq' rfl
  let iK : R →ₐ[K] B :=
    { i with
      commutes' := fun x => Subtype.ext (hi (algebraMap K R x)) }
  let YB : GL (Fin n) B := GeneralLinearGroup.map (S := (B : Type v)) i Y
  have hYBQ : GeneralLinearGroup.map B.val.toRingHom YB = YQ := by
    change GeneralLinearGroup.map (B.val.toRingHom.comp i) Y = _
    rw [show B.val.toRingHom.comp i = algebraMap R Q from RingHom.ext hi]
  have hgenB : matrixGeneratedSubalgebra (F : Type v) YB = ⊤ :=
    matrixGeneratedSubalgebra_map_eq_top rfl hYBQ
  have hgen := matrixGeneratedSubalgebra_of_fundamental hk hpv.1 Y hY
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y hgen
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  let : CharZero K := hk.1
  have hFstructure : T.IsStable (F : Set Q) ∧
      ProjectionKernels.RegularElementsAreUnits (F : Type v) := hF
  obtain ⟨_, hFfield⟩ := intermediateSubring_structure (k := K) hpv.1.2.1 hpv.2.1
    F.toSubring hFstructure.1 hFstructure.2
  let : IsSemisimpleRing (F : Type v) := semisimple_of_intermediateFieldStructure _ hFfield
  have hδQ : δ.IsExtension T :=
    ⟨hpv.2.1.comp hpv.1.1.1, hpv.2.2.comp hpv.1.1.2⟩
  have hTYQ : A.IsFundamental T YQ :=
    fundamental_map (IsScalarTower.toAlgHom K R Q) hpv.2.1 hY
  have hEBYB : A.IsFundamental EB YB := fundamental_map iK hEB hY
  let : Algebra δ.constantSubfield Q := Algebra.compHom Q δ.constantSubfield.subtype
  have hconst : T.HasConstantField (C := δ.constantSubfield) := by
    let cMap := Operator.RingHom.mapConstants (D := δ) (E := T) ⟨algebraMap K Q, hδQ.1⟩
    have hcMap : Function.Bijective cMap :=
      Operator.constants_finiteType_fractionRing δ E T hk hpv.1.2.1 hpv.1.1.1 hpv.2.1
    intro q
    constructor
    · intro hq
      obtain ⟨c, hc⟩ := hcMap.2 ⟨q, (Operator.mem_constantSubring T q).mpr hq⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    · rintro ⟨c, rfl⟩
      exact (Operator.mem_constantSubring T _).mp (cMap c).property
  have hτ : EF'.Commutes EF' τ.val := by
    have heq (x : F) : EF' x = EF x := Subtype.ext ((hFT.1 x).trans (hEF x).symm)
    intro x
    rw [heq, heq]
    exact τ.property x
  have hspec :
      ∃ (ψ : B →+* Q) (g : GL (Fin n) δ.constantSubfield),
        EB.Commutes T ψ ∧ (∀ x : F, ψ (algebraMap (F : Type v) B x) = (τ.val x : Q)) ∧
        GeneralLinearGroup.map ψ YB = YQ * GeneralLinearGroup.map (constantsIn δ) g := by
    let twisted : (F : Type v) →+* Q := (algebraMap (F : Type v) Q).comp τ.val.toRingHom
    let : Algebra (F : Type v) Q := twisted.toAlgebra
    let : SMul (F : Type v) Q := Algebra.toSMul
    let : IsScalarTower K (F : Type v) Q := IsScalarTower.of_algebraMap_eq fun x =>
      (congrArg Subtype.val (τ.val.commutes x)).symm
    have htwist : EF'.IsAlgebra T := hFT.1.comp hτ
    exact specializeRelativeTensor δ hk hδQ htwist hFB hs hconst hTYQ hEBYB hgenB
  obtain ⟨ψ, g, hψ, hψF, hψmat⟩ := hspec
  let j : R →ₐ[K] Q :=
    { ψ.comp i with
      commutes' := fun x => by
        change ψ (iK (algebraMap K R x)) = algebraMap K Q x
        rw [iK.commutes x]
        change ψ (algebraMap (F : Type v) B (algebraMap K F x)) = _
        rw [hψF, τ.val.commutes]
        rfl }
  obtain ⟨a, ha⟩ := lift_of_specialization Y hgen hpv.1.2.1 hpv.2.1 j g
    (hψ.comp hEB) hψmat
  refine ⟨a, fun x => ?_⟩
  have h := agree_on_intermediate i hi Subtype.val_injective ψ
    (matrixFractionAutomorphism δ E Y a) ha (algebraMap (F : Type v) B x)
  exact h.trans (hψF x)

end

end GaloisFormalization.PV
