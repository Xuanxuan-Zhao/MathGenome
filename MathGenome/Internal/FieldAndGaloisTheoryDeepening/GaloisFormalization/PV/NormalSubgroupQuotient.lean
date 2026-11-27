import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateAutomorphismLift
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.NormalSubgroupRealization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.NormalSubgroupQuotient

import Batteries.Tactic.OpenPrivate
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The normal subgroup criterion and quotient for Picard–Vessiot extensions. -/

namespace GaloisFormalization.PV

open scoped Matrix MatrixGroupCoordinates.Specs nonZeroDivisors
open Matrix (GeneralLinearGroup)
open MatrixGroupCoordinates.Specs (IsRegularRepresentation)

open private baseConstantMultiplier range_eq_of_image_matrix matrixAutomorphism_spec
  mapGL_injective from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
open private constantsIn from MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor
open private finiteType_of_generatedByMatrix restrictOperator restrictOperator_commutes
  from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing
open private fundamental_map from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotUniqueness

universe u v w

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Use the canonical localization algebra for the action on the total ring. -/
private theorem totalRingAction {kind : OperatorKind} {K R : Type*}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : OperatorField kind K) (A : LinearSystem kind K n)
    (E : Operator kind R) (T : Operator kind (TotalQuotientRing R)) (Y : GL (Fin n) R)
    (hbase : δ.IsBaseField) (hpv : IsPicardVessiotTotalExtension δ A E T)
    (hY : A.IsFundamental E Y) :
    ∃ α : matrixGaloisGroup δ E Y ≃* operatorAutomorphisms K T,
      ∀ g, (α g).val.toRingEquiv = matrixFractionAutomorphism δ E Y g := by
  have hAlg : inferInstanceAs (Algebra K (TotalQuotientRing R)) =
      Algebra.compHom (TotalQuotientRing R) (algebraMap K R) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have h := galoisTotalRingAction δ A E Y T hbase hpv.1 hY hpv.2.1
  dsimp only at h
  rw [← hAlg] at h
  obtain ⟨α, hα, _⟩ := h
  exact ⟨α, hα⟩

/-- Normality amounts to invariance of the fixed ring under every element of the group. -/
theorem fixedSubalgebraStableIffNormal : Specs.fixedSubalgebraStableIffNormal.{u, v} := by
  intro kind K R _ _ _ n δ A E T Y hbase hpv hY G H hclosed F
  let Q := TotalQuotientRing R
  let act : G → Q ≃+* Q := matrixFractionAutomorphism δ E Y
  obtain ⟨_, ⟨o, ho, hos⟩, _, _⟩ :=
    operatorGaloisCorrespondence δ A E T Y hbase hpv hY
  obtain ⟨α, hα, _⟩ := galoisTotalRingAction δ A E Y T hbase hpv.1 hY hpv.2.1
  have hαapply (g : G) (x : Q) : (α g).val x = act g x :=
    congrArg (fun τ : Q ≃+* Q => τ x) (hα g)
  have hmul (g h : G) (x : Q) : act (g * h) x = act g (act h x) := by
    rw [← hαapply, map_mul]
    change (α g).val ((α h).val x) = _
    rw [hαapply, hαapply]
  have hone (x : Q) : act 1 x = x := by
    rw [← hαapply, map_one]
    rfl
  have hstab : Specs.relativeStabilizer δ E Y F = (H : Set G) := by
    let Hc : {L : Subgroup G // IsClosed (L : Set G)} := ⟨H, hclosed⟩
    have h := hos (OrderDual.ofDual (o Hc))
    rw [OrderDual.toDual_ofDual, o.symm_apply_apply, ho Hc] at h
    exact h.symm
  change (∀ (g : G) (x : F), act g (x : Q) ∈ F) ↔ H.Normal
  constructor
  · intro hstable
    constructor
    intro h hh g
    change g * h * g⁻¹ ∈ (H : Set G)
    rw [← hstab]
    intro x
    change act (g * h * g⁻¹) (x : Q) = (x : Q)
    have hx : act h (act g⁻¹ (x : Q)) = act g⁻¹ (x : Q) :=
      (hstable g⁻¹ x) h hh
    rw [hmul, hmul, hx, ← hmul, mul_inv_cancel, hone]
  · intro hnormal g x h hh
    change act h (act g (x : Q)) = act g (x : Q)
    have hconj := hnormal.conj_mem h hh g⁻¹
    rw [inv_inv] at hconj
    have hx : act (g⁻¹ * h * g) (x : Q) = (x : Q) := x.property _ hconj
    have hgroup : h * g = g * (g⁻¹ * h * g) := by simp [← mul_assoc]
    rw [← hmul, hgroup, hmul, hx]

/-- Restrict a group action by operator automorphisms to a stable operator subalgebra. -/
private def restrictAutomorphismAction {kind : OperatorKind} {K Q G : Type*}
    [Field K] [CommRing Q] [Algebra K Q] [Group G]
    {T : Operator kind Q} {F : Subalgebra K Q} {EF : Operator kind F}
    (hEF : EF.Commutes T F.val) (α : G →* operatorAutomorphisms K T)
    (hstable : ∀ (g : G) (x : F), (α g).val (x : Q) ∈ F) :
    G →* operatorAutomorphisms K EF := by
  let f (g : G) : F →ₐ[K] F := ((α g).val.toAlgHom.comp F.val).codRestrict F (hstable g)
  have hcancel (g : G) : (f g).comp (f g⁻¹) = AlgHom.id K F := by
    apply AlgHom.ext
    intro x
    apply Subtype.val_injective
    change (α g).val ((α g⁻¹).val (x : Q)) = (x : Q)
    rw [← AlgEquiv.mul_apply]
    change (α g * α g⁻¹).val (x : Q) = (x : Q)
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  let e (g : G) : F ≃ₐ[K] F :=
    AlgEquiv.ofAlgHom (f g) (f g⁻¹) (hcancel g) (by simpa only [inv_inv] using hcancel g⁻¹)
  have he (g : G) (x : F) : (e g x : Q) = (α g).val (x : Q) := rfl
  have hEFapply (x : F) : (EF x : Q) = T (x : Q) := hEF x
  have hcomm (g : G) : EF.Commutes EF (e g) := by
    intro x
    apply Subtype.val_injective
    have hg : (α g).val (T (x : Q)) = T ((α g).val (x : Q)) :=
      (α g).property (x : Q)
    rw [he, hEFapply, hg, hEFapply, he]
  refine { toFun := fun g => ⟨e g, hcomm g⟩, map_one' := ?_, map_mul' := ?_ }
  · apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    change (e 1 x : Q) = (x : Q)
    rw [he, map_one]
    rfl
  · intro g h
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    change (e (g * h) x : Q) = (e g (e h x) : Q)
    rw [he, he, he, map_mul]
    rfl

private theorem conjugation_commutes {kind : OperatorKind} {K R S : Type*}
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {D : Operator kind R} {E : Operator kind S}
    (j : R ≃ₐ[K] S) (hj : D.Commutes E j) {τ : R ≃ₐ[K] R} (hτ : D.Commutes D τ) :
    E.Commutes E (j.autCongr τ) := by
  have happ (x : R) : j.autCongr τ (j x) = j (τ x) := by
    change j (τ (j.symm (j x))) = _
    rw [j.symm_apply_apply]
  intro y
  obtain ⟨x, rfl⟩ := j.surjective y
  rw [← hj x, happ, happ, hτ x, hj (τ x)]

/-- Conjugating by an operator algebra isomorphism identifies the automorphism groups. -/
private def operatorAutomorphismsCongr {kind : OperatorKind} {K R S : Type*}
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {D : Operator kind R} {E : Operator kind S}
    (j : R ≃ₐ[K] S) (hj : D.Commutes E j) :
    operatorAutomorphisms K D ≃* operatorAutomorphisms K E := by
  have h : (operatorAutomorphisms K D).map (j.autCongr.toMonoidHom) =
      operatorAutomorphisms K E := by
    ext τ
    constructor
    · rintro ⟨υ, hυ, rfl⟩
      exact conjugation_commutes j hj hυ
    · intro hτ
      exact ⟨(j.autCongr).symm τ,
        conjugation_commutes j.symm (Operator.Commutes.inverse (f := j.toEquiv) hj) hτ,
        (j.autCongr).apply_symm_apply τ⟩
  exact (j.autCongr.subgroupMap (operatorAutomorphisms K D)).trans (MulEquiv.subgroupCongr h)

set_option maxHeartbeats 800000 in
/-- The regular restriction map induces the quotient isomorphism on points. -/
theorem normalSubgroupQuotient : Specs.normalSubgroupQuotient.{u, v} := by
  intro kind K R _ _ _ n δ A E T Y hbase hpv hY Q G H hclosed hnormal F
  let : H.Normal := hnormal
  change OperatorField kind K at δ
  change LinearSystem kind K n at A
  change Operator kind R at E
  change Operator kind Q at T
  change IsPicardVessiotTotalExtension δ A E T at hpv
  obtain ⟨hfixed, _⟩ := operatorGaloisCorrespondence δ A E T Y hbase hpv hY
  have hF : Specs.isIntermediateTotalRing T F := hfixed H
  obtain ⟨m, ρ, A', W, hρ, _, _, D, U, X, i, hBpv, hX, hXfund, hXgen,
    _, hi, hicomm, hibase, hirange, histab, hcov⟩ :=
    normalSubgroupRealization δ A E T Y hbase hpv hY H hclosed hnormal
  let WQ := GeneralLinearGroup.map (algebraMap R Q) W
  let B := matrixGeneratedSubalgebra K WQ
  change LinearSystem kind K m at A'
  change Operator kind B at D
  change Operator kind (TotalQuotientRing B) at U
  change GL (Fin m) B at X
  change i.range = F at hirange
  have hXB : GeneralLinearGroup.map B.val.toRingHom X = WQ := hX
  have hiB (x : B) : i (algebraMap B (TotalQuotientRing B) x) = (x : Q) :=
    hibase x
  let j : TotalQuotientRing B ≃ₐ[K] F :=
    (AlgEquiv.ofInjective i hi).trans (Subalgebra.equivOfEq _ _ hirange)
  have hj (z : TotalQuotientRing B) : (j z : Q) = i z := rfl
  let EF : Operator kind F := restrictOperator T F.toSubring hF.1
  have hEF : EF.IsAlgebra T := restrictOperator_commutes T F.toSubring hF.1
  have hEFapply (x : F) : (EF x : Q) = T (x : Q) := hEF x
  have hjcomm : U.Commutes EF j := by
    intro z
    apply Subtype.val_injective
    rw [hj, hEFapply, hj]
    exact hicomm z
  obtain ⟨α, hα⟩ := totalRingAction δ A E T Y hbase hpv hY
  have hαapply (g : G) (x : Q) :
      (α g).val x = matrixFractionAutomorphism δ E Y g x :=
    congrArg (fun τ : Q ≃+* Q => τ x) (hα g)
  have hstable := (fixedSubalgebraStableIffNormal δ A E T Y hbase hpv hY H hclosed).mpr hnormal
  let res : G →* operatorAutomorphisms K EF :=
    restrictAutomorphismAction hEF α.toMonoidHom (fun g x => by
      change (α g).val (x : Q) ∈ F
      rw [hαapply]
      exact hstable g x)
  have hres (g : G) (x : F) :
      ((res g).val x : Q) = matrixFractionAutomorphism δ E Y g (x : Q) :=
    hαapply g x
  have hker : res.ker = H := by
    have hstab : Specs.relativeStabilizer δ E Y F = (H : Set G) := by
      rw [← hirange]
      exact histab
    ext g
    rw [MonoidHom.mem_ker, ← SetLike.mem_coe, ← hstab]
    constructor
    · intro hg x
      rw [← hres, hg]
      rfl
    · intro hg
      apply Subtype.ext
      apply AlgEquiv.ext
      intro x
      apply Subtype.val_injective
      exact (hres g x).trans (hg x)
  have hsurj : Function.Surjective res := by
    intro τ
    have hAlg : inferInstanceAs (Algebra K (TotalQuotientRing R)) =
        Algebra.compHom Q (algebraMap K R) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    have hlift := intermediateAutomorphismLift δ A E T Y hbase hpv hY
    dsimp only at hlift
    rw [← hAlg] at hlift
    obtain ⟨g, hg⟩ := hlift F hF EF hEF τ
    refine ⟨g, Subtype.ext ?_⟩
    apply AlgEquiv.ext
    intro x
    exact Subtype.ext ((hres g x).trans (hg x))
  let e : G ⧸ H ≃* operatorAutomorphisms K EF :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective res hsurj)
  have he (g : G) : e (QuotientGroup.mk' H g) = res g := by
    change QuotientGroup.kerLift res
      (QuotientGroup.quotientMulEquivOfEq hker.symm (QuotientGroup.mk g)) = res g
    rw [QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]
  let G' := matrixGaloisGroup δ D X
  obtain ⟨β, hβ⟩ := totalRingAction δ A' D U X hbase hBpv hXfund
  let φ : G' ≃* operatorAutomorphisms K EF := β.trans (operatorAutomorphismsCongr j hjcomm)
  have hφ (r : G') (z : TotalQuotientRing B) :
      (φ r).val (j z) = j (matrixFractionAutomorphism δ D X r z) := by
    change j ((β r).val (j.symm (j z))) = _
    rw [j.symm_apply_apply]
    exact congrArg j (congrArg (fun τ : TotalQuotientRing B ≃+* TotalQuotientRing B => τ z) (hβ r))
  refine ⟨m, A', B, D, U, X, EF, j, hBpv, hXfund, hXgen, hEF, hjcomm,
    fun b => (hj _).trans (hiB b), e, φ, fun g x => ?_, hφ, ?_⟩
  · rw [he, hres]
  · let π := G'.subtype.comp
        (φ.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' H)))
    change IsRegularRepresentation π
    suffices π = ρ by rw [this]; exact hρ
    ext g : 1
    let r : G' := φ.symm (res g)
    change (φ.symm (e (QuotientGroup.mk' H g))).val = ρ g
    rw [he]
    change r.val = ρ g
    let a := (matrixFractionAutomorphism δ E Y g).toRingHom
    let b := (matrixAutomorphism δ D X r).val.toRingHom
    have hr (z : TotalQuotientRing B) : a (i z) = i (matrixFractionAutomorphism δ D X r z) := by
      rw [← hj, ← hj]
      exact ((hres g (j z)).symm.trans
        (congrArg Subtype.val (show (res g).val (j z) = _ by
          rw [← φ.apply_symm_apply (res g)]
          exact hφ r z)))
    have hmaps : a.comp B.val.toRingHom = B.val.toRingHom.comp b := by
      ext x
      change a (x : Q) = (b x : Q)
      have hx := hr (algebraMap B (TotalQuotientRing B) x)
      have hx' : matrixFractionAutomorphism δ D X r
          (algebraMap B (TotalQuotientRing B) x) =
          algebraMap B (TotalQuotientRing B) (b x) :=
        IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
      rw [hx'] at hx
      simpa only [hiB] using hx
    have hmatrix : GeneralLinearGroup.map a WQ =
        WQ * GeneralLinearGroup.map (constantsIn δ (R := Q)) r.val := by
      rw [← hXB]
      change GeneralLinearGroup.map (a.comp B.val.toRingHom) X = _
      rw [hmaps]
      change GeneralLinearGroup.map B.val.toRingHom (GeneralLinearGroup.map b X) = _
      rw [show GeneralLinearGroup.map b X = X *
          GeneralLinearGroup.map (constantsIn δ (R := B)) r.val from matrixAutomorphism_spec X r,
        map_mul]
      rfl
    have hδQ : δ.IsExtension T := IsPicardVessiotTotalExtension.isExtension
      (A := A) (E := E) hpv
    apply mapGL_injective (constantsIn δ (R := Q)) (hδQ.2.comp Subtype.val_injective)
    exact mul_left_cancel (hmatrix.symm.trans (hcov g))

set_option maxHeartbeats 650000 in
/-- Any embedded Picard–Vessiot total extension over the base is Galois-stable. -/
theorem picardVessiotTotalSubextensionStable :
    Specs.picardVessiotTotalSubextensionStable.{u, v, w} := by
  intro kind K R _ _ _ n δ A E T Y hbase hpv hY Q F _ B _ _ m A' D U j
    hBpv hj hjcomm hrange g x
  change OperatorField kind K at δ
  change LinearSystem kind K n at A
  change LinearSystem kind K m at A'
  change Operator kind R at E
  change Operator kind Q at T
  change Operator kind B at D
  change Operator kind (TotalQuotientRing B) at U
  change IsPicardVessiotTotalExtension δ A E T at hpv
  change IsPicardVessiotTotalExtension δ A' D U at hBpv
  obtain ⟨Y₀, _, hgen⟩ := hpv.1.2.2
  let : Algebra.FiniteType K R := finiteType_of_generatedByMatrix hgen
  have hδQ := hpv.isExtension
  have hC := Operator.constants_finiteType_fractionRing δ E T hbase hpv.1.2.1 hpv.1.1.1 hpv.2.1
  obtain ⟨α, hα⟩ := totalRingAction δ A E T Y hbase hpv hY
  let τ : Q ≃ₐ[K] Q := (α g).val
  have hτ : T.Commutes T τ := (α g).property
  obtain ⟨X, hX, hXgen⟩ := hBpv.1.2.2
  let i : B →ₐ[K] TotalQuotientRing B := IsScalarTower.toAlgHom K B _
  let f := j.comp i
  let f' := τ.toAlgHom.comp f
  have hf : D.Commutes T f :=
    Operator.Commutes.comp (f := i) (g := j) hjcomm hBpv.2.1
  have hi : Function.Injective i := hBpv.2.2
  let W := GeneralLinearGroup.map f.toRingHom X
  have hW : A'.IsFundamental T W := fundamental_map hX f hf
  obtain ⟨b, hb⟩ := baseConstantMultiplier hbase hδQ hC hW
    (fundamental_map hW τ.toAlgHom hτ)
  let bK := GeneralLinearGroup.map (Specs.constantSubfield δ).subtype b
  have hfg : f'.range = f.range := range_eq_of_image_matrix hXgen f' f bK hb
  let q := (AlgEquiv.ofInjective f' (τ.injective.comp (hj.comp hi))).trans
    ((Subalgebra.equivOfEq _ _ hfg).trans (AlgEquiv.ofInjective f (hj.comp hi)).symm)
  have hq (y : B) : f (q y) = f' y := by
    exact congrArg Subtype.val ((AlgEquiv.ofInjective f (hj.comp hi)).apply_symm_apply _)
  let qFrac : TotalQuotientRing B ≃ₐ[K] TotalQuotientRing B :=
    IsFractionRing.algEquivOfAlgEquiv q
  have hcomp : τ.toRingHom.comp j.toRingHom = j.toRingHom.comp qFrac.toRingHom := by
    apply IsLocalization.ringHom_ext B⁰
    ext y
    change τ (j (i y)) = j (qFrac (algebraMap B (TotalQuotientRing B) y))
    rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    exact (hq y).symm
  obtain ⟨z, hz⟩ : (x : Q) ∈ j.range := hrange.symm ▸ x.property
  change matrixFractionAutomorphism δ E Y g (x : Q) ∈ F
  rw [← hα g, ← hz, ← hrange]
  exact ⟨qFrac z, (RingHom.congr_fun hcomp z).symm⟩

end
end GaloisFormalization.PV
