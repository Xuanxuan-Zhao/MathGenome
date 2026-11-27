import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.ClosedSubgroupRepresentations
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.DescendedRepresentationMatrix
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorGaloisCorrespondence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotUniqueness
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.TransitiveProductProjectionKernels
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.NormalSubgroupRealization

namespace GaloisFormalization.PV

open scoped Matrix MatrixGroupCoordinates.Specs nonZeroDivisors
open Matrix (GeneralLinearGroup)

open private finiteType_of_generatedByMatrix stable_range_of_commutes from
  MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing
open private determinantInverse_map matrixGeneratedSubalgebra_le_iff fundamental_map from
  MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotUniqueness
open private mapGL_injective from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
open private mapGL_comp from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.DescendedRepresentationMatrix

universe u v

/-- Regular elements of a stable subring avoid every field factor of the total ring. -/
private theorem regular_subring_elements_are_units
    {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CharZero K] [CommRing R] [Algebra K R] [IsNoetherianRing R]
    {E : Operator kind R} {T : Operator kind (TotalQuotientRing R)}
    (hE : E.IsSimple) (hET : E.IsAlgebra T) (S : Subring (TotalQuotientRing R))
    (hS : T.IsStable (S : Set (TotalQuotientRing R))) :
    ∀ x : S, x ∈ (S : Type v)⁰ → IsUnit (x : TotalQuotientRing R) := by
  let Q := TotalQuotientRing R
  classical
  cases kind with
  | differential =>
    let : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ K)
    let : Field Q := ((Operator.simpleDifferentialFractionField (K := Q) E hE).2).toField
    let : Nontrivial S := ⟨⟨0, 1, fun h => zero_ne_one (congrArg S.subtype h)⟩⟩
    intro x hx
    exact isUnit_iff_ne_zero.mpr (map_ne_zero_of_mem_nonZeroDivisors S.subtype
      Subtype.val_injective hx)
  | difference =>
    obtain ⟨hfin, hne, _, hQ, _, p, f, e, _, htrans, _, _, _, he⟩ :=
      simpleDifferenceFractionComponents E.toRingEquiv T.toRingEquiv hE hET
    let := hfin
    let := hne
    let L (i : minimalPrimes R) := FractionRing (R ⧸ i.val)
    let : ∀ i, Field (L i) := fun i => (hQ i).toField
    let σ := e.symm.trans (T.toRingEquiv.trans e)
    let S' := S.map e.toRingHom
    have hfwd (x : Q) : σ (e x) = e (T.toRingEquiv x) := by
      change e (T.toRingEquiv (e.symm (e x))) = _
      rw [e.symm_apply_apply]
    have hbwd (x : Q) : σ.symm (e x) = e (T.toRingEquiv.symm x) :=
      σ.injective (by rw [σ.apply_symm_apply, hfwd, T.toRingEquiv.apply_symm_apply])
    have hS' : (Operator.difference σ).IsStable (S' : Set (∀ i, L i)) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨T.toRingEquiv x, hS.1 hx, (hfwd x).symm⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨T.toRingEquiv.symm x, hS.2 hx, (hbwd x).symm⟩
    have hσ : ProjectionKernels.PermutesFactors σ p := by
      intro q i
      obtain ⟨x, rfl⟩ := e.surjective q
      rw [hfwd, he]
      exact map_eq_zero_iff _ (Operator.fractionRingEquiv (f i)).injective
    have hp : ProjectionKernels.Transitive p := by
      intro i j
      obtain ⟨m, hm⟩ := (show Equiv.Perm.SameCycle p i j from htrans i j).exists_nat_pow_eq
      exact ⟨m, by rwa [p.iterate_eq_pow]⟩
    let eS := S.equivMapOfInjective e.toRingHom e.injective
    intro x hx
    have hx' := (Operator.ringEquiv_mem_nonZeroDivisors_iff eS x).mpr hx
    have hu := (ProjectionKernels.mem_nonZeroDivisors_iff_isUnit σ p hσ hp
      ⟨S', hS'⟩ (eS x)).mp hx'
    have hinv : IsUnit (e.symm (e (x : Q))) := hu.map e.symm.toRingHom
    rwa [e.symm_apply_apply] at hinv

/-- Commutation on the original ring extends to fractions by clearing a unit denominator. -/
private theorem commutes_on_fraction_ring {kind : OperatorKind} {B Q : Type v}
    [CommRing B] [CommRing Q] {D : Operator kind B} {T : Operator kind Q}
    (j : TotalQuotientRing B →+* Q)
    (h : D.Commutes T (j.comp (algebraMap B (TotalQuotientRing B)))) :
    D.totalQuotient.Commutes T j := by
  let U := D.totalQuotient
  let i := algebraMap B (TotalQuotientRing B)
  have hi : D.Commutes U i := D.fractionOperator_commutes
  have hj (x : B) : j (i (D x)) = T (j (i x)) := h x
  intro q
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq B⁰ q
  let r := IsLocalization.mk' (TotalQuotientRing B) a b
  have hr : i b * r = i a := IsLocalization.mk'_spec' _ _ _
  have hjr : j (i b) * j r = j (i a) := by rw [← map_mul, hr]
  have hb : IsUnit (j (i b)) := (IsLocalization.map_units (TotalQuotientRing B) b).map j
  change j (U r) = T (j r)
  cases kind with
  | differential =>
    have hl := congrArg (fun x => j (U x)) hr
    have hh := congrArg T.apply hjr
    change j (U.toDerivation (i b * r)) = j (U.toDerivation (i a)) at hl
    change T.toDerivation (j (i b) * j r) = T.toDerivation (j (i a)) at hh
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul] at hl
    simp only [Derivation.leibniz, smul_eq_mul] at hh
    change j (i b) * j (U r) + j r * j (U (i b)) = j (U (i a)) at hl
    change j (i b) * T (j r) + j r * T (j (i b)) = T (j (i a)) at hh
    rw [← hi b, ← hi a, hj b, hj a] at hl
    exact hb.mul_left_cancel (add_right_cancel (hl.trans hh.symm))
  | difference =>
    have hl := congrArg (fun x => j (U x)) hr
    have hh := congrArg T.apply hjr
    change j (U.toRingEquiv (i b * r)) = j (U.toRingEquiv (i a)) at hl
    change T.toRingEquiv (j (i b) * j r) = T.toRingEquiv (j (i a)) at hh
    rw [map_mul, map_mul] at hl
    rw [map_mul] at hh
    change j (U (i b)) * j (U r) = j (U (i a)) at hl
    change T (j (i b)) * T (j r) = T (j (i a)) at hh
    rw [← hi b, ← hi a, hj b, hj a] at hl
    exact (hb.map T.toRingEquiv.toRingHom).mul_left_cancel (hl.trans hh.symm)

private theorem fraction_image_is_intermediate {kind : OperatorKind} {K : Type u}
    {B Q : Type v} [Field K] [CommRing B] [CommRing Q] [Algebra K B] [Algebra K Q]
    {U : Operator kind (TotalQuotientRing B)} {T : Operator kind Q}
    (j : TotalQuotientRing B →ₐ[K] Q) (hj : Function.Injective j)
    (h : U.Commutes T j) : Specs.isIntermediateTotalRing T j.range := by
  constructor
  · exact stable_range_of_commutes (f := j.toRingHom) h
  · let e := (AlgEquiv.ofInjective j hj).toRingEquiv
    intro x hx
    obtain ⟨r, rfl⟩ := e.surjective x
    have hr := (Operator.ringEquiv_mem_nonZeroDivisors_iff e r).mp hx
    rw [IsFractionRing.nonZeroDivisors_eq_isUnit B (TotalQuotientRing B)] at hr
    exact (show IsUnit r from hr).map e.toRingHom

/-- Fixing the matrix fixes its inverse determinant, its generated algebra, and all fractions. -/
private theorem fixes_fraction_image_iff_fixes_matrix
    {K : Type u} {Q : Type v} [Field K] [CommRing Q] [Algebra K Q] {m : ℕ}
    (W : GL (Fin m) Q) (j : TotalQuotientRing (matrixGeneratedSubalgebra K W) →ₐ[K] Q)
    (hj : ∀ x, j (algebraMap (matrixGeneratedSubalgebra K W) _ x) = (x : Q))
    (τ : Q ≃ₐ[K] Q) :
    (∀ x : j.range, τ (x : Q) = (x : Q)) ↔ GeneralLinearGroup.map τ.toRingHom W = W := by
  let B := matrixGeneratedSubalgebra K W
  let i := algebraMap B (TotalQuotientRing B)
  constructor
  · intro h
    apply Units.ext
    ext a b
    have hw := (matrixGeneratedSubalgebra_le_iff.mp (le_rfl (a := B))).2 a b
    let x : B := ⟨W.val a b, hw⟩
    have hx := h ⟨j (i x), ⟨i x, rfl⟩⟩
    change τ (j (i x)) = j (i x) at hx
    rw [hj] at hx
    exact hx
  · intro h
    let F : Subalgebra K Q := AlgHom.equalizer τ.toAlgHom (AlgHom.id K Q)
    have hB : B ≤ F := by
      apply matrixGeneratedSubalgebra_le_iff.mpr
      refine ⟨?_, fun a b => ?_⟩
      · change τ (LinearSystem.determinantInverse W) = LinearSystem.determinantInverse W
        exact (determinantInverse_map τ.toRingHom W).symm.trans
          (congrArg LinearSystem.determinantInverse h)
      · exact congrArg (fun X : GL (Fin m) Q => X.val a b) h
    have hcomp : τ.toRingHom.comp j.toRingHom = j.toRingHom := by
      apply IsLocalization.ringHom_ext B⁰
      ext x
      change τ (j (i x)) = j (i x)
      rw [hj]
      exact hB x.property
    rintro ⟨q, r, rfl⟩
    exact RingHom.congr_fun hcomp r

/-- Realize the fixed ring of a closed normal subgroup via a fundamental
matrix whose Galois action has that subgroup as its kernel. -/
theorem normalSubgroupRealization : Specs.normalSubgroupRealization.{u, v} := by
  classical
  intro kind K R _ _ _ n δ A E T Y hbase hpv hY Q G H hclosed hnormal
  change OperatorField kind K at δ
  change LinearSystem kind K n at A
  change Operator kind R at E
  change Operator kind Q at T
  change δ.IsBaseField at hbase
  change IsPicardVessiotTotalExtension δ A E T at hpv
  have hDT := hpv.isExtension
  let : CharZero K := hbase.1
  let : IsAlgClosed (Specs.constantSubfield δ) := hbase.2
  obtain ⟨Y₀, _, hgen⟩ := hpv.1.2.2
  let : Algebra.FiniteType K R := finiteType_of_generatedByMatrix hgen
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have hG := (galoisCoordinateAlgebra δ A E Y hbase hpv.1 hY).2.1
  obtain ⟨m, ρ, hρ, hker⟩ :=
    ClosedSubgroupRepresentations.exists_kernelRepresentation G hG H hclosed hnormal
  obtain ⟨W, Aρ, hW, hact⟩ :=
    descendedRepresentationMatrix δ A E T Y hbase hpv hY ρ hρ
  change LinearSystem kind K m at Aρ
  let WQ := GeneralLinearGroup.map (algebraMap R Q) W
  let B := matrixGeneratedSubalgebra K WQ
  let C := Specs.constantSubfield δ
  let c := (algebraMap K Q).comp C.subtype
  have hWQ : Aρ.IsFundamental T WQ :=
    fundamental_map hW (IsScalarTower.toAlgHom K R Q) hpv.2.1
  have hsimple := hpv.1.2.1
  have hQsimple := Operator.isSimple_fractionRing E T hsimple hpv.2.1
  have hC :
      letI : Algebra C Q := Algebra.compHom Q C.subtype
      T.HasConstantField (C := C) := by
    intro x
    change T.IsConstant x ↔ ∃ a : C, c a = x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (Operator.constants_finiteType_fractionRing δ E T hbase hsimple
        hpv.1.1.1 hpv.2.1).surjective ⟨x, (Operator.mem_constantSubring T x).mpr hx⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    · rintro ⟨a, rfl⟩
      exact (Operator.mem_constantSubring T _).mp
        (Operator.RingHom.mapConstants (D := δ) (E := T) ⟨algebraMap K Q, hDT.1⟩ a).property
  obtain ⟨D, hD, hBpv, X, hX, hXfund, hXgen⟩ :=
    picardVessiot_recognition δ Aρ T hbase hDT hQsimple hC WQ hWQ
  change Operator kind B at D
  change D.Commutes T B.val at hD
  change IsPicardVessiotRing δ Aρ D at hBpv
  have hstable : T.IsStable (B : Set Q) :=
    (show Set.range B.val.toRingHom = (B : Set Q) from
      Set.ext fun _ => ⟨fun ⟨x, hx⟩ => hx ▸ x.property, fun hx => ⟨⟨_, hx⟩, rfl⟩⟩) ▸
      stable_range_of_commutes (f := B.val.toRingHom) hD
  have hu : ∀ x : B, x ∈ (B : Type v)⁰ → IsUnit (x : Q) :=
    regular_subring_elements_are_units (K := K) hsimple hpv.2.1 B.toSubring hstable
  let j : TotalQuotientRing B →ₐ[K] Q := IsLocalization.liftAlgHom (f := B.val) fun b =>
    hu b.val b.property
  have hjbase (x : B) : j (algebraMap B (TotalQuotientRing B) x) = (x : Q) :=
    IsLocalization.lift_eq (fun b : (B : Type v)⁰ => hu b.val b.property) x
  have hjinj : Function.Injective j :=
    (IsLocalization.lift_injective_iff (S := TotalQuotientRing B)
      (g := B.val.toRingHom) (fun b : (B : Type v)⁰ => hu b.val b.property)).mpr
      (fun x y => ⟨fun h => congrArg B.val (IsFractionRing.injective B _ h),
        fun h => congrArg (algebraMap B (TotalQuotientRing B)) (Subtype.val_injective h)⟩)
  have hjcomm : D.totalQuotient.Commutes T j := by
    apply commutes_on_fraction_ring j.toRingHom
    intro x
    change j (algebraMap B (TotalQuotientRing B) (D x)) =
      T (j (algebraMap B (TotalQuotientRing B) x))
    rw [hjbase, hjbase]
    exact hD x
  have hinter := fraction_image_is_intermediate j hjinj hjcomm
  have hcov (g : G) :
      GeneralLinearGroup.map (matrixFractionAutomorphism δ E Y g).toRingHom WQ =
        WQ * GeneralLinearGroup.map c (ρ g) := by
    let τ := (matrixAutomorphism δ E Y g).val.toRingHom
    let τQ := (matrixFractionAutomorphism δ E Y g).toRingHom
    have ht : τQ.comp (algebraMap R Q) = (algebraMap R Q).comp τ := by
      ext r
      exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ r
    change GeneralLinearGroup.map τQ (GeneralLinearGroup.map (algebraMap R Q) W) = _
    rw [mapGL_comp, ht, ← mapGL_comp, hact g, map_mul, mapGL_comp]
    rfl
  have hstab : Specs.relativeStabilizer δ E Y j.range = (H : Set G) := by
    ext g
    change (∀ x : j.range, matrixFractionAutomorphism δ E Y g (x : Q) = (x : Q)) ↔ g ∈ H
    let τ : Q ≃ₐ[K] Q :=
      IsFractionRing.algEquivOfAlgEquiv (matrixAutomorphism δ E Y g).val
    change (∀ x : j.range, τ (x : Q) = (x : Q)) ↔ g ∈ H
    rw [fixes_fraction_image_iff_fixes_matrix WQ j hjbase τ, ← hker]
    change GeneralLinearGroup.map τ.toRingHom WQ = WQ ↔ ρ g = 1
    have hτ : GeneralLinearGroup.map τ.toRingHom WQ =
        WQ * GeneralLinearGroup.map c (ρ g) := hcov g
    rw [hτ]
    have hone := (GeneralLinearGroup.map (n := Fin m) c).map_one
    constructor
    · intro hx
      apply mapGL_injective c (hDT.2.comp Subtype.val_injective)
      apply mul_left_cancel (a := WQ)
      rwa [hone, mul_one]
    · intro hx
      rw [hx, hone, mul_one]
  have hrange : j.range = Specs.matrixFixedSubalgebra δ E Y (H : Set G) := by
    obtain ⟨_, ⟨o, ho, hos⟩, _, _⟩ := operatorGaloisCorrespondence δ A E T Y hbase hpv hY
    let F : {S : Subalgebra K Q // Specs.isIntermediateTotalRing T S}ᵒᵈ :=
      OrderDual.toDual ⟨j.range, hinter⟩
    have hH : o.symm F = ⟨H, hclosed⟩ :=
      Subtype.ext (SetLike.coe_injective ((hos (OrderDual.ofDual F)).trans hstab))
    have h := ho (o.symm F)
    rw [o.apply_symm_apply, hH] at h
    exact h
  exact ⟨m, ρ, Aρ, W, hρ, hker, hW, D, D.totalQuotient, X, j, hBpv.totalExtension,
    hX, hXfund, hXgen, hu, hjinj, hjcomm, hjbase, hrange, hstab, hcov⟩

end GaloisFormalization.PV
