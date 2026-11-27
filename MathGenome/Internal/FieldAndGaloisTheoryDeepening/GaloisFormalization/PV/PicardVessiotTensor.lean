import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.ConstantIdealDescent
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteTypeConstants
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FundamentalMatrices
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.ReducedFieldBaseChange
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTensor

namespace GaloisFormalization.PV

open scoped TensorProduct Matrix
open Algebra.TensorProduct (includeLeftRingHom includeRight)
open Matrix (GeneralLinearGroup)
open LinearSystem (determinantInverse)

universe u v

abbrev tensorRatio := @Specs.tensorRatio

abbrev picardVessiotCoordinateAlgebra := @Specs.picardVessiotCoordinateAlgebra

private theorem determinantInverse_map {S B : Type*} [CommRing S] [CommRing B]
    {n : ℕ} (f : S →+* B) (Y : GL (Fin n) S) :
    determinantInverse (GeneralLinearGroup.map f Y) = f (determinantInverse Y) := by
  unfold determinantInverse
  rw [GeneralLinearGroup.map_det, ← map_inv]
  rfl

private theorem determinantInverse_mul {S : Type*} [CommRing S] {n : ℕ}
    (Y Z : GL (Fin n) S) :
    determinantInverse (Y * Z) = determinantInverse Y * determinantInverse Z := by
  simp [determinantInverse, mul_inv_rev, mul_comm]

section MatrixAlgebras

variable {C S : Type*} [CommRing C] [CommRing S] [Algebra C S] {n : ℕ}

private theorem matrixGeneratedSubalgebra_le_iff (Y : GL (Fin n) S) (P : Subalgebra C S) :
    matrixGeneratedSubalgebra C Y ≤ P ↔
      (∀ i j, Y.val i j ∈ P) ∧ determinantInverse Y ∈ P := by
  rw [matrixGeneratedSubalgebra, Algebra.adjoin_le_iff]
  constructor
  · intro h
    exact ⟨fun i j => h (Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩), h (Set.mem_insert _ _)⟩
  · rintro ⟨h, hinv⟩ x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | ⟨⟨i, j⟩, rfl⟩
    · exact hinv
    · exact h i j

private theorem matrixGeneratedSubalgebra_mul_le (Y Z : GL (Fin n) S) (P : Subalgebra C S)
    (hY : matrixGeneratedSubalgebra C Y ≤ P) (hZ : matrixGeneratedSubalgebra C Z ≤ P) :
    matrixGeneratedSubalgebra C (Y * Z) ≤ P := by
  obtain ⟨hY, hYi⟩ := (matrixGeneratedSubalgebra_le_iff Y P).mp hY
  obtain ⟨hZ, hZi⟩ := (matrixGeneratedSubalgebra_le_iff Z P).mp hZ
  refine (matrixGeneratedSubalgebra_le_iff _ _).mpr ⟨fun i j => ?_, ?_⟩
  · change (Y.val * Z.val) i j ∈ P
    rw [Matrix.mul_apply]
    exact P.sum_mem fun k _ => P.mul_mem (hY i k) (hZ k j)
  · rw [determinantInverse_mul]
    exact P.mul_mem hYi hZi

private theorem finiteType_of_matrixGenerated (Y : GL (Fin n) S)
    (hY : matrixGeneratedSubalgebra C Y = ⊤) : Algebra.FiniteType C S := by
  constructor
  rw [← hY]
  exact Subalgebra.fg_def.mpr ⟨_, (Set.finite_range _).insert _, rfl⟩

private theorem matrixUnit_over_generatedSubalgebra (Y : GL (Fin n) S) :
    ∃ B : GL (Fin n) (matrixGeneratedSubalgebra C Y),
      GeneralLinearGroup.map (matrixGeneratedSubalgebra C Y).val.toRingHom B = Y := by
  let P := matrixGeneratedSubalgebra C Y
  obtain ⟨hY, hYi⟩ := (matrixGeneratedSubalgebra_le_iff Y P).mp le_rfl
  let M : Matrix (Fin n) (Fin n) P := Matrix.of fun i j => ⟨Y.val i j, hY i j⟩
  have hM : M.map P.val = Y.val := rfl
  have hdet : P.val M.det = Y.val.det := by
    exact (RingHom.map_det P.val.toRingHom M).trans (congrArg Matrix.det hM)
  let d : P := ⟨determinantInverse Y, hYi⟩
  have hd : M.det * d = 1 := by
    apply (show Function.Injective P.val from Subtype.val_injective)
    rw [map_mul, map_one, hdet]
    exact (GeneralLinearGroup.det Y).mul_inv
  let B := GeneralLinearGroup.mk'' M (IsUnit.of_mul_eq_one d hd)
  exact ⟨B, Units.ext hM⟩

end MatrixAlgebras

section OperatorAlgebras

variable {kind : OperatorKind} {K : Type u} [Field K]
  {R : Type v} [CommRing R] [Algebra K R] {n : ℕ}
  {δ : OperatorField kind K} {E : Operator kind R}

private theorem hasConstantField_of_finiteType [Algebra.FiniteType K R]
    (hk : δ.IsBaseField) (hs : E.IsSimple) (he : δ.IsAlgebra E) :
    letI : Algebra δ.constantSubfield R := Algebra.compHom R δ.constantSubfield.subtype
    E.HasConstantField (C := δ.constantSubfield) := by
  let : Algebra δ.constantSubfield R := Algebra.compHom R δ.constantSubfield.subtype
  intro x
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (Operator.constants_finiteType δ E hk hs he).2
      ⟨x, (Operator.mem_constantSubring E x).mpr hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact (Operator.mem_constantSubring E _).mp
      (Operator.RingHom.mapConstants (D := δ) (E := E) ⟨algebraMap K R, he⟩ c).property

private theorem matrixGeneratedSubalgebra_of_fundamental
    {A : LinearSystem kind K n} (hk : δ.IsBaseField) (hpv : IsPicardVessiotRing δ A E)
    (Y : GL (Fin n) R) (hY : A.IsFundamental E Y) :
    matrixGeneratedSubalgebra K Y = ⊤ := by
  obtain ⟨he, hs, W, hW, hgen⟩ := hpv
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated W hgen
  let : Algebra δ.constantSubfield R := Algebra.compHom R δ.constantSubfield.subtype
  have hC := hasConstantField_of_finiteType hk hs he.1
  obtain ⟨B, hB, _⟩ := A.fundamentalRightMultiplier δ hk E he Y W hY hW
  let P := matrixGeneratedSubalgebra K Y
  have hmem (x : E.constantSubring) : (x : R) ∈ P := by
    obtain ⟨c, hc⟩ := (hC (x : R)).mp ((Operator.mem_constantSubring E _).mp x.property)
    rw [← hc]
    exact P.algebraMap_mem (c : K)
  have hBP : matrixGeneratedSubalgebra K (GeneralLinearGroup.map E.constantSubring.subtype B)
      ≤ P := by
    refine (matrixGeneratedSubalgebra_le_iff _ _).mpr ⟨fun i j => hmem (B.val i j), ?_⟩
    rw [determinantInverse_map]
    exact hmem (determinantInverse B)
  apply top_unique
  rw [← hgen, hB]
  exact matrixGeneratedSubalgebra_mul_le _ _ P le_rfl hBP

private theorem fundamental_map
    {S : Type*} [CommRing S] [Algebra K S] {F : Operator kind S}
    {A : LinearSystem kind K n} {Y : GL (Fin n) R}
    (f : R →ₐ[K] S) (hf : E.Commutes F f) (hY : A.IsFundamental E Y) :
    A.IsFundamental F (GeneralLinearGroup.map f.toRingHom Y) := by
  ext i j
  change F (f (Y.val i j)) = (A.mapCoefficients S * Y.val.map f) i j
  rw [← hf]
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) R => f (M i j)) hY
  simpa only [LinearSystem.mapCoefficients, Matrix.map_apply, Matrix.mul_apply,
    map_sum, map_mul, AlgHom.commutes] using h

private theorem isReduced_tensor_of_isSimple [CharZero K] [Algebra.FiniteType K R]
    (hs : E.IsSimple) : IsReduced (R ⊗[K] R) := by
  classical
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  cases kind with
  | differential =>
    let : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ K)
    let : IsDomain R := Operator.isDomain_of_isSimple E hs
    let f := IsScalarTower.toAlgHom K R (FractionRing R)
    let : IsReduced (FractionRing R ⊗[K] R) := reducedFieldBaseChange K (FractionRing R) R
    exact isReduced_of_injective (Algebra.TensorProduct.map f (AlgHom.id K R))
      (Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap
        (IsFractionRing.injective R (FractionRing R)))
  | difference =>
    obtain ⟨hfin, _, hdom, e, _, _, _, _, he, _⟩ :=
      simpleDifferenceComponents E.toRingEquiv hs
    let I := minimalPrimes R
    let : Finite I := hfin
    let : Fintype I := Fintype.ofFinite I
    let (i : I) : IsDomain (R ⧸ i.val) := hdom i
    let L (i : I) := FractionRing (R ⧸ i.val)
    let f : R →ₐ[K] ∀ i : I, L i := AlgHom.pi fun i =>
      (IsScalarTower.toAlgHom K (R ⧸ i.val) (L i)).comp (Ideal.Quotient.mkₐ K i.val)
    have hf : Function.Injective f := by
      intro a b hab
      apply e.injective
      funext i
      rw [he, he]
      exact IsFractionRing.injective (R ⧸ i.val) (L i) (congrFun hab i)
    let : IsReduced R := isReduced_of_injective f hf
    let (i : I) : IsReduced (R ⊗[K] L i) :=
      let : IsReduced (L i ⊗[K] R) := reducedFieldBaseChange K (L i) R
      isReduced_of_injective (Algebra.TensorProduct.comm K R (L i))
        (Algebra.TensorProduct.comm K R (L i)).injective
    let g := Algebra.TensorProduct.map (AlgHom.id K R) f
    have hg : Function.Injective g :=
      Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
    let t := Algebra.TensorProduct.piRight K K R L
    exact isReduced_of_injective (t.toAlgHom.comp g) (t.injective.comp hg)

end OperatorAlgebras

private theorem tensor_adjoin_eq_top {K R C : Type*} [Field K] [CommRing R] [Algebra K R]
    [Field C] [Algebra C R] [SMulCommClass K C R] {n : ℕ}
    (D : Subalgebra C (R ⊗[K] R)) (Y : GL (Fin n) R)
    (hY : matrixGeneratedSubalgebra K Y = ⊤)
    (hZ : matrixGeneratedSubalgebra C (tensorRatio K Y) ≤ D) :
    Algebra.adjoin R (D : Set (R ⊗[K] R)) = ⊤ := by
  let T := R ⊗[K] R
  let P : Subalgebra R T := Algebra.adjoin R (D : Set T)
  let left : R →+* T := includeLeftRingHom
  let right : R →ₐ[K] T := includeRight
  let Z := tensorRatio K Y
  have hYZ : GeneralLinearGroup.map right.toRingHom Y = GeneralLinearGroup.map left Y * Z := by
    change GeneralLinearGroup.map right.toRingHom Y =
      GeneralLinearGroup.map left Y *
        ((GeneralLinearGroup.map left Y)⁻¹ * GeneralLinearGroup.map right.toRingHom Y)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hmem : matrixGeneratedSubalgebra R (GeneralLinearGroup.map right.toRingHom Y) ≤ P := by
    rw [hYZ]
    apply matrixGeneratedSubalgebra_mul_le
    · refine (matrixGeneratedSubalgebra_le_iff _ _).mpr ⟨fun i j => ?_, ?_⟩
      · exact P.algebraMap_mem (Y.val i j)
      · rw [determinantInverse_map]
        exact P.algebraMap_mem (determinantInverse Y)
    · obtain ⟨hentries, hdet⟩ := (matrixGeneratedSubalgebra_le_iff _ _).mp hZ
      exact (matrixGeneratedSubalgebra_le_iff _ _).mpr
        ⟨fun i j => Algebra.subset_adjoin (hentries i j), Algebra.subset_adjoin hdet⟩
  have hr : ∀ b : R, right b ∈ P := by
    let Q : Subalgebra K R := (P.restrictScalars K).comap right
    have hQ : matrixGeneratedSubalgebra K Y ≤ Q := by
      obtain ⟨hentries, hdet⟩ := (matrixGeneratedSubalgebra_le_iff _ _).mp hmem
      refine (matrixGeneratedSubalgebra_le_iff _ _).mpr ⟨fun i j => hentries i j, ?_⟩
      rw [determinantInverse_map] at hdet
      exact hdet
    rw [hY] at hQ
    exact fun b => hQ (show b ∈ (⊤ : Subalgebra K R) from trivial)
  apply top_unique
  intro t ht
  clear ht
  change t ∈ P
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have h := P.mul_mem (P.algebraMap_mem a) (hr b)
    change (a ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] b) ∈ P at h
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using h
  | add t s ht hs => exact P.add_mem ht hs

/-- Constancy, reducedness and the canonical operator isomorphism for the tensor of a
Picard–Vessiot ring with itself. -/
theorem picardVessiotTensor : Specs.picardVessiotTensor.{u, v} := by
  intro kind K _ R _ _ n δ A E Y F hk hpv hY hF
  change OperatorField kind K at δ
  change Operator kind R at E
  change LinearSystem kind K n at A
  change Operator kind (R ⊗[K] R) at F
  change δ.IsBaseField at hk
  change IsPicardVessiotRing δ A E at hpv
  change A.IsFundamental E Y at hY
  let C := δ.constantSubfield
  let : Algebra C R := Algebra.compHom R δ.constantSubfield.subtype
  let T := R ⊗[K] R
  let left : R →ₐ[K] T := Algebra.TensorProduct.includeLeft
  let right : R →ₐ[K] T := includeRight
  have hleft : E.Commutes F left := hF.2.1
  have hright : E.Commutes F right := hF.2.2
  have hl : Function.Injective left :=
    (show Function.LeftInverse (Algebra.TensorProduct.lmul' K) left from
      fun x => mul_one x).injective
  have hEF : E.IsExtension F := ⟨hleft, hl⟩
  have hδF : δ.IsExtension F := ⟨hleft.comp hpv.1.1, hl.comp hpv.1.2⟩
  have hgen := matrixGeneratedSubalgebra_of_fundamental hk hpv Y hY
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y hgen
  let : CharZero K := hk.1
  have hC : E.HasConstantField (C := C) := hasConstantField_of_finiteType hk hpv.2.1 hpv.1.1
  let Y₁ := GeneralLinearGroup.map left.toRingHom Y
  let Y₂ := GeneralLinearGroup.map right.toRingHom Y
  let Z := tensorRatio K Y
  have hYZ : Y₂ = Y₁ * Z := by
    change Y₂ = Y₁ * (Y₁⁻¹ * Y₂)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  obtain ⟨W, hW, _⟩ := A.fundamentalRightMultiplier δ hk F hδF Y₁ Y₂
    (fundamental_map left hleft hY) (fundamental_map right hright hY)
  have hZ : GeneralLinearGroup.map F.constantSubring.subtype W = Z :=
    mul_left_cancel (hW.symm.trans hYZ)
  have hentry (i j : Fin n) : F.IsConstant (Z.val i j) := by
    rw [← hZ]
    exact (Operator.mem_constantSubring F _).mp (W.val i j).property
  have hdet : F.IsConstant (determinantInverse Z) := by
    rw [← hZ, determinantInverse_map]
    exact (Operator.mem_constantSubring F _).mp (determinantInverse W).property
  let D : Subalgebra C T := picardVessiotCoordinateAlgebra δ Y
  let P : Subalgebra C T :=
    { F.constantSubring with
      algebraMap_mem' := fun c =>
        (Operator.mem_constantSubring F _).mpr
          ((show E.Commutes F left.toRingHom from hleft).isConstant
            ((hC _).mpr ⟨c, rfl⟩)) }
  have hDP : D ≤ P := (matrixGeneratedSubalgebra_le_iff Z P).mpr
    ⟨fun i j => (Operator.mem_constantSubring F _).mpr (hentry i j),
      (Operator.mem_constantSubring F _).mpr hdet⟩
  have hD (d : D) : F.IsConstant (d : T) :=
    (Operator.mem_constantSubring F _).mp (hDP d.property)
  let : IsReduced T := isReduced_tensor_of_isSimple hpv.2.1
  have hredD : IsReduced D := isReduced_of_injective D.val Subtype.val_injective
  have hDT : Algebra.adjoin R (D : Set T) = ⊤ := tensor_adjoin_eq_top D Y hgen le_rfl
  obtain ⟨G, hG, _⟩ := Operator.tensor_constant_existsUnique (R := C)
    (T := D) hC.isAlgebra
  obtain ⟨e, he⟩ := Operator.constantTensorMulIsEquiv D hpv.2.1 hC hEF hG hD hDT
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin n) D, GeneralLinearGroup.map D.val.toRingHom B = Z :=
    matrixUnit_over_generatedSubalgebra (C := C) Z
  refine ⟨hentry, hdet, hD, inferInstance, hredD, G, e, hG, he, B, hB, ?_⟩
  let U := R ⊗[C] D
  let : CommRing U := Algebra.TensorProduct.instCommRing
  let : Algebra C U := Algebra.TensorProduct.leftAlgebra
  let f : U →+* T := e.val.toAlgHom.toRingHom
  let i : D →+* U := (includeRight : D →ₐ[C] U).toRingHom
  let l : R →+* U := includeLeftRingHom
  have hfl : f.comp l = left.toRingHom :=
    RingHom.ext fun r => e.val.commutes r
  have hfr : f.comp i = D.val.toRingHom := by
    ext d
    change e.val.toAlgHom (1 ⊗ₜ[C] d) = (d : T)
    rw [he]
    change Operator.constantTensorMul D (1 ⊗ₜ[C] d) = (d : T)
    simp
  change GeneralLinearGroup.map f
    (GeneralLinearGroup.map l Y * GeneralLinearGroup.map i B) = Y₂
  rw [map_mul]
  change GeneralLinearGroup.map (f.comp l) Y *
    GeneralLinearGroup.map (f.comp i) B = Y₂
  rw [hfl, hfr, hB]
  exact hYZ.symm

end GaloisFormalization.PV
