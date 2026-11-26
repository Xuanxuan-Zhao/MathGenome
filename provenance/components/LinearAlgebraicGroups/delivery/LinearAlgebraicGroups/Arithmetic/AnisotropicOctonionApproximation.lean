import Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicOctonionApproximation
import Specs.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
import LinearAlgebraicGroups.Arithmetic.OctonionForms
import LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import LinearAlgebraicGroups.Arithmetic.WeakApproximationByTori
import Mathlib.Topology.Algebra.Valued.NormedValued
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
noncomputable section

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Filter Set Topology
open scoped CategoryTheory.MonObj Classical MatrixGroups NumberField RestrictedProduct TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicOctonionApproximation

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)
open AdelicGroups ArithmeticLatticeProjection
open Composition.OctonionAutomorphismSpecification (AutomorphismGroup)
open Composition.Specification (OctonionNormConditions)
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates octonionMatrixHom)
open Specs.AnisotropicTensorQuotients (octonionMatrixModel localConditions)
open Specs.Arithmetic.LocalProjectedClosure (LocalNormalClosure FiniteCovolumeSubgroup)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)

open private linearPointsInBasis automorphismGroupAlongIso
  from LinearAlgebraicGroups.Arithmetic.OctonionForms
open private matrixActionEquiv from LinearAlgebraicGroups.Albert.AutomorphismScheme
open private matrixCoordinates_value
  from LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors

section MatrixComparison

variable {K C : Type u} [Field K] [NonAssocRing C] [Module K C]
  [IsScalarTower K C C] [SMulCommClass K C C]
  {G : AffineAlgebraicGroup K}

private def octonionRealization (A : AutomorphismGroup K C) (e : G.val ≅ A.group)
    (b : Module.Basis (Fin 8) K C) : MatrixRealization G where
  size := 8
  ambient := ⟨A.generalLinear, A.linearAffine, A.linearFiniteType, A.linearQuasiCompact⟩
  matrix := linearPointsInBasis A (b.reindex Equiv.ulift.symm)
  embedding := (automorphismGroupAlongIso G A e).inclusion
  closed := (automorphismGroupAlongIso G A e).closed

private def downMatrix {L : Type u} [CommRing L] : GL (Index.{u} 8) L ≃* GL (Fin 8) L :=
  Units.mapEquiv (Matrix.reindexRingEquiv L Equiv.ulift).toMulEquiv

private theorem downMatrix_entry {L : Type u} [CommRing L] (m : GL (Index.{u} 8) L)
    (a b : Fin 8) : (downMatrix m).val a b = m.val ⟨a⟩ ⟨b⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem octonionRealization_matrix (A : AutomorphismGroup K C)
    (e : G.val ≅ A.group) (b : Module.Basis (Fin 8) K C) (L : Type u)
    [Field L] [Algebra K L] (x : PointsIn (octonionRealization A e b) L) :
    downMatrix (asMatrix (octonionRealization A e b) L x) =
      octonionMatrixHom (L := L) b (automorphismGroupAlongIso G A e) x := by
  let S := CommAlgCat.of K L
  let B := automorphismGroupAlongIso G A e
  let c : Module.Basis (Index.{u} 8) K C := b.reindex Equiv.ulift.symm
  let M := asMatrix (octonionRealization A e b) L x
  let f := (B.subgroupPoints S x).val
  have hM : matrixActionEquiv c L M = f := by
    change matrixActionEquiv c L ((matrixActionEquiv c L).symm
      (A.linearPoints S (((schemePoints K).map B.inclusion).app S x))) = f
    rw [MulEquiv.apply_symm_apply]
    exact B.evaluatesInclusion S x
  apply Units.ext
  ext i j
  rw [downMatrix_entry]
  change M.val ⟨i⟩ ⟨j⟩ =
    (matrixCoordinates (b.baseChange L)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv L (L ⊗[K] C)) f)).val i j
  rw [matrixCoordinates_value, LinearMap.toMatrix_apply]
  have hcoeff : LinearMap.toMatrix (c.baseChange L) (c.baseChange L) f.val = M.val := by
    rw [← hM]
    exact (Matrix.toLinAlgEquiv (c.baseChange L)).symm_apply_apply M.val
  rw [← hcoeff, LinearMap.toMatrix_apply]
  have hc : c.baseChange L = (b.baseChange L).reindex Equiv.ulift.symm := by
    ext a
    simp [c]
  rw [hc]
  simp [LinearMap.GeneralLinearGroup.generalLinearEquiv]

private def downMatrixContinuous {L : Type u} [CommRing L] [TopologicalSpace L] :
    GL (Index.{u} 8) L ≃ₜ* GL (Fin 8) L :=
  Units.mapContinuousMulEquiv
    { toMulEquiv := (Matrix.reindexRingEquiv L Equiv.ulift).toMulEquiv
      continuous_toFun := continuous_id.matrix_reindex Equiv.ulift Equiv.ulift
      continuous_invFun := continuous_id.matrix_reindex Equiv.ulift.symm Equiv.ulift.symm }

private theorem downMatrix_map {L M : Type u} [CommRing L] [CommRing M]
    (f : L →+* M) (g : GL (Index.{u} 8) L) :
    downMatrix (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (downMatrix g) := by
  apply Units.ext
  ext i j
  rfl

private theorem downMatrix_integral {L : Type u} [Field L] (O : ValuationSubring L)
    (g : GL (Index.{u} 8) L) :
    downMatrix g ∈ (Matrix.GeneralLinearGroup.map O.subtype).range ↔
      g ∈ (Matrix.GeneralLinearGroup.map O.subtype).range := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨downMatrix.symm z, downMatrix.injective ?_⟩
    rw [downMatrix_map, MulEquiv.apply_symm_apply, hz]
  · rintro ⟨z, rfl⟩
    exact ⟨downMatrix z, (downMatrix_map _ _).symm⟩

open AnisotropicTensorQuotients
open private MatrixAdeles matrixAt continuous_matrixAt adelicMatrixGroup mem_localConditions
  from LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients

private def integralMatrixAt (D : GlobalFieldData.{u,v} K) (w : D.Place) :
    Subgroup (GL (Fin 8) (D.Completion w)) :=
  match w with
  | .inl w => (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range
  | .inr _ => ⊤

private theorem matrixAt_integral_iff (D : GlobalFieldData.{u,v} K)
    (A : AutomorphismGroup K C) (e : G.val ≅ A.group) (b : Module.Basis (Fin 8) K C)
    (w : D.Place) (x : LocalPoints D (octonionRealization A e b) w) :
    downMatrix (asMatrix (octonionRealization A e b) (D.Completion w) x) ∈ integralMatrixAt D w ↔
      x ∈ localSubgroup D (octonionRealization A e b) w := by
  cases w with
  | inl w => exact downMatrix_integral (D.integers w) _
  | inr w => exact iff_of_true (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem eventually_integral_matrixAdeles (D : GlobalFieldData.{u,v} K)
    (x : MatrixAdeles D (Fin 8)) :
    ∀ᶠ w : D.Place in cofinite, matrixAt D w x ∈ integralMatrixAt D w := by
  cases D with
  | number h =>
    letI := h
    refine eventually_cofinite.mpr ((eventually_cofinite.mp x.1.property).image Sum.inl |>.subset ?_)
    rintro (w | w) hw
    · exact ⟨w, hw, rfl⟩
    · exact (hw (Subgroup.mem_top _)).elim
  | function F t =>
    refine eventually_cofinite.mpr ((eventually_cofinite.mp x.property).image Sum.inl |>.subset ?_)
    rintro (w | w) hw
    · exact ⟨w, hw, rfl⟩
    · exact w.elim

private theorem assemble_matrixAdeles (D : GlobalFieldData.{u,v} K)
    (x : ∀ w : D.Place, GL (Fin 8) (D.Completion w))
    (hx : ∀ᶠ w : D.Place in cofinite, x w ∈ integralMatrixAt D w) :
    ∃ m : MatrixAdeles D (Fin 8), ∀ w, matrixAt D w m = x w := by
  have hfinite := (Sum.inl_injective : Function.Injective (Sum.inl : D.FinitePlace → D.Place))
    |>.tendsto_cofinite.eventually hx
  cases D with
  | number h =>
    letI := h
    refine ⟨(⟨fun w => x (.inl w), hfinite⟩, fun w => x (.inr w)), ?_⟩
    rintro (w | w) <;> rfl
  | function F t =>
    refine ⟨⟨fun w => x (.inl w), hfinite⟩, ?_⟩
    rintro (w | w)
    · rfl
    · exact w.elim

open private integralMatrices_isOpen from LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

private theorem integralMatrixAt_open (D : GlobalFieldData.{u,v} K) (w : D.FinitePlace) :
    IsOpen (integralMatrixAt D (.inl w) : Set (GL (Fin 8) (D.Completion (.inl w)))) := by
  exact @integralMatrices_isOpen _ (Fin 8) _ _ _ _ _ (D.integers w)
    (D.integers_properties w).2.1

private theorem matrixAdeles_topologicalGroup (D : GlobalFieldData.{u,v} K) :
    IsTopologicalGroup (MatrixAdeles D (Fin 8)) := by
  have h := integralMatrixAt_open D
  cases D with
  | number hn =>
    letI := hn
    letI : Fact (∀ w : NumberFinitePlace K, IsOpen
        ((Matrix.GeneralLinearGroup.map (n := Fin 8)
          (w.adicCompletionIntegers K).subtype).range :
          Set (GL (Fin 8) (w.adicCompletion K)))) := ⟨h⟩
    exact inferInstanceAs (IsTopologicalGroup (TensorAdelicReduction.NumberMatrixAdeles K (Fin 8)))
  | function F t =>
    letI : Fact (∀ w : FunctionPlace K, IsOpen
        ((Matrix.GeneralLinearGroup.map (n := Fin 8) w.integers.toSubring.subtype).range :
          Set (GL (Fin 8) w.Completion))) := ⟨h⟩
    exact inferInstanceAs (IsTopologicalGroup (TensorAdelicReduction.FunctionMatrixAdeles K (Fin 8)))

private theorem allIntegral_open (D : GlobalFieldData.{u,v} K) :
    IsOpen {x : MatrixAdeles D (Fin 8) | ∀ w, matrixAt D w x ∈ integralMatrixAt D w} := by
  have h := integralMatrixAt_open D
  cases D with
  | number hn =>
    letI := hn
    let X (w : NumberFinitePlace K) := GL (Fin 8) (w.adicCompletion K)
    let U (w : NumberFinitePlace K) : Set (X w) :=
      (Matrix.GeneralLinearGroup.map (n := Fin 8) (w.adicCompletionIntegers K).subtype).range
    have hopen := (RestrictedProduct.isOpenEmbedding_structureMap
      (R := X) (A := U) h).isOpen_range
    rw [RestrictedProduct.range_structureMap] at hopen
    convert hopen.preimage (continuous_fst (X := Πʳ w, [X w, U w])) using 1
    ext x
    constructor
    · exact fun hx w => hx (.inl w)
    · intro hx
      rintro (w | w)
      · exact hx w
      · exact Subgroup.mem_top _
  | function F t =>
    let X (w : FunctionPlace K) := GL (Fin 8) w.Completion
    let U (w : FunctionPlace K) : Set (X w) :=
      (Matrix.GeneralLinearGroup.map (n := Fin 8) w.integers.toSubring.subtype).range
    have hopen := (RestrictedProduct.isOpenEmbedding_structureMap
      (R := X) (A := U) h).isOpen_range
    rw [RestrictedProduct.range_structureMap] at hopen
    convert hopen using 1
    ext x
    constructor
    · exact fun hx w => hx (.inl w)
    · intro hx
      rintro (w | w)
      · exact hx w
      · exact w.elim

open private cosetMap continuous_cosetMap surjective_cosetMap
  from LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

set_option backward.isDefEq.respectTransparency false in
private theorem matrixQuotientCompactness (D : GlobalFieldData.{u,v} K)
    (A : AutomorphismGroup K C) (e : G.val ≅ A.group) (b : Module.Basis (Fin 8) K C)
    (δ : GL (Fin 8) K →* MatrixAdeles D (Fin 8))
    (hδ : ∀ r w, matrixAt D w (δ r) = Matrix.GeneralLinearGroup.map (D.embedding w) r)
    (hQ : Specs.AnisotropicTensorQuotients.CompactMatrixQuotient
      (adelicMatrixGroup D (octonionMatrixModel b (automorphismGroupAlongIso G A e)))
      (octonionMatrixModel b (automorphismGroupAlongIso G A e) K (RingHom.id K)) δ) :
    CompactSpace (Adeles D (octonionRealization A e b) ∅ ⧸
      diagonalSubgroup D (octonionRealization A e b)) := by
  let j := octonionRealization A e b
  let M := octonionMatrixModel b (automorphismGroupAlongIso G A e)
  let H := adelicMatrixGroup D M
  letI := matrixAdeles_topologicalGroup D
  let f (w : D.Place) : LocalPoints D j w →* GL (Fin 8) (D.Completion w) :=
    downMatrix.toMonoidHom.comp (asMatrix j (D.Completion w))
  have hf (w : D.Place) : IsEmbedding (f w) :=
    downMatrixContinuous.toHomeomorph.isEmbedding.comp (localMatrixEmbedding D j w).isEmbedding
  have hRange (w : D.Place) : (f w).range = M (D.Completion w) (D.embedding w) := by
    ext m
    change (∃ p : LocalPoints D j w, f w p = m) ↔
      ∃ p : LocalPoints D j w,
        octonionMatrixHom (L := D.Completion w) b (automorphismGroupAlongIso G A e) p = m
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, (octonionRealization_matrix A e b (D.Completion w) p).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, octonionRealization_matrix A e b (D.Completion w) p⟩
  let coord (w : D.Place) : H →* (f w).range :=
    ((matrixAt D w).comp H.subtype).codRestrict _ (fun m => by
      rw [hRange w]
      exact (mem_localConditions _ _ _).mp m.property w)
  let a (w : D.Place) : H →* LocalPoints D j w :=
    (MonoidHom.ofInjective (hf w).injective).symm.toMonoidHom.comp (coord w)
  have ha (w : D.Place) (m : H) : f w (a w m) = matrixAt D w m.val :=
    MonoidHom.apply_ofInjective_symm (hf w).injective (coord w m)
  have hcont (w : D.Place) : Continuous (a w) :=
    (hf w).continuous_iff.mpr (by
      simpa only [Function.comp_def, ha] using
        (continuous_matrixAt (I := Fin 8) D w).comp (continuous_subtype_val : Continuous (Subtype.val : H → _)))
  have hint (w : D.Place) (m : H) :
      a w m ∈ localSubgroup D j w ↔ matrixAt D w m.val ∈ integralMatrixAt D w := by
    rw [← matrixAt_integral_iff D A e b, ← ha w m]
    rfl
  let lift : H →* Adeles D j ∅ :=
    { toFun := fun m => ⟨fun w => a w.1 m, by
        apply Eventually.mono (Subtype.val_injective.tendsto_cofinite.eventually
          (eventually_integral_matrixAdeles D m.val))
        intro w hw
        exact (hint w.1 m).mpr hw⟩
      map_one' := RestrictedProduct.ext _ _ fun w => (a w.1).map_one
      map_mul' := fun m n => RestrictedProduct.ext _ _ fun w => (a w.1).map_mul m n }
  let U := {m : H | ∀ w, matrixAt D w m.val ∈ integralMatrixAt D w}
  have hU : IsOpen U := (allIntegral_open D).preimage continuous_subtype_val
  have h1 : (1 : H) ∈ U := fun w => by
    change matrixAt D w 1 ∈ integralMatrixAt D w
    rw [map_one]
    exact (integralMatrixAt D w).one_mem
  have hLiftCont : Continuous lift := by
    apply continuous_of_continuousAt_one
    apply ContinuousOn.continuousAt _ (hU.mem_nhds h1)
    rw [continuousOn_iff_continuous_domRestrict]
    let g (m : U) (w : Outside D ∅) : localSubgroup D j w.1 :=
      ⟨a w.1 m.val, (hint w.1 m.val).mpr (m.property w.1)⟩
    have hg : Continuous g := continuous_pi fun w =>
      ((hcont w.1).comp continuous_subtype_val).subtype_mk _
    exact RestrictedProduct.isEmbedding_structureMap.continuous.comp hg
  let outside (w : D.Place) : Outside D ∅ := ⟨w, Finset.notMem_empty w⟩
  have hLiftSurj : Function.Surjective lift := by
    intro x
    let y (w : D.Place) := f w (x (outside w))
    have hy : ∀ᶠ w in cofinite, y w ∈ integralMatrixAt D w := by
      apply Eventually.mono ((show Function.Injective outside from fun _ _ h =>
        congrArg Subtype.val h).tendsto_cofinite.eventually x.property)
      intro w hw
      exact (matrixAt_integral_iff D A e b w (x (outside w))).mpr hw
    obtain ⟨m, hm⟩ := assemble_matrixAdeles D y hy
    have hmH : m ∈ H := (mem_localConditions _ _ _).mpr fun w => by
      rw [← hRange w, hm w]
      exact ⟨x (outside w), rfl⟩
    refine ⟨⟨m, hmH⟩, RestrictedProduct.ext _ _ fun w => (hf w.1).injective ?_⟩
    exact (ha w.1 ⟨m, hmH⟩).trans (hm w.1)
  have hdiag : ((M K (RingHom.id K)).map δ).subgroupOf H ≤
      (diagonalSubgroup D j).comap lift := by
    rintro m ⟨r, hr, hrm⟩
    obtain ⟨p, hp⟩ := hr
    change RationalPoints G at p
    change δ r = m.val at hrm
    refine ⟨p, fun w => (hf w.1).injective ?_⟩
    change f w.1 (a w.1 m) = f w.1 (localPoint D j w.1 p)
    rw [ha, ← hrm, hδ]
    change _ = downMatrix (asMatrix j (D.Completion w.1) (localPoint D j w.1 p))
    rw [localPoint_matrix]
    exact (congrArg (Matrix.GeneralLinearGroup.map (D.embedding w.1))
      (hp.symm.trans (octonionRealization_matrix A e b K p).symm)).trans
        (downMatrix_map (D.embedding w.1) (j.onPoints p)).symm
  letI := hQ.2
  exact (surjective_cosetMap lift hdiag hLiftSurj).compactSpace (continuous_cosetMap lift hdiag hLiftCont)

/-- The compact tensor quotient uses the same local points and rational diagonal as
the quotient in any closed realization of the octonion automorphism scheme. -/
theorem compactOctonionAdelicQuotient (D : GlobalFieldData.{u,v} K)
    (q : QuadraticForm K C) (A : AutomorphismGroup K C) (e : G.val ≅ A.group)
    (hq : OctonionNormConditions q) (ha : ∀ x, q x = 0 → x = 0)
    (i : MatrixRealization G) : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  classical
  letI := hq.finite
  have hDim := ((Composition.octonion_norm_iff_field q).mp hq).2
  let b := (Module.finBasis K C).reindex (finCongr hDim)
  let j := octonionRealization A e b
  have hQ := octonionCompactness D b q (automorphismGroupAlongIso G A e) hq ha
  have hcomp : CompactSpace (Adeles D j ∅ ⧸ diagonalSubgroup D j) := by
    cases D with
    | number hn =>
      letI := hn
      obtain ⟨δ, hδ, h⟩ := hQ
      let D₀ : GlobalFieldData.{u,v} K := .number hn
      let M := octonionMatrixModel b (automorphismGroupAlongIso G A e)
      have hG : adelicMatrixGroup D₀ M =
          localConditions Specs.AnisotropicTensorQuotients.numberAtPlace
            (fun (w : NumberPlace K) => M w.Completion w.embedding) := by
        ext x
        simp only [adelicMatrixGroup, mem_localConditions]
        constructor <;> intro hx w <;> cases w
        · exact hx (.inl _)
        · exact hx (.inr _)
        · exact hx (.inl _)
        · exact hx (.inr _)
      exact matrixQuotientCompactness D₀ A e b δ
        (fun r w => by cases w with | inl w => exact hδ r (.inl w) | inr w => exact hδ r (.inr w))
        (hG.symm ▸ h)
    | function F t =>
      obtain ⟨δ, hδ, h⟩ := hQ
      let D₀ : GlobalFieldData.{u,v} K := .function F t
      let M := octonionMatrixModel b (automorphismGroupAlongIso G A e)
      have hG : adelicMatrixGroup D₀ M =
          localConditions Specs.AnisotropicTensorQuotients.functionAtPlace
            (fun (w : FunctionPlace K) => M w.Completion w.embedding) := by
        ext x
        simp only [adelicMatrixGroup, mem_localConditions]
        exact ⟨fun hx w => hx (.inl w), fun hx w => by cases w with
          | inl w => exact hx w
          | inr w => exact w.elim⟩
      exact matrixQuotientCompactness D₀ A e b δ
        (fun r w => by cases w with | inl w => exact hδ r w | inr w => exact w.elim)
        (hG.symm ▸ h)
  let f := changeRealization D j i ∅
  have h : diagonalSubgroup D j ≤ (diagonalSubgroup D i).comap f.toMonoidHom := by
    rintro x ⟨g, hg⟩
    exact ⟨g, fun w => hg w⟩
  letI := hcomp
  exact (surjective_cosetMap f.toMonoidHom h f.surjective).compactSpace
    (continuous_cosetMap f.toMonoidHom h f.continuous)

end MatrixComparison


section RealPoints

open Specs.OctonionForms (realNormCore realAutomorphismColumns)
open Composition.Specification (normBaseChange)
open DivisionOctonionOrthogonalTensors (octonionMatrixStabilizer)

private theorem continuousMatrixUnits {X F I : Type*} [TopologicalSpace X]
    [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [Fintype I] [DecidableEq I]
    (g : X → GL I F) (hg : Continuous (fun x => (g x).val)) : Continuous g := by
  refine Units.continuous_iff.mpr ⟨hg, ?_⟩
  simp only [Matrix.coe_units_inv]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx : (g x).val.det ≠ 0 := (Matrix.GeneralLinearGroup.det (g x)).ne_zero
  have hinv : ContinuousAt Ring.inverse (g x).val.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx
  have h : ContinuousAt (fun a : Matrix I I F => a⁻¹) (g x).val :=
    continuousAt_matrix_inv _ hinv
  exact h.comp (f := fun y => (g y).val) hg.continuousAt

private def baseChangeAlongEquiv {F E V : Type*} [Field F] [Field E] [AddCommGroup V]
    [Module F V] (r : F ≃+* E) :
    letI : Algebra F E := r.toRingHom.toAlgebra
    letI := RingHomInvPair.of_ringEquiv r
    letI := RingHomInvPair.symm (↑r : F →+* E) (↑r.symm : E →+* F)
    V ≃ₛₗ[(↑r : F →+* E)] (E ⊗[F] V) := by
  letI : Algebra F E := r.toRingHom.toAlgebra
  letI := RingHomInvPair.of_ringEquiv r
  letI := RingHomInvPair.symm (↑r : F →+* E) (↑r.symm : E →+* F)
  let f : V →ₛₗ[(↑r : F →+* E)] E ⊗[F] V :=
    { toFun := fun v => (1 : E) ⊗ₜ[F] v
      map_add' := fun a b => TensorProduct.tmul_add _ _ _
      map_smul' := fun a v => by
        change (1 : E) ⊗ₜ[F] (a • v) = r a • ((1 : E) ⊗ₜ[F] v)
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul' (r a)]
        rfl }
  let e : F ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := r) fun _ => rfl
  let l := (TensorProduct.lid F V).symm.trans
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl F V))
  have hl : (l : V → E ⊗[F] V) = f := by
    funext v
    change TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl F V)
      ((TensorProduct.lid F V).symm v) = _
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul]
    change e 1 ⊗ₜ[F] v = 1 ⊗ₜ[F] v
    rw [map_one]
  exact LinearEquiv.ofBijective f (hl ▸ l.bijective)

private theorem baseChangeAlongEquiv_apply {F E V : Type*} [Field F] [Field E]
    [AddCommGroup V] [Module F V] (r : F ≃+* E) (x : V) :
    letI : Algebra F E := r.toRingHom.toAlgebra
    baseChangeAlongEquiv r x = (1 : E) ⊗ₜ[F] x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem compactConnectedOfRealNorm {K C : Type u} [Field K] [NonAssocRing C]
    [Module K C] [IsScalarTower K C C] [SMulCommClass K C C] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place)
    (A : AutomorphismGroup K C) (e : G.val ≅ A.group)
    (q : QuadraticForm K C) (hq : OctonionNormConditions q)
    (r : D.Completion w ≃+* ℝ) (hr : Continuous r.symm)
    (hp : letI := hq.projective
      let F := D.Completion w
      let qF := normBaseChange F q
      letI := (Composition.octonion_norm_baseChange hq F).projective
      letI : Algebra F ℝ := r.toRingHom.toAlgebra
      ∀ x, x ≠ 0 → 0 < normBaseChange ℝ qF x) :
    CompactSpace (LocalPoints D i w) ∧ ConnectedSpace (LocalPoints D i w) := by
  classical
  let F := D.Completion w
  let B := automorphismGroupAlongIso G A e
  let V := F ⊗[K] C
  letI : Algebra F ℝ := r.toRingHom.toAlgebra
  let W := ℝ ⊗[F] V
  letI := hq.projective
  letI := hq.finite
  let qF := normBaseChange F q
  have hqF := Composition.octonion_norm_baseChange hq F
  letI := hqF.projective
  let qR := normBaseChange ℝ qF
  have hqR := Composition.octonion_norm_baseChange hqF ℝ
  letI := hqR.finite
  letI := realNormCore qR hp
  letI := (realNormCore qR hp).toNormedAddCommGroup
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore inferInstance
  have hDim := ((Composition.octonion_norm_iff_field q).mp hq).2
  let b : Module.Basis (Fin 8) K C := (Module.finBasis K C).reindex (finCongr hDim)
  let bF := b.baseChange F
  let bR := bF.baseChange ℝ
  let j := octonionRealization A e b
  let P := LocalPoints D j w
  let m : P →* GL (Fin 8) F := downMatrix.toMonoidHom.comp (asMatrix j F)
  have hm (p : P) : m p = octonionMatrixHom (L := F) b B p :=
    octonionRealization_matrix A e b F p
  have hEmb : IsEmbedding m :=
    downMatrixContinuous.toHomeomorph.isEmbedding.comp (localMatrixEmbedding D j w).isEmbedding
  letI := RingHomInvPair.of_ringEquiv r
  letI := RingHomInvPair.symm (↑r : F →+* ℝ) (↑r.symm : ℝ →+* F)
  let L : V ≃ₛₗ[(↑r : F →+* ℝ)] W := baseChangeAlongEquiv r
  have hL (x : V) : L x = (1 : ℝ) ⊗ₜ[F] x := baseChangeAlongEquiv_apply r x
  have hLm (x y : V) : L (x * y) = L x * L y := by
    rw [hL, hL, hL]
    exact (by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul] :
        (1 : ℝ) ⊗ₜ[F] x * (1 : ℝ) ⊗ₜ[F] y = (1 : ℝ) ⊗ₜ[F] (x * y)).symm
  have hL₁ : L 1 = 1 := hL 1
  have hLb (s : Fin 8) : L (bF s) = bR s := by simp [hL, bR]
  have hLc (x : V) (s : Fin 8) : bR.repr (L x) s = r (bF.repr x s) := by
    rw [hL]
    change (bF.baseChange ℝ).repr (1 ⊗ₜ[F] x) s = _
    simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    rfl
  let T : Set (Fin 8 → W) := realAutomorphismColumns (C := W) bR
  have hTc : IsCompact T := OctonionForms.realCompact hqR hp bR
  have hTn : IsConnected T := OctonionForms.realConnected hqR hp bR
  let a (t : T) : W ≃ₗ[ℝ] W := Classical.choose t.property
  have ha (t : T) := Classical.choose_spec t.property
  let f (t : T) : V ≃ₗ[F] V := L.trans ((a t).trans L.symm)
  have hf (t : T) (x : V) : L (f t x) = a t (L x) := L.apply_symm_apply _
  have hfm (t : T) (x y : V) : f t (x * y) = f t x * f t y := by
    apply L.injective
    rw [hf, hLm, (ha t).2.2, hLm, hf, hf]
  let g (t : T) : GL (Fin 8) F := matrixCoordinates bF (f t)
  have hg (t : T) (s k : Fin 8) : (g t).val s k = r.symm (bR.repr (t.val k) s) := by
    apply r.injective
    rw [r.apply_symm_apply]
    change r ((matrixCoordinates bF (f t)).val s k) = _
    rw [matrixCoordinates_value, LinearMap.toMatrix_apply, ← hLc]
    change (bR.repr (L (f t (bF k)))) s = _
    rw [hf, hLb, show a t (bR k) = t.val k from (ha t).1 k]
  have hgc : Continuous g := by
    apply continuousMatrixUnits g
    apply continuous_matrix
    intro s k
    simp_rw [hg]
    exact hr.comp <| ((Finsupp.lapply s).comp bR.repr.toLinearMap).continuous_of_finiteDimensional.comp
      ((continuous_apply k).comp continuous_subtype_val)
  have hgmem (t : T) : g t ∈ (octonionMatrixHom (L := F) b B).range := by
    have h := (octonionMatrixStabilizer (L := F) b B).2.2 (g t)
    apply h.1.mpr
    apply h.2.mpr
    change ∀ x y, (matrixCoordinates bF).symm (g t) (x * y) =
      (matrixCoordinates bF).symm (g t) x * (matrixCoordinates bF).symm (g t) y
    simpa only [g, MulEquiv.symm_apply_apply] using hfm t
  let p (t : T) : P := Classical.choose (hgmem t)
  have hpM (t : T) : m (p t) = g t := (hm (p t)).trans (Classical.choose_spec (hgmem t))
  have hpC : Continuous p := hEmb.continuous_iff.mpr (by simpa only [Function.comp_def, hpM] using hgc)
  have hpS : Function.Surjective p := by
    intro x
    let f₀ := (matrixCoordinates bF).symm (m x)
    have hmem : m x ∈ (octonionMatrixHom (L := F) b B).range := ⟨x, (hm x).symm⟩
    have h := (octonionMatrixStabilizer (L := F) b B).2.2 (m x)
    have h₀ : ∀ z y, f₀ (z * y) = f₀ z * f₀ y := h.2.mp (h.1.mp hmem)
    have h₁ : f₀ 1 = 1 := by
      obtain ⟨y, hy⟩ := f₀.surjective 1
      calc
        f₀ 1 = f₀ 1 * f₀ y := by rw [hy, mul_one]
        _ = 1 := by rw [← h₀, one_mul, hy]
    let a₀ : W ≃ₗ[ℝ] W := L.symm.trans (f₀.trans L)
    have ha₀ (z : V) : a₀ (L z) = L (f₀ z) := by
      change L (f₀ (L.symm (L z))) = L (f₀ z)
      rw [L.symm_apply_apply]
    let t : T := ⟨fun k => a₀ (bR k), a₀, fun _ => rfl, by
      rw [← hL₁, ha₀, h₁], by
      intro z y
      obtain ⟨z, rfl⟩ := L.surjective z
      obtain ⟨y, rfl⟩ := L.surjective y
      rw [← hLm, ha₀, h₀, hLm, ha₀, ha₀]⟩
    refine ⟨t, hEmb.injective ?_⟩
    rw [hpM]
    have heq : f t = f₀ := by
      apply LinearEquiv.toLinearMap_injective
      apply bF.ext
      intro k
      change f t (bF k) = f₀ (bF k)
      apply L.injective
      rw [hf, hLb, show a t (bR k) = t.val k from (ha t).1 k]
      change a₀ (bR k) = L (f₀ (bF k))
      rw [← hLb, ha₀]
    change matrixCoordinates bF (f t) = m x
    rw [heq, MulEquiv.apply_symm_apply]
  letI : CompactSpace T := isCompact_iff_compactSpace.mp hTc
  letI : ConnectedSpace T := isConnected_iff_connectedSpace.mp hTn
  letI : CompactSpace P := hpS.compactSpace hpC
  letI : ConnectedSpace P := hpS.connectedSpace hpC
  let h := AdelicGroups.continuous_changePoints j i F
  exact ⟨(changePoints j i F).surjective.compactSpace h,
    (changePoints j i F).surjective.connectedSpace h⟩

end RealPoints

section LocalProjections

open CompactProductIsolation (Contracted)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition)

open MeasureTheory Topology
open ArithmeticLatticeProjection (FiniteInvariantQuotientMeasure)
open LocalQuotientTransport (RightCosets RightInvariant coset rightTranslate imageSubgroup)

/-- Inversion takes the invariant measure on `P ⧸ H` to a right-invariant
measure on `H ∖ P`. -/
private theorem rightInvariantMeasureOfFiniteQuotient {P : Type u} [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] (H : Subgroup P)
    (h : FiniteInvariantQuotientMeasure H) :
    ∃ ν : Measure (RightCosets H), IsFiniteMeasure ν ∧ ν ≠ 0 ∧ RightInvariant ν := by
  unfold FiniteInvariantQuotientMeasure at h
  borelize (P ⧸ H)
  obtain ⟨ν, hfin, hpos, hinv⟩ := h
  let q : P ⧸ H → RightCosets H := Quotient.map' Inv.inv (by
    intro x y hxy
    rw [QuotientGroup.rightRel_apply, inv_inv]
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem (QuotientGroup.leftRel_apply.mp hxy))
  have hq : Continuous q := continuous_quot_map _ continuous_inv
  have hμ : ν ≠ 0 := by
    intro hz
    have hpos' : 0 < ν Set.univ := isOpen_univ.measure_pos ν Set.univ_nonempty
    simp [hz] at hpos'
  refine ⟨ν.map q, inferInstance, (Measure.map_ne_zero_iff hq.measurable.aemeasurable).mpr hμ, ?_⟩
  intro a
  have ha : Measurable (rightTranslate (H := H) a) :=
    ((LocalQuotientTransport.quotient_action H).2.2.comp
      (continuous_id.prodMk continuous_const)).measurable
  have hsmul : Measurable (a⁻¹ • · : P ⧸ H → P ⧸ H) :=
    (continuous_const_smul _).measurable
  have he : rightTranslate a ∘ q = q ∘ (a⁻¹ • ·) := by
    funext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    change coset H (g⁻¹ * a) = coset H ((a⁻¹ * g)⁻¹)
    rw [mul_inv_rev, inv_inv]
  refine ⟨ha, ?_⟩
  rw [Measure.map_map ha hq.measurable, he, ← Measure.map_map hq.measurable hsmul]
  congr 1
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hsmul hs, measure_preimage_smul ν a⁻¹ s]

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Arithmetic.LocalQuotientMixing (MixingCases)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open LocalAlgebraicTransport (pointTopology RationalPoints)

/-- Apply the conditional finite-covolume input under a topological group
comparison with the original affine points over the local field. -/
private theorem fullProjectionOfLocalModel (hfull : FiniteCovolumeSubgroup.{u})
    {F P : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J) (hmix : MixingCases J)
    (H : Subgroup P) (hclosed : IsClosed (H : Set P)) (hnd : ¬ DiscreteTopology H)
    (hμ : FiniteInvariantQuotientMeasure H) :
    letI := pointTopology J.val.X
    IsTopologicalGroup (RationalPoints J.val.X) →
    (P ≃ₜ* RationalPoints J.val.X) → H = ⊤ := by
  let _ := pointTopology J.val.X
  intro htop e
  let : IsTopologicalGroup (RationalPoints J.val.X) := htop
  obtain ⟨ν, hfin, hpos, hinv⟩ := rightInvariantMeasureOfFiniteQuotient H hμ
  have := hfin
  obtain ⟨hm, hc, hd⟩ := LocalQuotientTransport.subgroup_transport e H
  obtain ⟨q, _, hq⟩ := LocalQuotientTransport.quotient_transport e H
  obtain ⟨hfin', hpos', hinv', _⟩ :=
    LocalQuotientTransport.measure_transport e q hq ν hinv hpos
  have := hfin'
  have he := hfull F J hJ hmix (imageSubgroup e H) (hc.mp hclosed) (hnd ∘ hd.mpr)
    (ν.map q) hpos' hinv'
  apply top_unique
  intro x _
  exact (hm x).mp (he ▸ Subgroup.mem_top (e x))

open AdelicGroups (Adeles LocalPoints Outside StrongApproximation localSubgroup)
open ArithmeticLatticeProjection (FinitePoints diagonalSubgroup lattice forgetPlaces)
open CompactProductIsolation (Contracted insertFinite diagonalClosure projectedArithmetic)
open Specs.IntegralModels (MatrixRealization)

/-- The projected arithmetic subgroup is dense if its nondiscrete closed
finite-covolume closure is the whole product. The contraction argument then
embeds every element of the product in the adelic diagonal closure. -/
private theorem isolateFactorsOfFullProjection {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hJ : J.Nonempty) (hd : Disjoint J S)
    (U : Subgroup (Adeles D i (S ∪ J)))
    (hU : IsCompact (U : Set (Adeles D i (S ∪ J))))
    (hU' : IsOpen (U : Set (Adeles D i (S ∪ J))))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hfull : ∀ H : Subgroup (FinitePoints D i J),
      IsClosed (H : Set (FinitePoints D i J)) → ¬ DiscreteTopology H →
      FiniteInvariantQuotientMeasure H → H = ⊤)
    (hcontract : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
      Set (FinitePoints D i J))) :
    ∀ x : FinitePoints D i J, insertFinite D i S J x ∈ diagonalClosure D i S := by
  obtain ⟨hnd, H, hH, _, hμ⟩ := ArithmeticLatticeProjection.projectionProperties
    D i S (S ∪ J) J U Finset.subset_union_left Finset.subset_union_right
    hcompact hnoncompact hJ hd hU hU'
  have hclosed : IsClosed (H : Set (FinitePoints D i J)) := by rw [hH]; exact isClosed_closure
  have hnd' : ¬ DiscreteTopology H := by
    intro h
    apply hnd
    have hi : (projectedArithmetic D i S J U : Set (FinitePoints D i J)) ⊆ H := by
      rw [hH]
      exact subset_closure
    exact (isDiscrete_iff_discreteTopology.mpr h).mono hi
  have htop := hfull H hclosed hnd' hμ
  have hP : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
    rw [dense_iff_closure_eq]
    calc
      _ = (H : Set (FinitePoints D i J)) := hH.symm
      _ = Set.univ := by rw [htop, Subgroup.coe_top]
  exact (CompactProductIsolation.isolateAdelicFactors D i S J hd U hU hU').2 hP hcontract

/-- With compact archimedean factors outside the omitted set, singleton
arithmetic projections suffice away from a finite set of exceptions. -/
private theorem strongApproximationOfLocalProjections {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hd : Disjoint J S)
    (harch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → CompactSpace (LocalPoints D i (.inr w)))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hfull : ∀ w : Outside D S, w.1 ∉ J → ∀ H : Subgroup (FinitePoints D i {w.1}),
      IsClosed (H : Set (FinitePoints D i {w.1})) → ¬ DiscreteTopology H →
      FiniteInvariantQuotientMeasure H → H = ⊤)
    (hcontract : ∀ w : Outside D S, w.1 ∉ J →
      Dense (Subgroup.closure {x : FinitePoints D i {w.1} | Contracted x} :
        Set (FinitePoints D i {w.1})))
    (hrem : DenseRange (ArithmeticLatticeProjection.rationalProjection D i J)) :
    StrongApproximation D i S := by
  have hsingle (w : Outside D S) (hw : w.1 ∉ J) (a : LocalPoints D i w.1) :
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
        diagonalClosure D i S := by
    let T : Finset D.Place := {w.1}
    have hT : Disjoint T S := by simpa [T] using w.2
    let U := ArithmeticLatticeProjection.integralOutside D i (S ∪ T)
    obtain ⟨hUc, hUo⟩ := ArithmeticLatticeProjection.compactOpenOutside D i (S ∪ T)
      fun x hx => harch x (fun hx' => hx (Finset.mem_union_left _ hx'))
    have hins := isolateFactorsOfFullProjection D i S T ⟨w.1, Finset.mem_singleton_self _⟩
      hT U hUc hUo hcompact hnoncompact (hfull w hw) (hcontract w hw)
    obtain ⟨x, hx⟩ := CompactProductIsolation.mulSingle_mem_range_insertFinite D i hT w
      (Finset.mem_singleton_self _) a
    exact hx ▸ hins x
  exact ((CompactProductIsolation.projectToRemainingPlaces D i S J hd).2 hsingle).2.2.mp hrem

set_option backward.isDefEq.respectTransparency false in
/-- A singleton subproduct of completions is the original local point group. -/
private def singletonLocalPoints {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    FinitePoints D i {w} ≃ₜ* LocalPoints D i w := by
  let w₀ : (↑({w} : Finset D.Place) : Set D.Place) := ⟨w, Finset.mem_singleton_self _⟩
  letI : Unique (↑({w} : Finset D.Place) : Set D.Place) :=
    ⟨⟨w₀⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.property)⟩
  let A := fun x : (↑({w} : Finset D.Place) : Set D.Place) => LocalPoints D i x.1
  let e := MulEquiv.piUnique A
  let h := Homeomorph.piUnique A
  exact { toMulEquiv := e, continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Unipotent (Index baseChangedAlgebraicGroup)

open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups
open private matrixPresentation glVal_isEmbedding continuous_glEvaluation from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Specs.StandardGroups (GLCoordinates universalMatrix)
open LocalAlgebraicTransport (evaluation)
open AdelicGroups (PointsIn asMatrix localPoint)
open Opposite

set_option backward.isDefEq.respectTransparency false in
private theorem localPointTopology_eq_matrixTopology {F : Type u} [Field F]
    [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (J : AffineAlgebraicGroup F) (j : MatrixRealization J) :
    pointTopology J.val.X = (inferInstance : TopologicalSpace (PointsIn j F)) := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr J.prop.1
  let coords : Γ(J.val.X.left, ⊤) ⟶ CommRingCat.of A.unop :=
    e.hom.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A.unop)).hom
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hg : Function.Surjective coords := ConcreteCategory.bijective_of_isIso coords |>.2
  let evalAt (p : RationalPoints J.val.X) := (coordinateMap (p ≫ e.inv)).hom
  have heval (p : RationalPoints J.val.X) (a : Γ(J.val.X.left, ⊤)) :
      evaluation p a = evalAt p (coords a) := by
    let f := coordinateMap (p ≫ e.inv)
    have hf := congrArg Over.Hom.left (coordinateMap_spec (p ≫ e.inv))
    rw [algSpec_map_left] at hf
    have hp : (p ≫ e.inv) ≫ e.hom = p := by simp
    have hcomp : e.hom.left.appTop ≫ (p ≫ e.inv).left.appTop = p.left.appTop := by
      rw [← Scheme.Hom.comp_appTop]
      exact congrArg (fun m => m.left.appTop) hp
    change Spec.map (CommRingCat.ofHom f.hom.toRingHom) = (p ≫ e.inv).left at hf
    change (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom) a = f.hom (coords a)
    rw [← hcomp, Category.assoc, ← hf, Scheme.ΓSpecIso_naturality]
    rfl
  obtain ⟨d, hsurj, hd⟩ := matrixPresentation A.unop e j
  let mat := fun p : PointsIn j F => (asMatrix j F p).val
  have hm : IsInducing mat := glVal_isEmbedding.isInducing.comp (IsInducing.induced (asMatrix j F))
  apply le_antisymm
  · rw [hm.eq_induced]
    apply continuous_iff_le_induced.mp
    let _ := pointTopology J.val.X
    apply continuous_matrix
    intro k l
    let z := universalMatrix F (Index.{u} j.size) k l
    obtain ⟨b, hb⟩ := hg (d.hom z)
    have h (p : RationalPoints J.val.X) : (mat p) k l = evaluation p b := by
      rw [heval, hb]
      have hc := congrArg (fun f : GLCoordinates F (Index.{u} j.size) →ₐ[F] F => f z) (hd F p)
      exact (glEvaluation_entry (asMatrix j F p) k l).symm.trans hc
    simp_rw [h]
    exact (continuous_apply b).comp continuous_induced_dom
  · apply continuous_iff_le_induced.mp
    apply continuous_pi
    intro a
    simp_rw [heval]
    obtain ⟨z, hz⟩ := hsurj (coords a)
    have he (p : PointsIn j F) : evalAt p (coords a) = glEvaluation (asMatrix j F p) z := by
      rw [← hz]
      exact congrArg (fun f : GLCoordinates F (Index.{u} j.size) →ₐ[F] F => f z) (hd F p).symm
    simp_rw [he]
    exact (continuous_glEvaluation (R := F) z).comp (IsInducing.induced (asMatrix j F)).continuous


private theorem completionMatrixComparison {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    ∃ j : MatrixRealization (baseChangedAlgebraicGroup (D.Completion w) G),
      Nonempty (PointsIn j (D.Completion w) ≃ₜ* LocalPoints D i w) := by
  let F := D.Completion w
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e : PointsIn j F ≃* LocalPoints D i w :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  let l : PointsIn j F ≃ₜ LocalPoints D i w := hj.homeomorph _
  refine ⟨j, ⟨{
    toMulEquiv := e
    continuous_toFun := l.continuous
    continuous_invFun := ?_ }⟩⟩
  have he : (e.symm : LocalPoints D i w → PointsIn j F) = l.symm := by
    funext x
    apply e.injective
    exact (e.apply_symm_apply x).trans (l.apply_symm_apply x).symm
  change Continuous (e.symm : LocalPoints D i w → PointsIn j F)
  rw [he]
  exact l.symm.continuous

/-- The two point topologies used by the arithmetic and local quotient
theorems give a topological group identification over the actual completion. -/
private theorem completionPointsComparison {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    let J := baseChangedAlgebraicGroup (D.Completion w) G
    letI := pointTopology J.val.X
    Nonempty (LocalPoints D i w ≃ₜ* RationalPoints J.val.X) := by
  let F := D.Completion w
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨j, ⟨d⟩⟩ := completionMatrixComparison D i w
  let hasComparison (t : TopologicalSpace (PointsIn j F)) : Prop :=
    letI := t
    Nonempty (LocalPoints D i w ≃ₜ* PointsIn j F)
  have htop := localPointTopology_eq_matrixTopology J j
  have hd : hasComparison (inferInstance : TopologicalSpace (PointsIn j F)) := ⟨d.symm⟩
  exact (congrArg hasComparison htop).mpr hd

/-- For a finite completion satisfying the local mixing hypotheses, apply the
finite-covolume premise to the subgroup obtained by arithmetic projection. -/
private theorem fullProjectionOfFiniteCompletion (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (hG : IsAbsolutelyAlmostSimple G)
    (hmix : MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))
    (H : Subgroup (FinitePoints D i {Sum.inl w}))
    (hclosed : IsClosed (H : Set (FinitePoints D i {Sum.inl w})))
    (hnd : ¬ DiscreteTopology H) (hμ : FiniteInvariantQuotientMeasure H) : H = ⊤ := by
  let F := D.Completion (.inl w)
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  let _ : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let L := baseChangedAlgebraicGroup F G
  let _ := pointTopology L.val.X
  obtain ⟨e⟩ := completionPointsComparison D i (.inl w)
  have hL := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  have htop := LocalAlgebraicTransport.rationalPointTopologicalGroup L
  exact fullProjectionOfLocalModel hfull L hL hmix H hclosed hnd hμ htop
    ((singletonLocalPoints D i (.inl w)).trans e)

private theorem contractionOverLocalField {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (c : Cocharacter G.val) (R : LimitDecomposition c) (g : PointsIn i F)
    (hg : g ∈ ((((groupPointsFunctor F).map R.contracting.inclusion).app
      (CommAlgCat.of F F)).hom).range) : Contracted g := by
  let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let _ : Valuation.RankOne
      (Valued.v (R := F) (Γ₀ := ValuativeRel.ValueGroupWithZero F)) := by
    change Valuation.RankOne (ValuativeRel.valuation F)
    infer_instance
  let nF : NontriviallyNormedField F := Valued.toNontriviallyNormedField F
    (ValuativeRel.ValueGroupWithZero F)
  obtain ⟨t, ht⟩ := @LocalCocharacterEvaluation.contractingScalarExists.{u} F nF
  have hcont : @Continuous F F nF.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _ (algebraMap F F) := by
    change Continuous (algebraMap F F)
    simpa using (continuous_id : Continuous (id : F → F))
  exact ⟨_, @LocalCocharacterEvaluation.contractingEvaluation.{u,u}
    F _ _ _ G i c R F nF.toNormedField (Algebra.id F) hcont t ht g hg⟩

/-- Contracting elements and the groups they generate are transported with
the point topology. -/
private theorem contractedGenerationOfEquiv {P : Type u} {Q : Type v} [Group P] [Group Q]
    [TopologicalSpace P] [TopologicalSpace Q] (e : P ≃ₜ* Q)
    (h : Subgroup.closure {x : P | Contracted x} = ⊤) :
    Subgroup.closure {x : Q | Contracted x} = ⊤ := by
  apply top_unique
  rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, ← h, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha⟩ := hx
  refine ⟨e a, ?_⟩
  have hc : Continuous (e : P → Q) := e.continuous
  have ht : Tendsto (fun n : ℕ => e (a ^ n * x * (a ^ n)⁻¹)) atTop (𝓝 (e 1)) :=
    (hc.tendsto 1).comp ha
  change Tendsto (fun n : ℕ => e a ^ n * e x * (e a ^ n)⁻¹) atTop (𝓝 1)
  simpa only [map_one, map_mul, map_inv, map_pow] using ht

open Specs.GeometricRadicals (IsSplitReductive IsSplitTorus)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.RootGroups (rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.ProjectiveRecurrence (cocharacterRadicalPoints localPointSet)
open Composition.OctonionAutomorphismSpecification (IsAdjointG2)
open Composition.PeirceSpecification (ZornIsomorphism)
open Composition.Specification (normBaseChange)

open private scalarExtendedAutomorphisms automorphismAlgebraicGroup
  from LinearAlgebraicGroups.Composition.OctonionAutomorphisms
open private rootPoint_hasLimit rootPoint_surjective
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private sameSubgroupIso from LinearAlgebraicGroups.Classification.CentralIsogenies

private theorem positivePairingOfRoot {F : Type u} [Field F] {J : AffineAlgebraicGroup F}
    (T : Specs.ClosedSubgroup J.val) (hs : IsSplitTorus T.group)
    {α : Specs.CharacterDescent.Character T.group} (hα : α ∈ absoluteRoots T) :
    ∃ c : Cocharacter T.group, 0 < pairing T.group α c := by
  obtain ⟨hcomm, _, _, _, _, P, hP, hpair⟩ := RootData.CharacterPairing.perfectCharacterPairing T.group hs
  letI := hcomm
  letI := hP
  have hex : ∃ c, P (Additive.ofMul α) c ≠ 0 := by
    by_contra! h
    apply hα.1
    have hz : P (Additive.ofMul α) = 0 := LinearMap.ext h
    exact congrArg Additive.toMul (P.toPerfPair.injective (hz.trans P.toPerfPair.map_zero.symm))
  obtain ⟨c, hc⟩ := hex
  by_cases hz : 0 < P (Additive.ofMul α) c
  · exact ⟨c.toMul, (hpair α c.toMul) ▸ hz⟩
  · refine ⟨(-c).toMul, ?_⟩
    rw [← hpair]
    change 0 < P (Additive.ofMul α) (-c)
    rw [map_neg]
    omega

private theorem splitRadicalsGenerate {F : Type u} [Field F] (J : AffineAlgebraicGroup F)
    (hJ : IsAbsolutelyAlmostSimple J) (hs : IsSplitReductive J) (hsc : GeometricallySimplyConnected J) :
    Subgroup.closure (cocharacterRadicalPoints J) = ⊤ := by
  obtain ⟨hred, T, hT, hmax⟩ := hs
  apply top_unique
  rw [← SplitLocalGeneration.splitLocalGeneration J hJ.1 hsc T hT hmax]
  apply Subgroup.closure_mono
  rintro _ ⟨α, hα, U, hU, p, rfl⟩
  obtain ⟨c, hc⟩ := positivePairingOfRoot T hT hα
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition J (c ≫ T.inclusion)
  obtain ⟨_, _, W, _, _, _, ⟨L, j, hj⟩, huniq⟩ :=
    (RootData.RootGroups.rootSubgroups J hred T hT hmax).2 α hα
  obtain ⟨e, he⟩ := sameSubgroupIso (huniq U hU)
  let R := CommAlgCat.of F F
  let pW : GroupPoints W.group R := p ≫ e.inv.hom.hom
  obtain ⟨a, ha⟩ := rootPoint_surjective j R pW
  have he' : e.inv ≫ W.inclusion = U.inclusion := by rw [← he, Iso.inv_hom_id_assoc]
  have hx : rootPoint (j.hom ≫ W.inclusion) R a = p ≫ U.inclusion.hom.hom := by
    change rootPoint j.hom R a ≫ W.inclusion.hom.hom = _
    rw [ha]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun f : U.group ⟶ J.val => p ≫ f.hom.hom) he')
  refine ⟨c ≫ T.inclusion, D, ?_⟩
  exact (D.contracting_points R _).mp (hx ▸ rootPoint_hasLimit hj c hc R a)

private theorem octonionSplitAfterExtension {K C F : Type u} [Field K] [Field F] [Algebra K F]
    [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
    (G : AffineAlgebraicGroup K) (A : AutomorphismGroup K C) (e : G.val ≅ A.group)
    (q : QuadraticForm K C) (hq : OctonionNormConditions q)
    (split : letI := hq.projective; Nonempty (ZornIsomorphism (normBaseChange F q))) :
    IsSplitReductive (baseChangedAlgebraicGroup F G) ∧
      GeometricallySimplyConnected (baseChangedAlgebraicGroup F G) := by
  letI := hq.projective
  let B := scalarExtendedAutomorphisms (K := F) (automorphismGroupAlongIso G A e)
  have hn := Composition.octonion_norm_baseChange hq F
  have h := OctonionForms.splitOctonionGroupStructure hn split B
  obtain ⟨⟨hred, _, _, T, _, hT, hmax, _⟩, hsc⟩ := h
  exact ⟨⟨hred, T, hT, hmax⟩, hsc⟩

private theorem octonionFiniteSplit {K C : Type u} [Field K]
    [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
    (D : GlobalFieldData.{u,v} K) (w : D.FinitePlace)
    (G : AffineAlgebraicGroup K) (A : AutomorphismGroup K C) (e : G.val ≅ A.group)
    (q : QuadraticForm K C) (hq : OctonionNormConditions q) :
    let J := baseChangedAlgebraicGroup (D.Completion (.inl w)) G
    IsSplitReductive J ∧ GeometricallySimplyConnected J := by
  let F := D.FiniteCompletion w
  letI : Algebra K F := (D.embedding (.inl w)).toAlgebra
  have hn := Composition.octonion_norm_baseChange hq F
  exact octonionSplitAfterExtension (F := F) G A e q hq (OctonionForms.finiteCompletionSplit D w hn)

private theorem contractedGenerationOfRadicals {F : Type u} [Field F] [TopologicalSpace F]
    (J : AffineAlgebraicGroup F) (j : MatrixRealization J)
    (hgen : Subgroup.closure (cocharacterRadicalPoints J) = ⊤)
    (hc : ∀ (c : Cocharacter J.val) (L : LimitDecomposition c) (g : PointsIn j F),
      g ∈ ((((groupPointsFunctor F).map L.contracting.inclusion).app
        (CommAlgCat.of F F)).hom).range → Contracted g) :
    Subgroup.closure {g : PointsIn j F | Contracted g} = ⊤ := by
  apply top_unique
  change (⊤ : Subgroup (RationalPoints J)) ≤ _
  rw [← hgen]
  apply Subgroup.closure_mono
  rintro g ⟨c, L, hg⟩
  exact hc c L g hg

private theorem finiteSplitContractedDense {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (hG : IsAbsolutelyAlmostSimple G)
    (hs : let J := baseChangedAlgebraicGroup (D.Completion (.inl w)) G
          IsSplitReductive J ∧ GeometricallySimplyConnected J) :
    Dense (Subgroup.closure {g : FinitePoints D i {Sum.inl w} | Contracted g} :
      Set (FinitePoints D i {Sum.inl w})) := by
  let F := D.Completion (.inl w)
  let _ : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let J := baseChangedAlgebraicGroup F G
  have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  obtain ⟨j, ⟨e⟩⟩ := completionMatrixComparison D i (.inl w)
  have hl := contractedGenerationOfRadicals J j (splitRadicalsGenerate J hJ hs.1 hs.2)
    (contractionOverLocalField J j)
  rw [contractedGenerationOfEquiv (e.trans (singletonLocalPoints D i (.inl w)).symm) hl,
    Subgroup.coe_top]
  exact dense_univ

private theorem strongApproximationOfFiniteSplit (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (S J : Finset D.Place) (hd : Disjoint J S)
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hArchCompact : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → CompactSpace (LocalPoints D i (.inr w)))
    (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → Sum.inr w ∈ J)
    (hSplit : ∀ w : D.FinitePlace, let L := baseChangedAlgebraicGroup (D.Completion (.inl w)) G
      IsSplitReductive L ∧ GeometricallySimplyConnected L)
    (hrem : DenseRange (rationalProjection D i J)) :
    StrongApproximation D i S := by
  refine strongApproximationOfLocalProjections D i S J hd hArchCompact hcompact hnoncompact ?_ ?_ hrem
  · rintro ⟨w | w, hw⟩ hJ
    · exact fun H hclosed hnd hμ =>
        fullProjectionOfFiniteCompletion hfull D i w hG (Or.inl (hSplit w)) H hclosed hnd hμ
    · exact (hJ (hArch w hw)).elim
  · rintro ⟨w | w, hw⟩ hJ
    · exact finiteSplitContractedDense D i w hG (hSplit w)
    · exact (hJ (hArch w hw)).elim

/-- When there are no archimedean places, the finite split factor
argument has an empty remainder. -/
private theorem strongApproximationOfAllFiniteSplit (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hEmpty : IsEmpty D.InfinitePlace)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hSplit : ∀ w : D.FinitePlace, let L := baseChangedAlgebraicGroup (D.Completion (.inl w)) G
      IsSplitReductive L ∧ GeometricallySimplyConnected L)
    (S : Finset D.Place) (hnoncompact : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S := by
  apply strongApproximationOfFiniteSplit hfull D i hG hcompact
    S ∅ (Finset.disjoint_empty_left S) hnoncompact
  · exact fun w => (hEmpty.false w).elim
  · exact fun w => (hEmpty.false w).elim
  · exact hSplit
  · apply Function.Surjective.denseRange
    intro x
    exact ⟨1, funext fun w => (Finset.notMem_empty w.val w.property).elim⟩

end LocalProjections


section NumberFieldUniverses

open Specs.Arithmetic.ProjectiveRecurrence (evaluateArchimedean cocharacterRadicalPoints localPointSet)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private cosetMap continuous_cosetMap surjective_cosetMap
  from LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

private abbrev numberDatum (K : Type u) [Field K] [NumberField K] : GlobalFieldData.{u,v} K :=
  .number inferInstance

variable {K : Type u} [Field K] [NumberField K] {G : AffineAlgebraicGroup K}

private abbrev completionPointTopology (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (w : D.Place) : TopologicalSpace (LocalPoints D i w) :=
  inferInstance

private instance numberCompletionPointTopology (i : MatrixRealization G) (w : NumberPlace K) :
    TopologicalSpace (LocalPoints (numberDatum.{u,v} K) i w) :=
  completionPointTopology (numberDatum.{u,v} K) i w

private instance numberAdelesTopologicalGroup (i : MatrixRealization G)
    (S : Finset (NumberPlace K)) :
    IsTopologicalGroup (Adeles (numberDatum.{u,v} K) i S) :=
  adelicTopology (numberDatum.{u,v} K) i S

set_option backward.isDefEq.respectTransparency false in
private def numberPointComparison (i : MatrixRealization G) (w : NumberPlace K) :
    LocalPoints (numberDatum.{u,v} K) i w ≃ₜ* LocalPoints (numberDatum.{u,u} K) i w := by
  cases w <;> exact ContinuousMulEquiv.refl _

private theorem numberPointComparison_integral (i : MatrixRealization G) (w : NumberPlace K)
    (x : LocalPoints (numberDatum.{u,v} K) i w) :
    numberPointComparison i w x ∈ localSubgroup (numberDatum.{u,u} K) i w ↔
      x ∈ localSubgroup (numberDatum.{u,v} K) i w := by
  cases w <;> exact Iff.rfl

private theorem numberPointComparison_diagonal (i : MatrixRealization G) (w : NumberPlace K)
    (g : RationalPoints G) :
    numberPointComparison i w (localPoint (numberDatum.{u,v} K) i w g) =
      localPoint (numberDatum.{u,u} K) i w g := by
  cases w <;> rfl

set_option backward.isDefEq.respectTransparency false in
private def numberAdelesComparison (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    Adeles (numberDatum.{u,v} K) i S ≃ₜ* Adeles (numberDatum.{u,u} K) i S := by
  let D := numberDatum.{u,v} K
  let E := numberDatum.{u,u} K
  let e (w : Outside D S) := numberPointComparison.{u,v} i w.val
  have h₁ : ∀ᶠ w in Filter.cofinite, MapsTo (e w)
      (localSubgroup D i w.val) (localSubgroup E i w.val) :=
    Eventually.of_forall fun w _ hx => (numberPointComparison_integral i w.val _).mpr hx
  have h₂ : ∀ᶠ w in Filter.cofinite, MapsTo (e w).symm
      (localSubgroup E i w.val) (localSubgroup D i w.val) :=
    Eventually.of_forall fun w x hx => (numberPointComparison_integral i w.val _).mp
      ((ContinuousMulEquiv.apply_symm_apply (e w) x).symm ▸ hx)
  refine
    { toFun := RestrictedProduct.map (𝓕 := cofinite) (fun w => e w) h₁
      invFun := RestrictedProduct.map (𝓕 := cofinite) (fun w => (e w).symm) h₂
      left_inv := fun x => RestrictedProduct.ext _ _ fun w => (e w).symm_apply_apply (x w)
      right_inv := fun x => RestrictedProduct.ext _ _ fun w => (e w).apply_symm_apply (x w)
      map_mul' := fun x y => RestrictedProduct.ext _ _ fun w => (e w).map_mul (x w) (y w)
      continuous_toFun := RestrictedProduct.mapAlong_continuous
        (fun w : Outside D S => LocalPoints D i w.val)
        (fun w : Outside E S => LocalPoints E i w.val)
        id tendsto_id (fun w => e w) h₁ (fun w => (e w).continuous)
      continuous_invFun := RestrictedProduct.mapAlong_continuous
        (fun w : Outside E S => LocalPoints E i w.val)
        (fun w : Outside D S => LocalPoints D i w.val)
        id tendsto_id (fun w => (e w).symm) h₂ (fun w => (e w).symm.continuous) }

set_option backward.isDefEq.respectTransparency false in
private theorem numberAdelicCompactnessComparison (i : MatrixRealization G)
    (h : CompactSpace (Adeles (numberDatum.{u,v} K) i ∅ ⧸
      diagonalSubgroup (numberDatum.{u,v} K) i)) :
    CompactSpace (Adeles (numberDatum.{u,u} K) i ∅ ⧸ diagonalSubgroup (numberDatum.{u,u} K) i) := by
  let e := numberAdelesComparison.{u,v} i ∅
  letI := h
  have hd : diagonalSubgroup (numberDatum.{u,v} K) i ≤
      (diagonalSubgroup (numberDatum.{u,u} K) i).comap e.toMonoidHom := by
    rintro x ⟨g, hg⟩
    refine ⟨g, fun w => ?_⟩
    change numberPointComparison i w.val (x w) = _
    exact (congrArg (numberPointComparison i w.val) (hg w)).trans
      (numberPointComparison_diagonal i w.val g)
  exact (surjective_cosetMap e.toMonoidHom hd e.surjective).compactSpace
    (continuous_cosetMap e.toMonoidHom hd e.continuous)

omit [NumberField K] in
private theorem arithmeticSubgroup_integralOutside_iff (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (T : Finset D.Place) (g : RationalPoints G) :
    g ∈ arithmeticSubgroup D i T (integralOutside D i T) ↔
      ∀ w : Outside D T, localPoint D i w.val g ∈ localSubgroup D i w.val := by
  constructor
  · rintro ⟨x, hx, hg⟩ w
    exact hg w ▸ (hx w)
  · intro h
    exact ⟨diagonal D i T g, h, fun _ => rfl⟩

private theorem numberIntegralArithmeticComparison (i : MatrixRealization G)
    (T : Finset (NumberPlace K)) (g : RationalPoints G) :
    g ∈ arithmeticSubgroup (numberDatum.{u,u} K) i T (integralOutside (numberDatum.{u,u} K) i T) →
    g ∈ arithmeticSubgroup (numberDatum.{u,v} K) i T (integralOutside (numberDatum.{u,v} K) i T) := by
  intro hg
  apply (arithmeticSubgroup_integralOutside_iff _ _ _ _).mpr
  have h := (arithmeticSubgroup_integralOutside_iff _ _ _ _).mp hg
  intro w
  apply (numberPointComparison_integral i w.val _).mp
  rw [numberPointComparison_diagonal]
  exact h w

set_option backward.isDefEq.respectTransparency false in
private theorem numberArchimedeanLatticeProjection (D : GlobalFieldData.{u,v} K)
    (hD : D = .number inferInstance) (i : MatrixRealization G)
    (S T : Finset D.Place) (A : Finset D.InfinitePlace)
    (hST : S ⊆ T) (hA : A.Nonempty) (hout : ∀ w : ↑A, Sum.inr w.val ∉ S)
    (hin : ∀ w : ↑A, Sum.inr w.val ∈ T)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∉ T → CompactSpace (LocalPoints D i (.inr w)))
    (hG : IsAbsolutelyAlmostSimple G)
    (hgen : ∀ w : ↑A, Dense (↑(Subgroup.closure (localPointSet D i (.inr w.val)
      (cocharacterRadicalPoints
        (baseChangedAlgebraicGroup (D.Completion (.inr w.val)) G)))) :
      Set (LocalPoints D i (.inr w.val)))) :
    Dense (↑((lattice D i T (integralOutside D i T)).map (evaluateArchimedean D i A hin)) :
      Set (∀ w : ↑A, LocalPoints D i (.inr w.val))) := by
  subst D
  let D := numberDatum.{u,v} K
  let E := numberDatum.{u,u} K
  let p : FinitePoints D i S ≃ₜ FinitePoints E i S :=
    Homeomorph.piCongrRight (fun w => (numberPointComparison i w.val).toHomeomorph)
  have hE : ¬ CompactSpace (FinitePoints E i S) := by
    intro h
    letI := h
    exact hnoncompact (p.symm.surjective.compactSpace p.symm.continuous)
  obtain ⟨hUc, hUo⟩ := compactOpenOutside E i T hArch
  have hdense := ProjectiveRecurrence.archimedeanLatticeProjection G i E rfl S T A
    (integralOutside E i T) hST hA hout hin (numberAdelicCompactnessComparison i hcompact)
    hE hUc hUo hG hgen
  apply hdense.mono
  rintro q ⟨x, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨rationalProjection D i T g, ⟨g, numberIntegralArithmeticComparison i T g hg, rfl⟩, ?_⟩
  funext w
  rfl

end NumberFieldUniverses

section Archimedean

open Specs.Arithmetic.ProjectiveRecurrence (evaluateArchimedean cocharacterRadicalPoints localPointSet)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.GeometricRadicals (IsSplitReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Composition.Specification (normBaseChange)
open CompactProductIsolation (Contracted diagonalClosure insertFinite projectedArithmetic)
open private forgetPlaces_continuous forgetPlaces_surjective
  from LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

private theorem archimedeanOctonionDichotomy {K C : Type u} [Field K] [NumberField K]
    [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
    (G : AffineAlgebraicGroup K) (A : AutomorphismGroup K C) (e : G.val ≅ A.group)
    (q : QuadraticForm K C) (hq : OctonionNormConditions q)
    (D : GlobalFieldData.{u,v} K) (hD : D = .number inferInstance)
    (i : MatrixRealization G) (w : D.InfinitePlace) :
    let J := baseChangedAlgebraicGroup (D.Completion (.inr w)) G
    (IsSplitReductive J ∧ GeometricallySimplyConnected J) ∨
      (CompactSpace (LocalPoints D i (.inr w)) ∧ ConnectedSpace (LocalPoints D i (.inr w))) := by
  let F := D.Completion (.inr w)
  letI := hq.projective
  let qF := normBaseChange F q
  have hqF := Composition.octonion_norm_baseChange hq F
  have hCases : (∃ r : F ≃+* ℝ, Continuous r.symm) ∨ Nonempty (F ≃+* ℂ) := by
    subst D
    rcases w.isReal_or_isComplex with hw | hw
    · obtain ⟨r, hr⟩ := numberRealCompletion w hw
      let s : w.Completion ≃ᵢ ℝ := ⟨r.toEquiv, hr⟩
      exact Or.inl ⟨r, s.symm.continuous⟩
    · obtain ⟨r, _⟩ := numberComplexCompletion w hw
      exact Or.inr ⟨r⟩
  rcases hCases with hReal | hComplex
  · obtain ⟨r, hr⟩ := hReal
    letI : Algebra F ℝ := r.toRingHom.toAlgebra
    letI := hqF.projective
    let qR := normBaseChange ℝ qF
    have hqR := Composition.octonion_norm_baseChange hqF ℝ
    rcases OctonionForms.realSplitOrPositive hqR with hsplit | hp
    · obtain ⟨split⟩ := hsplit
      apply Or.inl
      apply octonionSplitAfterExtension G A e q hq
      apply Composition.Peirce.isotropic_field_split hqF
      let x := Composition.ZornSpecification.first ℝ
      have hx : x ≠ 0 := by
        intro h
        have h' := congrArg (fun z => (Composition.Zorn.coordinates ℝ z).1) h
        exact one_ne_zero (show (1 : ℝ) = 0 from h')
      have hnx : Composition.ZornSpecification.norm ℝ x = 0 := by
        rw [Composition.Zorn.norm_formula]
        change (1 : ℝ) * 0 - dotProduct (0 : Fin 3 → ℝ) 0 = 0
        simp [dotProduct]
      obtain ⟨y, hy⟩ := (baseChangeAlongEquiv (V := F ⊗[K] C) r).surjective
        (split.toLinearEquiv x)
      have hyt : (1 : ℝ) ⊗ₜ[F] y = split.toLinearEquiv x :=
        (baseChangeAlongEquiv_apply r y).symm.trans hy
      refine ⟨y, ?_, ?_⟩
      · intro h
        apply hx
        apply split.toLinearEquiv.injective
        rw [← hyt, h, TensorProduct.tmul_zero, map_zero]
      · apply r.injective
        rw [map_zero]
        calc
          r (qF y) = qR ((1 : ℝ) ⊗ₜ[F] y) := by
            rw [show qR ((1 : ℝ) ⊗ₜ[F] y) = 1 * 1 * algebraMap F ℝ (qF y) from
              Composition.normBaseChange_tmul ℝ qF (1 : ℝ) y, one_mul, one_mul]
            rfl
          _ = 0 := (congrArg qR hyt).trans ((split.map_norm x).trans hnx)
    · exact Or.inr (compactConnectedOfRealNorm D i (.inr w) A e q hq r hr hp)
  · obtain ⟨r⟩ := hComplex
    letI : IsAlgClosed F := ⟨fun f => Polynomial.Splits.of_splits_map_of_injective r.injective
      (IsAlgClosed.splits (f.map r.toRingHom)) (fun x _ => r.surjective x)⟩
    exact Or.inl (octonionSplitAfterExtension G A e q hq (OctonionForms.algebraicallyClosedSplit hqF))

private theorem splitLocalRadicalsGenerate {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place)
    (hG : IsAbsolutelyAlmostSimple G)
    (hs : let J := baseChangedAlgebraicGroup (D.Completion w) G
      IsSplitReductive J ∧ GeometricallySimplyConnected J) :
    Subgroup.closure (localPointSet D i w
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion w) G))) = ⊤ := by
  let F := D.Completion w
  let J := baseChangedAlgebraicGroup F G
  have h := splitRadicalsGenerate J
    (OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG) hs.1 hs.2
  let e : RationalPoints J ≃* LocalPoints D i w :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  have hle : (Subgroup.closure (cocharacterRadicalPoints J)).map e.toMonoidHom ≤
      Subgroup.closure (localPointSet D i w (cocharacterRadicalPoints J)) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  rw [h, Subgroup.map_top_of_surjective _ e.surjective] at hle
  exact top_unique hle

private theorem archimedeanContractedGeneration {K : Type u} [Field K] [NumberField K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (hD : D = .number inferInstance) (w : D.InfinitePlace)
    (hG : IsAbsolutelyAlmostSimple G)
    (hs : let J := baseChangedAlgebraicGroup (D.Completion (.inr w)) G
      IsSplitReductive J ∧ GeometricallySimplyConnected J) :
    Subgroup.closure {g : LocalPoints D i (.inr w) | Contracted g} = ⊤ := by
  let F := D.Completion (.inr w)
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨j, ⟨e⟩⟩ := completionMatrixComparison D i (.inr w)
  have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  have hR : ∃ a : Algebra ℝ F, letI := a; Continuous (algebraMap ℝ F) := by
    subst D
    obtain ⟨a, _, h⟩ := LocalCocharacterEvaluation.archimedeanCompletionScalars w
    exact ⟨a, h⟩
  obtain ⟨a, h⟩ := hR
  letI := a
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := ℝ)
  apply contractedGenerationOfEquiv e
  refine contractedGenerationOfRadicals J j (splitRadicalsGenerate J hJ hs.1 hs.2) ?_
  intro c L g hg
  exact ⟨_, LocalCocharacterEvaluation.contractingEvaluation J j c L h t ht g hg⟩

private theorem contractedGenerationOfFiniteProduct {I : Type*} [Finite I] {P : I → Type*}
    [∀ j, Group (P j)] [∀ j, TopologicalSpace (P j)]
    (hp : ∀ j, Subgroup.closure {g : P j | Contracted g} = ⊤) :
    Subgroup.closure {g : ∀ j, P j | Contracted g} = ⊤ := by
  let s (j : I) : Set (P j) := {g | Contracted g}
  have h1 (j : I) : 1 ∈ s j := ⟨1, by simpa using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : P j)) atTop (𝓝 1))⟩
  have hs : univ.pi s ⊆ {g : ∀ j, P j | Contracted g} := by
    intro g hg
    have hh (j : I) : Contracted (g j) := hg j (mem_univ j)
    choose a ha using hh
    exact ⟨a, tendsto_pi_nhds.mpr ha⟩
  have hle := Subgroup.closure_mono hs
  rw [Subgroup.closure_pi h1] at hle
  have he : (fun j => Subgroup.closure (s j)) = fun j => ⊤ := funext hp
  rw [he] at hle
  exact top_unique (fun x _ => hle (fun _ _ => Subgroup.mem_top _))

private theorem denseCompactRealProjection {K : Type u} [Field K] [NumberField K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (hD : D = .number inferInstance) (hG : IsAbsolutelyAlmostSimple G) (J : Finset D.Place)
    (hconn : ∀ w : (↑J : Set D.Place), ConnectedSpace (LocalPoints D i w.1)) :
    DenseRange (rationalProjection D i J) := by
  letI := hconn
  letI : ConnectedSpace (FinitePoints D i J) := inferInstance
  have hOpen : IsOpen (closure (range (rationalProjection D i J))) := by
    subst D
    exact WeakApproximationByTori.identityNeighborhood G hG.1 i J
  exact dense_iff_closure_eq.mpr
    (IsClopen.eq_univ ⟨isClosed_closure, hOpen⟩
      ⟨rationalProjection D i J 1, subset_closure ⟨1, rfl⟩⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem isolateSplitArchimedean {K : Type u} [Field K] [NumberField K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (hD : D = .number inferInstance) (hG : IsAbsolutelyAlmostSimple G)
    (S : Finset D.Place) (J : Finset D.Place) (A : Finset D.InfinitePlace)
    (hJ : J = A.map ⟨Sum.inr, Sum.inr_injective⟩) (hd : Disjoint J S)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S ∪ J → CompactSpace (LocalPoints D i (.inr w)))
    (hs : ∀ w : ↑A, let L := baseChangedAlgebraicGroup (D.Completion (.inr w.val)) G
      IsSplitReductive L ∧ GeometricallySimplyConnected L) :
    ((CompactProductIsolation.forgetOutside D i (S := S) (T := S ∪ J)
      Finset.subset_union_left).ker : Set (Adeles D i S)) ⊆ diagonalClosure D i S := by
  classical
  by_cases hA : A.Nonempty
  · let e : (↑A : Set D.InfinitePlace) ≃ (↑J : Set D.Place) :=
      Equiv.ofBijective (fun w => ⟨Sum.inr w.val, hJ.symm ▸ Finset.mem_map.mpr ⟨w.val, w.property, rfl⟩⟩)
        ⟨fun x y h => Subtype.ext (Sum.inr_injective (congrArg Subtype.val h)), fun w => by
          have hw : w.val ∈ A.map ⟨Sum.inr, Sum.inr_injective⟩ := hJ ▸ w.property
          obtain ⟨b, hb, he⟩ := Finset.mem_map.mp hw
          exact ⟨⟨b, hb⟩, Subtype.ext he⟩⟩
    let E := Homeomorph.piCongrLeft (Y := fun w : (↑J : Set D.Place) => LocalPoints D i w.val) e
    have hout (w : ↑A) : Sum.inr w.val ∉ S := Finset.disjoint_left.mp hd (e w).property
    have hin (w : ↑A) : Sum.inr w.val ∈ S ∪ J := Finset.mem_union_right S (e w).property
    let U := integralOutside D i (S ∪ J)
    obtain ⟨hUc, hUo⟩ := compactOpenOutside D i (S ∪ J) hArch
    have hgen (w : ↑A) : Dense (↑(Subgroup.closure (localPointSet D i (.inr w.val)
        (cocharacterRadicalPoints
          (baseChangedAlgebraicGroup (D.Completion (.inr w.val)) G)))) :
        Set (LocalPoints D i (.inr w.val))) := by
      rw [splitLocalRadicalsGenerate D i (.inr w.val) hG (hs w), Subgroup.coe_top]
      exact dense_univ
    have hproj : Dense (↑((lattice D i (S ∪ J) U).map (evaluateArchimedean D i A hin)) :
        Set (∀ w : ↑A, LocalPoints D i (.inr w.val))) := by
      exact numberArchimedeanLatticeProjection D hD i S (S ∪ J) A
        Finset.subset_union_left hA hout hin hcompact hnoncompact hArch hG hgen
    have hproj' := E.surjective.denseRange.dense_image E.continuous hproj
    have hdense : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
      apply hproj'.mono
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, E.symm.injective ?_⟩
      exact (E.symm_apply_apply _).symm
    have hcontract (w : (↑J : Set D.Place)) :
        Subgroup.closure {g : LocalPoints D i w.val | Contracted g} = ⊤ := by
      obtain ⟨b, rfl⟩ := e.surjective w
      exact archimedeanContractedGeneration D i hD b.val hG (hs b)
    have hgc : Dense (Subgroup.closure {g : FinitePoints D i J | Contracted g} :
        Set (FinitePoints D i J)) := by
      rw [contractedGenerationOfFiniteProduct hcontract, Subgroup.coe_top]
      exact dense_univ
    rintro x hx
    rw [← CompactProductIsolation.range_insertFinite_eq_ker D i hd] at hx
    obtain ⟨a, rfl⟩ := hx
    exact (CompactProductIsolation.isolateAdelicFactors D i S J hd U hUc hUo).2 hdense hgc a
  · have hA' : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hJe : J = ∅ := by rw [hJ, hA', Finset.map_empty]
    subst hJe
    rintro x hx
    rw [← CompactProductIsolation.range_insertFinite_eq_ker D i hd] at hx
    obtain ⟨a, rfl⟩ := hx
    have heq : insertFinite D i S ∅ a = 1 := by
      apply RestrictedProduct.ext
      intro w
      simp [CompactProductIsolation.insertFinite_apply]
    rw [heq, ← CompactProductIsolation.diagonalClosedSubgroup_coe]
    exact (CompactProductIsolation.diagonalClosedSubgroup D i S).one_mem

private theorem octonionNumberFieldStrongApproximation (hfull : FiniteCovolumeSubgroup.{u})
    {K C : Type u} [Field K] [NumberField K] [NonAssocRing C] [Module K C]
    [IsScalarTower K C C] [SMulCommClass K C C]
    (G : AffineAlgebraicGroup K) (A : AutomorphismGroup K C) (e : G.val ≅ A.group)
    (q : QuadraticForm K C) (hq : OctonionNormConditions q) (ha : ∀ x, q x = 0 → x = 0)
    (hG : IsAbsolutelyAlmostSimple G) (D : GlobalFieldData.{u,v} K)
    (hD : D = .number inferInstance) (i : MatrixRealization G)
    (S : Finset D.Place) (hS : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S := by
  classical
  have hF : Finite D.InfinitePlace := by
    subst D
    exact inferInstanceAs (Finite (NumberField.InfinitePlace K))
  letI := Fintype.ofFinite D.InfinitePlace
  let Split (w : D.InfinitePlace) : Prop :=
    let L := baseChangedAlgebraicGroup (D.Completion (.inr w)) G
    IsSplitReductive L ∧ GeometricallySimplyConnected L
  let Aₛ : Finset D.InfinitePlace := Finset.univ.filter fun w => Sum.inr w ∉ S ∧ Split w
  let J : Finset D.Place := Aₛ.map ⟨Sum.inr, Sum.inr_injective⟩
  let T := S ∪ J
  have hJ : Disjoint J S := by
    apply Finset.disjoint_left.mpr
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hw
    exact (Finset.mem_filter.mp hx).2.1
  have hArch (w : D.InfinitePlace) (hw : Sum.inr w ∉ T) :
      CompactSpace (LocalPoints D i (.inr w)) ∧ ConnectedSpace (LocalPoints D i (.inr w)) := by
    rcases archimedeanOctonionDichotomy G A e q hq D hD i w with hs | h
    · have hws : Sum.inr w ∉ S := fun h => hw (Finset.mem_union_left J h)
      have hwA : w ∈ Aₛ := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hws, hs⟩
      have hwJ : Sum.inr w ∈ J := Finset.mem_map.mpr ⟨w, hwA, rfl⟩
      exact (hw (Finset.mem_union_right S hwJ)).elim
    · exact h
  have hcomp := compactOctonionAdelicQuotient D q A e hq ha i
  have hk := isolateSplitArchimedean D i hD hG S J Aₛ rfl hJ hcomp hS
    (fun w hw => (hArch w hw).1) (fun w => (Finset.mem_filter.mp w.property).2.2)
  have hST : S ⊆ T := Finset.subset_union_left
  refine ((CompactProductIsolation.enlargeOmittedSet D i S T hST).2 hk).2.2.mp ?_
  have hT : ¬ CompactSpace (FinitePoints D i T) := by
    intro h
    letI := h
    exact hS ((forgetPlaces_surjective D i hST).compactSpace (forgetPlaces_continuous D i hST))
  let B : Finset D.InfinitePlace := Finset.univ.filter fun w => Sum.inr w ∉ T
  let R : Finset D.Place := B.map ⟨Sum.inr, Sum.inr_injective⟩
  have hR : Disjoint R T := by
    apply Finset.disjoint_left.mpr
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hw
    exact (Finset.mem_filter.mp hx).2
  refine strongApproximationOfFiniteSplit hfull D i hG hcomp T R hR hT
    (fun w hw => (hArch w hw).1)
    (fun w hw => Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩)
    (fun w => octonionFiniteSplit D w G A e q hq) ?_
  apply denseCompactRealProjection D i hD hG R
  intro w
  obtain ⟨b, hb, he⟩ := Finset.mem_map.mp w.property
  exact he ▸ (hArch b (Finset.mem_filter.mp hb).2).2

end Archimedean

/-- Conditional adelic compactness and strong approximation for anisotropic octonions. -/
theorem octonion_conditional
    (_ : LocalNormalClosure.{u}) (hfull : FiniteCovolumeSubgroup.{u}) :
    Specs.Arithmetic.AnisotropicOctonionApproximation.Octonion.{u,v} := by
  intro K C _ D _ _ _ _ q A hq ha G hG _ _ ⟨e⟩ i
  refine ⟨compactOctonionAdelicQuotient D q A e hq ha i, ?_⟩
  intro S _ hS
  cases D with
  | number hn =>
    letI := hn
    exact octonionNumberFieldStrongApproximation hfull G A e q hq ha hG (.number hn) rfl i S hS
  | function F t =>
    let D : GlobalFieldData.{u,v} K := .function F t
    exact strongApproximationOfAllFiniteSplit hfull D i hG ⟨PEmpty.elim⟩
      (compactOctonionAdelicQuotient D q A e hq ha i)
      (fun w => octonionFiniteSplit D w G A e q hq) S hS


end LinearAlgebraicGroups.Arithmetic.AnisotropicOctonionApproximation

universe v8_closure_33907f70281f0072_u0 v8_closure_33907f70281f0072_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicOctonionApproximation».«octonion» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«AnisotropicOctonionApproximation».«Octonion».{v8_closure_33907f70281f0072_u0, v8_closure_33907f70281f0072_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicOctonionApproximation».«octonion_conditional».{v8_closure_33907f70281f0072_u0, v8_closure_33907f70281f0072_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localNormalClosure».{v8_closure_33907f70281f0072_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localProjectedClosure».{v8_closure_33907f70281f0072_u0})
