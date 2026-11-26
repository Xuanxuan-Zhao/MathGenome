import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicAdNilpotents
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Free
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
universe u v w

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicAdNilpotents

open AlgebraicGeometry CategoryTheory Opposite Coalgebra TensorProduct WithConv LieAlgebra
open LinearAlgebraicGroups.Specs
open scoped TensorProduct

noncomputable section

open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private semisimpleDerivation semisimpleOnCoordinates_eq localJordan restrictInvariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer

/-- An adjoint-nilpotent element in a Killing Lie algebra is an eigenvector
of a rational adjoint operator, with eigenvalue two. -/
private theorem exists_bracket_eq_two_smul {k L : Type u} [Field k] [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] [IsKilling k L]
    (e : L) (he : IsNilpotent (ad k L e)) :
    ∃ h : L, ⁅h, e⁆ = (2 : k) • e := by
  let B := killingForm k L
  let f : Module.End k L := ad k L e
  have hB : B.Nondegenerate := IsKilling.killingForm_nondegenerate k L
  have hs : B.IsRefl := (LieModule.traceForm_isSymm k L L).isRefl
  have ho : B.orthogonal (LinearMap.range f) = LinearMap.ker f := by
    ext x
    rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker]
    constructor
    · intro hx
      apply hB.2
      intro y
      have hy := hx (f y) (LinearMap.mem_range_self f y)
      change killingForm k L ⁅e, y⁆ x = 0 at hy
      change killingForm k L y ⁅e, x⁆ = 0
      rw [LieModule.traceForm_apply_lie_apply' k L L, neg_eq_zero] at hy
      exact hy
    · intro hx y hy
      obtain ⟨z, rfl⟩ := hy
      change killingForm k L ⁅e, z⁆ x = 0
      rw [LieModule.traceForm_apply_lie_apply' k L L]
      change - B z (f x) = 0
      rw [hx, map_zero, neg_zero]
  have he' : e ∈ B.orthogonal (LinearMap.ker f) := by
    intro x hx
    have hxe : ⁅e, x⁆ = 0 := hx
    have hcomm : Commute (ad k L x) (ad k L e) := by
      let : LieRing (Module.End k L) := LieRing.ofAssociativeRing
      apply commute_iff_lie_eq.mpr
      rw [← LieHom.map_lie, ← lie_skew x e, hxe, neg_zero, map_zero]
    rw [killingForm_apply_apply, ← Module.End.mul_eq_comp, ← isNilpotent_iff_eq_zero]
    exact LinearMap.isNilpotent_trace_of_isNilpotent (hcomm.isNilpotent_mul_left he)
  rw [← ho, LinearMap.BilinForm.orthogonal_orthogonal hB hs] at he'
  obtain ⟨x, hx⟩ := he'
  change ⁅e, x⁆ = e at hx
  refine ⟨-(2 : k) • x, ?_⟩
  rw [smul_lie, ← lie_skew x e, hx, smul_neg, neg_smul, neg_neg]

section Weighting

open scoped MonoidAlgebra

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Bialgebra k A]

set_option maxHeartbeats 650000 in
/-- When the eigenspaces span the coordinate algebra, weighting the counit
on each eigenspace gives a bialgebra homomorphism to the group algebra. -/
private theorem exists_weightBialgHom {J : Type*} [AddCommGroup J]
    (D : Derivation k A A)
    (hinv : (comul (R := k)).comp D.toLinearMap =
      (D.toLinearMap.lTensor A).comp comul)
    (htop : (⨆ μ : k, Module.End.eigenspace D.toLinearMap μ) = ⊤)
    (w : k →+ J) :
    ∃ f : A →ₐc[k] MonoidAlgebra k (Multiplicative J), ∀ (μ : k) (a : A),
      D a = μ • a →
      f a = MonoidAlgebra.single (Multiplicative.ofAdd (w μ)) (counit (R := k) a) := by
  classical
  let E : k → Submodule k A := Module.End.eigenspace D.toLinearMap
  let C := MonoidAlgebra k (Multiplicative J)
  let : DirectSum.Decomposition E :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.eigenspaces_iSupIndep D.toLinearMap) htop).chooseDecomposition
  let component (μ : k) : E μ →ₗ[k] C :=
    (MonoidAlgebra.lsingle (Multiplicative.ofAdd (w μ))).comp
      ((counit (R := k)).comp (E μ).subtype)
  let F : A →ₗ[k] C :=
    (DirectSum.toModule k k C component).comp (DirectSum.decomposeLinearEquiv E).toLinearMap
  have hF (μ : k) (a : A) (ha : a ∈ E μ) :
      F a = MonoidAlgebra.single (Multiplicative.ofAdd (w μ)) (counit (R := k) a) := by
    change (DirectSum.toModule k k C component) (DirectSum.decompose E a) = _
    rw [DirectSum.decompose_of_mem E ha]
    exact DirectSum.toModule_lof (φ := component) k μ (⟨a, ha⟩ : E μ)
  have hind {p : A → Prop} (he : ∀ μ a, a ∈ E μ → p a) (hz : p 0)
      (ha : ∀ a b, p a → p b → p (a + b)) (a : A) : p a :=
    Submodule.iSup_induction E (motive := p) (htop.symm ▸ Submodule.mem_top) he hz ha
  have h1 : F 1 = 1 := by
    rw [hF 0 1 (Module.End.mem_eigenspace_iff.mpr (by simp)), map_zero, Bialgebra.counit_one]
    rfl
  let f : A →ₐ[k] C :=
    { toFun := F
      map_zero' := F.map_zero
      map_add' := F.map_add
      map_one' := h1
      map_mul' := by
        intro a b
        induction a using hind generalizing b with
        | hz => simp
        | ha a c ha hc => simp [add_mul, ha, hc]
        | he μ a ha =>
          induction b using hind with
          | hz => simp
          | ha b c hb hc => simp [mul_add, hb, hc]
          | he ν b hb =>
            have hab : a * b ∈ E (μ + ν) := by
              rw [Module.End.mem_eigenspace_iff]
              change D (a * b) = _
              rw [D.leibniz, show D a = μ • a from Module.End.mem_eigenspace_iff.mp ha,
                show D b = ν • b from Module.End.mem_eigenspace_iff.mp hb, add_smul,
                smul_eq_mul, smul_eq_mul, mul_smul_comm, mul_smul_comm, mul_comm b a, add_comm]
            rw [hF _ _ hab, hF _ _ ha, hF _ _ hb, MonoidAlgebra.single_mul_single,
              map_add, Bialgebra.counit_mul]
            rfl
      commutes' x := by
        rw [Algebra.algebraMap_eq_smul_one, F.map_smul, h1, Algebra.smul_def, mul_one] }
  refine ⟨BialgHom.ofAlgHom f ?_ ?_, fun μ a ha ↦ hF μ a (Module.End.mem_eigenspace_iff.mpr ha)⟩
  · ext a
    change counit (R := k) (F a) = counit (R := k) a
    induction a using hind with
    | hz => simp
    | ha a b ha hb => simp [ha, hb]
    | he μ a ha =>
      rw [hF μ a ha]
      exact MonoidAlgebra.counit_single _ _
  · ext a
    change Algebra.TensorProduct.map f f (comul (R := k) a) = comul (R := k) (F a)
    induction a using hind with
    | hz => simp
    | ha a b ha hb => simp [ha, hb]
    | he μ a ha =>
      have hE : E μ = D.toLinearMap.eqLocus (μ • (LinearMap.id : A →ₗ[k] A)) := by
        ext x
        rw [Module.End.mem_eigenspace_iff, LinearMap.mem_eqLocus]
        rfl
      have hΔ : comul (R := k) a ∈ LinearMap.range ((E μ).subtype.lTensor A) := by
        rw [hE]
        have heq := Module.Flat.eqLocus_lTensor_eq k A D.toLinearMap
          (μ • (LinearMap.id : A →ₗ[k] A))
        change _ ∈ LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor k A _) 
        rw [← heq]
        change D.toLinearMap.lTensor A (comul (R := k) a) =
          (μ • (LinearMap.id : A →ₗ[k] A)).lTensor A (comul (R := k) a)
        rw [LinearMap.lTensor_smul, LinearMap.lTensor_id, ← LinearMap.comp_apply,
          ← hinv, LinearMap.comp_apply]
        change comul (R := k) (D a) = μ • comul (R := k) a
        have hda : D a = μ • a := Module.End.mem_eigenspace_iff.mp ha
        rw [hda, map_smul]
      obtain ⟨z, hz⟩ := hΔ
      let p : A ⊗[k] A →ₗ[k] A :=
        (TensorProduct.rid k A).toLinearMap.comp ((counit (R := k)).lTensor A)
      let m := Multiplicative.ofAdd (w μ)
      have hcalc (z : A ⊗[k] E μ) :
          Algebra.TensorProduct.map f f ((E μ).subtype.lTensor A z) =
            F (p ((E μ).subtype.lTensor A z)) ⊗ₜ[k] (MonoidAlgebra.single m (1 : k) : C) := by
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
          rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul]
          change F x ⊗ₜ[k] F y.val = F (counit (R := k) y.val • x) ⊗ₜ[k] _
          rw [hF μ y.val y.property, F.map_smul, TensorProduct.smul_tmul]
          congr 1
          rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
        | add x y hx hy => simp [hx, hy, TensorProduct.add_tmul]
      rw [← hz, hcalc, hz]
      have hp : p (comul (R := k) a) = a := by
        simp [p, Coalgebra.lTensor_counit_comul]
      rw [hp, hF μ a ha]
      have hcomul := (MonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) m).comul_eq_tmul_self
      change (MonoidAlgebra.single m _ : C) ⊗ₜ[k] _ = _
      rw [show (MonoidAlgebra.single m (counit (R := k) a) : C) =
        (counit (R := k) a) • MonoidAlgebra.single m 1 by rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one],
        map_smul, hcomul, TensorProduct.smul_tmul']

end Weighting

section Descent

variable {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]
variable {A : Type w} [CommRing A] [Bialgebra k A]

private theorem comul_one_tmul (a : A) :
    comul (R := K) ((1 : K) ⊗ₜ[k] a) =
      TensorProduct.AlgebraTensorModule.distribBaseChange k K A A ((1 : K) ⊗ₜ[k] comul (R := k) a) := by
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
  generalize comul (R := k) a = t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y => rfl

private theorem descend_bialgHom {B : Type*} [CommRing B] [Bialgebra k B]
    (f : (K ⊗[k] A) →ₐc[K] (K ⊗[k] B))
    (hf : ∀ a : A, ∃ b : B, (1 : K) ⊗ₜ[k] b = f ((1 : K) ⊗ₜ[k] a)) :
    ∃ g : A →ₐc[k] B, ∀ a, (1 : K) ⊗ₜ[k] g a = f ((1 : K) ⊗ₜ[k] a) := by
  let iA : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let iB : B →ₐ[k] K ⊗[k] B := Algebra.TensorProduct.includeRight
  have hinj : Function.Injective iB :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  let g0 : A → B := fun a ↦ (hf a).choose
  have hg0 (a : A) : iB (g0 a) = f (iA a) := (hf a).choose_spec
  let g : A →ₐ[k] B := {
    toFun := g0
    map_zero' := hinj (by rw [hg0, map_zero, map_zero, map_zero])
    map_one' := hinj (by rw [hg0, map_one, map_one, map_one])
    map_add' a b := hinj (by rw [hg0, map_add iB, hg0, hg0, map_add, map_add])
    map_mul' a b := hinj (by rw [hg0, map_mul iB, hg0, hg0, map_mul, map_mul])
    commutes' a := hinj (by
      rw [hg0, iA.commutes, iB.commutes]
      change f.toAlgHom.restrictScalars k (algebraMap k _ a) = algebraMap k _ a
      exact (f.toAlgHom.restrictScalars k).commutes a) }
  refine ⟨BialgHom.ofAlgHom g ?_ ?_, hg0⟩
  · ext a : 1
    change counit (R := k) (g a) = counit (R := k) a
    apply (algebraMap k K).injective
    have h := CoalgHomClass.counit_comp_apply f (iA a)
    rw [← hg0] at h
    change counit (R := K) ((1 : K) ⊗ₜ[k] g a) =
      counit (R := K) ((1 : K) ⊗ₜ[k] a) at h
    simpa only [TensorProduct.counit_tmul, Bialgebra.counit_one, one_mul, Algebra.smul_def,
      mul_one] using h
  · ext a : 1
    apply (Algebra.TensorProduct.includeRight_injective (B := B ⊗[k] B)
      (algebraMap k K).injective)
    apply (TensorProduct.AlgebraTensorModule.distribBaseChange k K B B).injective
    change TensorProduct.AlgebraTensorModule.distribBaseChange k K B B
        ((1 : K) ⊗ₜ[k] Algebra.TensorProduct.map g g (comul (R := k) a)) =
      TensorProduct.AlgebraTensorModule.distribBaseChange k K B B ((1 : K) ⊗ₜ[k] comul (R := k) (g a))
    rw [← comul_one_tmul, show (1 : K) ⊗ₜ[k] g a = f ((1 : K) ⊗ₜ[k] a) from hg0 a,
      ← CoalgHomClass.map_comp_comul_apply, comul_one_tmul]
    generalize comul (R := k) a = t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul]
      simp only [LinearMap.coe_ofClass]
      rw [show (1 : K) ⊗ₜ[k] g x = f ((1 : K) ⊗ₜ[k] x) from hg0 x,
        show (1 : K) ⊗ₜ[k] g y = f ((1 : K) ⊗ₜ[k] y) from hg0 y]

end Descent

section Adjoint

open Specs.SemisimpleLieCentralizer (InvariantDerivation IsInvariant)
open private tangentComparison tangentComparison_matrix universalMatrix_coaction
  coactionOperator coactionOperator_matrix coactionOperator_intertwines semisimpleOnCoordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
/-- An adjoint eigenvector gives a matrix coefficient of the same weight
for the invariant derivation on the coordinate algebra. -/
private theorem adjoint_eigenfunction {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) (A : HopfAlgebraCategory k)
    (i : specGroup A ≅ G.val) (h e : Lie k G.val) (c : k)
    (he : s.lieRing.toBracket.bracket h e =
      s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul c e)
    (hne : e ≠ @Zero.zero (Lie k G.val) s.lieRing.toAddCommGroup.toZero) :
    ∃ (D : InvariantDerivation A) (a : A), D.val a = c • a ∧ counit (R := k) a = 1 := by
  classical
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, b, _, L, l, Ad, _, hAd, _⟩ :=
    LinearAlgebraicGroups.adjointRepresentation k G s
  let ι := ULift.{u} (Fin n)
  let q := LinearAlgebraicGroups.hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso i
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let D := (tangentComparison A G.val q).symm h
  let M := RationalRepresentations.universalMatrix A G' L.val q l Ad
  have hM := universalMatrix_coaction A G' q L.val l Ad
  have hdiff : InfinitesimalCommutator.matrixDifferential Ad l h =
      Specs.SemisimpleLieCentralizer.matrixAction A M D := by
    rw [← tangentComparison_matrix A G' q L.val l Ad D]
    exact congrArg (InfinitesimalCommutator.matrixDifferential Ad l)
      ((tangentComparison A G.val q).apply_symm_apply h).symm
  let b' := Pi.basisFun k ι
  let ρ := RationalRepresentations.coactionOfMatrix A b' M hM
  let v : ι → k := b.equivFun e
  have hv : coactionOperator A D ρ v = c • v := by
    change coactionOperator A D (RationalRepresentations.coactionOfMatrix A b' M hM) v = _
    rw [coactionOperator_matrix, Matrix.toLinAlgEquiv'_apply, ← hdiff, hAd, he]
    exact LinearEquiv.map_smul b.equivFun c e
  have hvne : v ≠ 0 := fun H =>
    hne (b.equivFun.injective (H.trans b.equivFun.map_zero.symm))
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! H
    exact hvne (funext H)
  let C := RationalRepresentations.tensorCoordinate (C := A) b' j
  let a := C (ρ.coaction v)
  have hC : D.val.toLinearMap.comp C = C.comp (D.val.toLinearMap.lTensor (ι → k)) := by
    apply TensorProduct.ext'
    intro x y
    change D.val ((b'.coord j x) • y) = (b'.coord j x) • D.val y
    exact D.val.toLinearMap.map_smul _ _
  have hDa : D.val a = c • a := by
    change ((D.val.toLinearMap.comp C).comp ρ.coaction) v = _
    rw [hC, LinearMap.comp_assoc, ← coactionOperator_intertwines A D ρ]
    change C (ρ.coaction (coactionOperator A D ρ v)) = _
    rw [hv, map_smul, map_smul]
  let U := (TensorProduct.rid k (ι → k)).toLinearMap.comp ((counit (R := k) (A := A)).lTensor _)
  have hε : (counit (R := k)).comp C = (b'.coord j).comp U := by
    apply TensorProduct.ext'
    intro x y
    change counit (R := k) ((b'.coord j x) • y) =
      b'.coord j ((counit (R := k) y) • x)
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  have hεa : counit (R := k) a = v j := by
    change ((counit (R := k)).comp C) (ρ.coaction v) = _
    rw [hε]
    change b'.coord j (U (ρ.coaction v)) = _
    rw [show U (ρ.coaction v) = v from ρ.counit v]
    simp [b']
  refine ⟨D, (v j)⁻¹ • a, ?_, ?_⟩
  · change D.val.toLinearMap ((v j)⁻¹ • a) = _
    rw [map_smul, show D.val.toLinearMap a = c • a from hDa, smul_comm]
  · rw [map_smul, hεa, smul_eq_mul, inv_mul_cancel₀ hj]

private theorem semisimpleDerivation_eigen {k : Type u} [Field k] [PerfectField k]
    (A : HopfAlgebraCategory k) (D : InvariantDerivation A) (a : A) (c : k)
    (ha : D.val a = c • a) : (semisimpleDerivation A D).val a = c • a := by
  obtain ⟨W, hW⟩ := (RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule a
  let : FiniteDimensional k W.val := W.property.2
  let x : W.val := ⟨a, hW⟩
  let J := localJordan A D W
  have hx : restrictInvariant A D W x = c • x := Subtype.ext ha
  have hj := J.property
  have hcomm : Commute (restrictInvariant A D W) J.val.1 :=
    (congrArg (fun T => Commute T J.val.1) hj.sum).mpr ((Commute.refl _).add_left hj.commute.symm)
  have hsub : restrictInvariant A D W - J.val.1 = J.val.2 := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have h := congrArg (fun f : Module.End k W.val => (f y).val) hj.sum
    change (restrictInvariant A D W y).val = (J.val.1 y).val + (J.val.2 y).val at h
    change (restrictInvariant A D W y).val - (J.val.1 y).val = (J.val.2 y).val
    rw [h, add_sub_cancel_left]
  have hnil : IsNilpotent (restrictInvariant A D W - J.val.1) := hsub.symm ▸ hj.nilpotent
  have hs := Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
    (Module.End.mem_genEigenspace_one.mpr hx) hcomm hj.semisimple.isFinitelySemisimple hnil
  change semisimpleOnCoordinates A D x.val = _
  rw [semisimpleOnCoordinates_eq A D W x]
  exact congrArg Subtype.val hs

end Adjoint

section ScalarExtension

open Specs.SemisimpleLieCentralizer (InvariantDerivation IsInvariant)
open private isSemisimple_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private def extendDerivation {A : Type u} [CommRing A] [Algebra k A]
    (D : Derivation k A A) : Derivation K (K ⊗[k] A) (K ⊗[k] A) where
  toLinearMap := D.toLinearMap.baseChange K
  map_one_eq_zero' := by
    change D.toLinearMap.baseChange K ((1 : K) ⊗ₜ[k] (1 : A)) = 0
    simp
  leibniz' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | tmul c d =>
        simp only [smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
        change (a * c) ⊗ₜ[k] D (b * d) =
          (a * c) ⊗ₜ[k] (b * D d) + (c * a) ⊗ₜ[k] (d * D b)
        rw [D.leibniz, smul_eq_mul, smul_eq_mul, TensorProduct.tmul_add, mul_comm c a]
      | add y z hy hz =>
        simp only [smul_eq_mul, mul_add, add_mul, map_add] at hy hz ⊢
        rw [hy, hz]
        abel
    | add x z hx hz =>
      simp only [smul_eq_mul, mul_add, add_mul, map_add] at hx hz ⊢
      rw [hx, hz]
      abel

private theorem extendDerivation_invariant (A : HopfAlgebraCategory k)
    (S : InvariantDerivation A) : IsInvariant (extendHopf K A)
      (extendDerivation (K := K) S.val).toLinearMap := by
  let T := S.val.toLinearMap.baseChange K
  let E := K ⊗[k] A
  let dist := TensorProduct.AlgebraTensorModule.distribBaseChange k K A A
  have hdist (x : A ⊗[k] A) :
      T.lTensor E (dist ((1 : K) ⊗ₜ[k] x)) =
        dist ((1 : K) ⊗ₜ[k] S.val.toLinearMap.lTensor A x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, LinearMap.lTensor_tmul,
        LinearMap.baseChange_tmul, LinearMap.lTensor_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  apply LinearMap.ext
  intro z
  change comul (R := K) (T z) = T.lTensor E (comul (R := K) z)
  induction z using TensorProduct.inductionOn with
  | tmul r a =>
    have hr : r ⊗ₜ[k] a = r • ((1 : K) ⊗ₜ[k] a) := by
      simp [TensorProduct.smul_tmul', smul_eq_mul]
    simp only [hr, map_smul]
    congr 1
    rw [LinearMap.baseChange_tmul, comul_one_tmul, comul_one_tmul, hdist]
    exact congrArg (fun x => dist ((1 : K) ⊗ₜ[k] x)) (LinearMap.congr_fun S.property a)
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem semisimpleDerivation_span [PerfectField k] [IsAlgClosed K]
    (A : HopfAlgebraCategory k) (D : InvariantDerivation A) :
    (⨆ μ : K, Module.End.eigenspace ((semisimpleDerivation A D).val.toLinearMap.baseChange K) μ) = ⊤ := by
  let S := (semisimpleDerivation A D).val.toLinearMap
  let E := Module.End.eigenspace (S.baseChange K)
  suffices h : ∀ z : K ⊗[k] A, z ∈ ⨆ μ, E μ by exact eq_top_iff.mpr fun z _ => h z
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r a =>
    obtain ⟨W, hW⟩ := (RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule a
    let : FiniteDimensional k W.val := W.property.2
    let J := localJordan A D W
    let I := W.val.subtype.baseChange K
    let T := J.val.1.baseChange K
    have hI : W.val.subtype.comp J.val.1 = S.comp W.val.subtype :=
      LinearMap.ext fun x => (semisimpleOnCoordinates_eq A D W x).symm
    have hIK : I.comp T = (S.baseChange K).comp I := by
      simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange K) hI
    have hT : (⨆ μ : K, Module.End.eigenspace T μ) = ⊤ :=
      (isSemisimple_baseChange J.property.semisimple).iSup_eigenspace_eq_top
    have hImage : ∀ z, I z ∈ ⨆ μ, E μ := by
      intro z
      refine Submodule.iSup_induction (Module.End.eigenspace T)
        (motive := fun z => I z ∈ ⨆ μ, E μ)
        (hT.symm ▸ (Submodule.mem_top : z ∈ (⊤ : Submodule K (K ⊗[k] W.val)))) ?_ ?_ ?_
      · intro μ x hx
        apply Submodule.mem_iSup_of_mem μ
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [← LinearMap.comp_apply, ← hIK, LinearMap.comp_apply, hx, map_smul]
      · simp
      · exact fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy
    exact hImage (r ⊗ₜ[k] (⟨a, hW⟩ : W.val))
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end ScalarExtension

section GaloisDescent

open Specs.SemisimpleLieCentralizer (InvariantDerivation)
open Descent (SemilinearAction)
open scoped MonoidAlgebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option maxHeartbeats 700000 in
private theorem weight_equivariant (A : HopfAlgebraCategory k) {J : Type u} [AddCommGroup J]
    (S : Derivation k A A) (w : K →+ J)
    (hw : ∀ (σ : K ≃ₐ[k] K) (μ : K), w (σ μ) = w μ)
    (htop : (⨆ μ : K, Module.End.eigenspace (S.toLinearMap.baseChange K) μ) = ⊤)
    (f : (K ⊗[k] A) →ₐc[K] MonoidAlgebra K (Multiplicative J))
    (hf : ∀ (μ : K) (a : K ⊗[k] A), S.toLinearMap.baseChange K a = μ • a →
      f a = MonoidAlgebra.single (Multiplicative.ofAdd (w μ)) (counit (R := K) a))
    (σ : K ≃ₐ[k] K) (a : K ⊗[k] A) :
    f ((SemilinearAction.scalarExtension (K := K) A).act σ a) =
      MonoidAlgebra.mapRingHom (Multiplicative J) σ.toRingHom (f a) := by
  let g := (SemilinearAction.scalarExtension (K := K) A).act σ
  let T := S.toLinearMap.baseChange K
  have hT (z : K ⊗[k] A) : T (g z) = g (T z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s a => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hε (z : K ⊗[k] A) : counit (R := K) (g z) = σ (counit (R := K) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s a =>
      change counit (R := K) (σ s ⊗ₜ[k] a) = σ (counit (R := K) (s ⊗ₜ[k] a))
      simp [TensorProduct.counit_tmul, Algebra.smul_def]
    | add a b ha hb => simp only [map_add, ha, hb]
  change f (g a) = _
  refine Submodule.iSup_induction (Module.End.eigenspace T)
    (motive := fun z => f (g z) = MonoidAlgebra.mapRingHom (Multiplicative J) σ.toRingHom (f z))
    (htop.symm ▸ (Submodule.mem_top : a ∈ (⊤ : Submodule K (K ⊗[k] A)))) ?_ ?_ ?_
  · intro μ a ha
    have h := Module.End.mem_eigenspace_iff.mp ha
    have hg : T (g a) = σ μ • g a := by
      rw [hT, h]
      exact (SemilinearAction.scalarExtension (K := K) A).map_smul σ μ a
    rw [hf _ _ hg, hf _ _ h, hε, hw, MonoidAlgebra.mapRingHom_single]
    rfl
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]

private theorem groupAlgebraBaseChange_one_tmul {M : Type u} [CommGroup M]
    (x : MonoidAlgebra k M) :
    CharacterDescent.groupAlgebraBaseChange k K M ((1 : K) ⊗ₜ[k] x) =
      MonoidAlgebra.map (algebraMap k K).toAddMonoidHom x := by
  change MonoidAlgebra.scalarTensorEquiv k K ((1 : K) ⊗ₜ[k] x) = _
  rw [MonoidAlgebra.scalarTensorEquiv_tmul, one_smul]
  rfl

variable [IsGalois k K]

set_option maxHeartbeats 700000 in
private theorem descend_weightHom (A : HopfAlgebraCategory k) {J : Type u} [AddCommGroup J]
    (S : Derivation k A A) (w : K →+ J)
    (hw : ∀ (σ : K ≃ₐ[k] K) (μ : K), w (σ μ) = w μ)
    (htop : (⨆ μ : K, Module.End.eigenspace (S.toLinearMap.baseChange K) μ) = ⊤)
    (f : (K ⊗[k] A) →ₐc[K] MonoidAlgebra K (Multiplicative J))
    (hf : ∀ (μ : K) (a : K ⊗[k] A), S.toLinearMap.baseChange K a = μ • a →
      f a = MonoidAlgebra.single (Multiplicative.ofAdd (w μ)) (counit (R := K) a)) :
    ∃ g : A →ₐc[k] MonoidAlgebra k (Multiplicative J), ∀ a,
      MonoidAlgebra.map (algebraMap k K).toAddMonoidHom (g a) = f ((1 : K) ⊗ₜ[k] a) := by
  let b := CharacterDescent.groupAlgebraBaseChange k K (Multiplicative J)
  have hex (a : A) : ∃ y, b ((1 : K) ⊗ₜ[k] y) = f ((1 : K) ⊗ₜ[k] a) := by
    have h : f ((1 : K) ⊗ₜ[k] a) ∈ Set.range
        (MonoidAlgebra.map (algebraMap k K).toAddMonoidHom :
          MonoidAlgebra k (Multiplicative J) → MonoidAlgebra K (Multiplicative J)) := by
      rw [MonoidAlgebra.range_map]
      intro m
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      have heq := weight_equivariant A S w hw htop f hf σ ((1 : K) ⊗ₜ[k] a)
      change f (σ 1 ⊗ₜ[k] a) = _ at heq
      rw [map_one] at heq
      change σ.toRingHom ((f ((1 : K) ⊗ₜ[k] a)).coeff m) = _
      simpa only [MonoidAlgebra.coeff_mapRingHom] using
        congrArg (fun z : MonoidAlgebra K (Multiplicative J) => z.coeff m) heq.symm
    obtain ⟨y, hy⟩ := h
    exact ⟨y, (groupAlgebraBaseChange_one_tmul y).trans hy⟩
  obtain ⟨g, hg⟩ := descend_bialgHom (b.symm.toBialgHom.comp f) (fun a => by
    obtain ⟨y, hy⟩ := hex a
    exact ⟨y, (b.toEquiv.eq_symm_apply).mpr hy⟩)
  refine ⟨g, fun a => ?_⟩
  rw [← groupAlgebraBaseChange_one_tmul]
  exact (b.toEquiv.eq_symm_apply).mp (hg a)

end GaloisDescent

section RationalWeight

open Specs.SemisimpleLieCentralizer (InvariantDerivation)
open scoped MonoidAlgebra

set_option maxHeartbeats 700000 in
private theorem exists_rational_weightHom {k : Type u} [Field k] [CharZero k]
    (A : HopfAlgebraCategory k) (D : InvariantDerivation A) (a : A)
    (ha : D.val a = (2 : k) • a) (hε : counit (R := k) a = 1) :
    ∃ (g : A →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} ℚ))),
      g a = MonoidAlgebra.single (Multiplicative.ofAdd (⟨2⟩ : ULift.{u} ℚ)) 1 := by
  let K := AlgebraicClosure k
  let : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  let i := Algebra.linearMap ℚ k
  obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (algebraMap ℚ k).injective)
  -- The normalized trace is Galois invariant and recovers scalars from the ground field.
  let trace := Algebra.normalizedTrace k K
  let w : K →+ ULift.{u} ℚ :=
    AddEquiv.ulift.symm.toAddMonoidHom.comp (p.toAddMonoidHom.comp trace.toAddMonoidHom)
  have hw (σ : K ≃ₐ[k] K) (μ : K) : w (σ μ) = w μ :=
    congrArg (fun x => (⟨p x⟩ : ULift.{u} ℚ)) (Algebra.normalizedTrace_map k K σ.toAlgHom μ)
  have hw2 : w (2 : K) = ⟨2⟩ := by
    change (⟨p (trace (2 : K))⟩ : ULift.{u} ℚ) = ⟨2⟩
    rw [← map_ofNat (algebraMap k K) 2, Algebra.normalizedTrace_algebraMap_apply_eq_self]
    apply ULift.ext
    have hp2 := LinearMap.congr_fun hp (2 : ℚ)
    change p (algebraMap ℚ k (2 : ℚ)) = (2 : ℚ) at hp2
    simpa only [map_ofNat] using hp2
  let S := semisimpleDerivation A D
  let T := extendDerivation (K := K) S.val
  have htop := semisimpleDerivation_span (K := K) A D
  have hT := extendDerivation_invariant (K := K) A S
  obtain ⟨f, hf⟩ := exists_weightBialgHom T hT htop w
  obtain ⟨g, hg⟩ := descend_weightHom A S.val w hw htop f hf
  refine ⟨g, ?_⟩
  have hsa := semisimpleDerivation_eigen A D a 2 ha
  have he : T ((1 : K) ⊗ₜ[k] a) = (2 : K) • ((1 : K) ⊗ₜ[k] a) := by
    change S.val.toLinearMap.baseChange K ((1 : K) ⊗ₜ[k] a) = _
    rw [LinearMap.baseChange_tmul, show S.val.toLinearMap a = (2 : k) • a from hsa,
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_ofNat,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hεK : counit (R := K) ((1 : K) ⊗ₜ[k] a) = 1 := by
    simp [TensorProduct.counit_tmul, hε]
  apply MonoidAlgebra.map_injective (algebraMap k K).toAddMonoidHom (algebraMap k K).injective
  rw [hg, hf _ _ he, hεK, hw2, MonoidAlgebra.map_single]
  simp

end RationalWeight

section SplitTorus

open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra)
open CategoryTheory.CartesianMonoidalCategory
open scoped MonoidAlgebra

open private hopfImageIdeal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private liftHopfQuotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem splitTorus_of_rational_weightHom {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (A : HopfAlgebraCategory k) [Algebra.FiniteType k A]
    (i : specGroup A ≅ G.val)
    (f : A →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} ℚ))) (a : A)
    (m : Multiplicative (ULift.{u} ℚ)) (hm : m ≠ 1)
    (hf : f a = MonoidAlgebra.single m 1) :
    ∃ T : ClosedSubgroup G.val, GeometricRadicals.IsSplitTorus T.group ∧
      ¬ GeometricRadicals.IsTrivialSubgroup T := by
  classical
  let M := Multiplicative (ULift.{u} ℚ)
  let B := groupAlgebra k M
  let F : A ⟶ B := CommHopfAlgCat.ofHom f
  -- The image on coordinate algebras represents a closed subgroup of the given group.
  let I := RingHom.ker F.hom.toAlgHom
  let : I.IsHopfIdeal k := hopfImageIdeal F
  let Q := hopfQuotient A I
  let q := hopfQuotientMap A I
  let b := liftHopfQuotient I F (fun _ hx => hx)
  have hb : Function.Injective b.hom := RingHom.kerLift_injective F.hom.toAlgHom.toRingHom
  obtain ⟨N, ⟨d, _⟩, _⟩ := (DiagonalizableGroups.hopfSubalgebraClassification k M b).mp hb
  have hQ : Algebra.FiniteType k Q := inferInstanceAs (Algebra.FiniteType k (A ⧸ I))
  let : Group.FG N := MonoidAlgebra.finiteType_iff_group_fg.mp (hQ.equiv d.toAlgEquiv.symm)
  let : Module.Finite ℤ (Additive N) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let : Module.IsTorsionFree ℤ (Additive N) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r n hn
    have hn' : r • (n.toMul.val.toAdd.down : ℚ) = 0 :=
      congrArg (fun z : Additive N => z.toMul.val.toAdd.down) hn
    rcases smul_eq_zero.mp hn' with h | h
    · exact Or.inl h
    · exact Or.inr (Subtype.ext (ULift.ext h))
  obtain ⟨r, v⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive N)
  let L : N ≃* StandardLattice.{u} r :=
    { toFun := fun x j => ⟨Multiplicative.ofAdd (v.equivFun (Additive.ofMul x) j)⟩
      invFun := fun y => (v.equivFun.symm fun j => (y j).down.toAdd).toMul
      left_inv := fun x => v.equivFun.symm_apply_apply (Additive.ofMul x)
      right_inv := fun y => funext fun j =>
        ULift.ext (congrArg Multiplicative.ofAdd (congrFun (v.equivFun.apply_symm_apply _) j))
      map_mul' := fun x y => funext fun j =>
        ULift.ext (congrArg Multiplicative.ofAdd (congrFun (map_add v.equivFun
          (Additive.ofMul x) (Additive.ofMul y)) j)) }
  let aIso : groupAlgebra k (StandardLattice.{u} r) ≅ Q :=
    CommHopfAlgCat.isoMk ((MonoidAlgebra.domCongrBialgEquiv k k L.symm).trans d)
  obtain ⟨std⟩ := CharacterDescent.standardSplitTorus (k := k) r
  have hclosed : IsClosedImmersion (specGroupMap q).hom.hom.left :=
    (LinearAlgebraicGroups.hopfMapClosedImmersion k q).mpr
      Ideal.Quotient.mk_surjective
  let := hclosed
  let : IsIso i.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso i.hom
  let T : ClosedSubgroup G.val := ⟨specGroup Q, specGroupMap q ≫ i.hom, by
    change IsClosedImmersion ((specGroupMap q).hom.hom.left ≫ i.hom.hom.hom.left)
    infer_instance⟩
  refine ⟨T, ⟨r, ⟨(hopfSpec (CommRingCat.of k)).mapIso aIso.op ≪≫ std⟩⟩, ?_⟩
  rintro ⟨triv⟩
  let R := CommAlgCat.of k B
  let E := (LinearAlgebraicGroups.hopfSpecPointIso Q ≪≫ (groupPointsFunctor k).mapIso triv).app R
  have hs : (toConv b.hom.toAlgHom : (convolutionPoints Q).obj R) = 1 := by
    apply E.groupIsoToMulEquiv.injective
    exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  have heval := congrArg (fun p : (convolutionPoints Q).obj R => p.ofConv (q.hom a)) hs
  change f a = algebraMap k B (counit (R := k) (q.hom a)) at heval
  have hε : counit (R := k) (q.hom a) = 1 := by
    rw [CoalgHomClass.counit_comp_apply, ← CoalgHomClass.counit_comp_apply f a,
      hf, MonoidAlgebra.counit_single, Bialgebra.counit_one]
  rw [hf, hε, map_one, MonoidAlgebra.one_def] at heval
  exact hm (MonoidAlgebra.of_injective (R := k) heval)

end SplitTorus

/-- A nonzero adjoint-nilpotent element would yield a nontrivial split torus
by weighting the coordinate ring with the semisimple part of an invariant
derivation. -/
theorem adNilpotentEqZero_conditional
    (lieSemisimple : Specs.SemisimplyDifferentiated.LieSemisimple.{u})
    (_adjointCocharacterLift : Specs.AdjointCocharacters.AdjointCocharacterLift.{u})
    (_adjointQuotientExists : Specs.AdjointCocharacters.AdjointQuotientExists.{u})
    (_maximalTorusPreimage : Specs.AdjointCocharacters.MaximalTorusPreimage.{u})
    (_rationalCocharacterSurjectivity : Specs.AdjointCocharacters.RationalCocharacterSurjectivity.{u})
    (_semisimpleRationalCocharacterIso : Specs.AdjointCocharacters.SemisimpleRationalCocharacterIso.{u}) :
    Specs.AnisotropicAdNilpotents.AdNilpotentEqZero.{u} := by
  intro k _ _ G hG hanis s
  let := s.lieRing
  let := s.lieAlgebra
  intro e he
  by_contra hne
  obtain ⟨hfinite, hradical⟩ := lieSemisimple G hG s
  let : FiniteDimensional k (Lie k G.val) := hfinite
  let : LieAlgebra.HasTrivialRadical k (Lie k G.val) := ⟨hradical⟩
  obtain ⟨h, hh⟩ := exists_bracket_eq_two_smul e he
  obtain ⟨A, hA, ⟨i⟩⟩ := groupPresentation G
  let : Algebra.FiniteType k A := hA
  have hne' : e ≠ @Zero.zero (Lie k G.val) s.lieRing.toAddCommGroup.toZero := by
    intro hz
    exact hne (hz.trans (congrArg (fun g : AddGroup (PointKernel G.val) =>
      @Zero.zero _ g.toZero) s.group_law))
  obtain ⟨D, a, ha, hε⟩ := adjoint_eigenfunction G s A i h e 2 hh hne'
  obtain ⟨g, hg⟩ := exists_rational_weightHom A D a ha hε
  have hm : (Multiplicative.ofAdd (⟨2⟩ : ULift.{u} ℚ)) ≠ 1 := by
    intro h
    have H := congrArg (fun x : Multiplicative (ULift.{u} ℚ) => x.toAdd.down) h
    exact (by decide : (2 : ℚ) ≠ 0) H
  obtain ⟨T, hT, hnt⟩ := splitTorus_of_rational_weightHom G A i g a _ hm hg
  exact hnt (hanis T hT)

end

end LinearAlgebraicGroups.Arithmetic.AnisotropicAdNilpotents

universe v8_closure_4db075d1542b4581_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicAdNilpotents».«adNilpotentEqZero» : _root_.«LinearAlgebraicGroups».«Specs».«AnisotropicAdNilpotents».«AdNilpotentEqZero».{v8_closure_4db075d1542b4581_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicAdNilpotents».«adNilpotentEqZero_conditional».{v8_closure_4db075d1542b4581_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«SemisimplyDifferentiated».«lieSemisimple».{v8_closure_4db075d1542b4581_u0}) (@_root_.«LinearAlgebraicGroups».«Descent».«AdjointCocharacters».«adjointCocharacterLift».{v8_closure_4db075d1542b4581_u0}) (@_root_.«LinearAlgebraicGroups».«Descent».«AdjointCocharacters».«adjointQuotientExists».{v8_closure_4db075d1542b4581_u0}) (@_root_.«LinearAlgebraicGroups».«Descent».«AdjointCocharacters».«maximalTorusPreimage».{v8_closure_4db075d1542b4581_u0}) (@_root_.«LinearAlgebraicGroups».«Descent».«AdjointCocharacters».«rationalCocharacterSurjectivity».{v8_closure_4db075d1542b4581_u0}) (@_root_.«LinearAlgebraicGroups».«Descent».«AdjointCocharacters».«semisimpleRationalCocharacterIso».{v8_closure_4db075d1542b4581_u0})
