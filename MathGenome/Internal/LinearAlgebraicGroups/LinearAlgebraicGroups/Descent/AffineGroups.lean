import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.RingTheory.Etale.Descent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open Coalgebra HopfAlgebra
open scoped TensorProduct

namespace LinearAlgebraicGroups.Descent

universe u
noncomputable section

set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

section Tensor

variable {R S X Y : Type u}
  [CommRing R] [CommRing S] [CommRing X] [CommRing Y]
  [Algebra k R] [Algebra k S] [Algebra k X] [Algebra k Y]
  [Algebra K X] [Algebra K Y] [IsScalarTower k K X] [IsScalarTower k K Y]

private theorem scalarCompat (f : R →ₐ[k] X) :
    f.toRingHom.comp (algebraMap k R) = (algebraMap K X).comp (algebraMap k K) :=
  RingHom.ext fun a => (f.commutes a).trans (IsScalarTower.algebraMap_apply k K X a)

private def tensorAlong (f : R →ₐ[k] X) (g : S →ₐ[k] Y) :
    R ⊗[k] S →ₐ[k] X ⊗[K] Y where
  __ := Algebra.TensorProduct.mapRingHom (algebraMap k K) f.toRingHom g.toRingHom
    (scalarCompat f) (scalarCompat g)
  commutes' a := by
    change Algebra.TensorProduct.mapRingHom (algebraMap k K) f.toRingHom g.toRingHom
      (scalarCompat f) (scalarCompat g) _ = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.mapRingHom_tmul]
    change f (algebraMap k R a) ⊗ₜ[K] g 1 = _
    rw [f.commutes, map_one, IsScalarTower.algebraMap_apply k K X,
      IsScalarTower.algebraMap_apply k K (X ⊗[K] Y), Algebra.TensorProduct.algebraMap_apply]

@[simp] private theorem tensorAlong_tmul (f : R →ₐ[k] X) (g : S →ₐ[k] Y) (x : R) (y : S) :
    tensorAlong (K := K) f g (x ⊗ₜ[k] y) = f x ⊗ₜ[K] g y :=
  Algebra.TensorProduct.mapRingHom_tmul _ _ _ (scalarCompat f) (scalarCompat g) _ _

private theorem tensorAlong_lift (f : R →ₐ[k] X) (g : S →ₐ[k] Y) :
    (tensorAlong (K := K) f g).toLinearMap.liftBaseChange K =
      (TensorProduct.map (f.toLinearMap.liftBaseChange K) (g.toLinearMap.liftBaseChange K)).comp
        (TensorProduct.AlgebraTensorModule.distribBaseChange k K R S).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

private theorem tensorAlong_injective (f : R →ₐ[k] X) (g : S →ₐ[k] Y)
    (hf : Function.Injective (f.toLinearMap.liftBaseChange K))
    (hg : Function.Injective (g.toLinearMap.liftBaseChange K)) :
    Function.Injective (tensorAlong (K := K) f g) := by
  have h := TensorProduct.map_injective_of_flat_flat _ _ hf hg
  have lift_inj : Function.Injective ((tensorAlong (K := K) f g).toLinearMap.liftBaseChange K) := by
    rw [tensorAlong_lift]
    exact h.comp (TensorProduct.AlgebraTensorModule.distribBaseChange k K R S).injective
  exact fun x y e =>
    Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective
      (lift_inj (by
        simp only [Algebra.TensorProduct.includeRight_apply, LinearMap.liftBaseChange_tmul,
          AlgHom.toLinearMap_apply, one_smul, e]))

end Tensor

variable {A B : HopfAlgebraCategory K} (D : HopfDescentDatum k A)
variable [FiniteDimensional k K] [IsGalois k K]

private theorem fixed_lift_bijective :
    Function.Bijective (D.fixed.val.toLinearMap.liftBaseChange K) :=
  D.action.descent_bijective

private abbrev fixedTensor : D.fixed ⊗[k] D.fixed →ₐ[k] A ⊗[K] A :=
  tensorAlong (K := K) D.fixed.val D.fixed.val

private theorem fixedTensor_injective : Function.Injective (fixedTensor D) :=
  tensorAlong_injective _ _ (fixed_lift_bijective D).injective (fixed_lift_bijective D).injective

private theorem fixedTriple_injective :
    Function.Injective (tensorAlong (K := K) D.fixed.val (fixedTensor D)) := by
  apply tensorAlong_injective _ _ (fixed_lift_bijective D).injective
  rw [tensorAlong_lift]
  exact (TensorProduct.map_injective_of_flat_flat _ _ (fixed_lift_bijective D).injective
    (fixed_lift_bijective D).injective).comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange k K _ _).injective

private def fixedComul : D.fixed →ₗ[k] D.fixed ⊗[k] D.fixed :=
  (D.action.tensorEquiv D.action).symm.toLinearMap.comp
    (D.action.restrict (D.action.tensor D.action) (comul (R := K)) D.comul_equivariant)

private def fixedCounit : D.fixed →ₗ[k] k :=
  (SemilinearAction.unitEquiv (K := K)).symm.toLinearMap.comp
    (D.action.restrict SemilinearAction.unit (counit (R := K)) D.counit_equivariant)

private def fixedAntipode : D.fixed →ₗ[k] D.fixed :=
  D.action.restrict D.action (antipode K) D.antipode_equivariant

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem fixedTensor_toLinearMap :
    (fixedTensor D).toLinearMap =
      (D.action.tensor D.action).fixed.subtype.comp (D.action.tensorComparison D.action) := by
  apply TensorProduct.ext'
  intro x y
  change fixedTensor D (x ⊗ₜ[k] y) = _
  rw [tensorAlong_tmul]
  rfl

@[simp] private theorem fixedComul_apply (x : D.fixed) :
    fixedTensor D (fixedComul D x) = comul (R := K) (x : A) := by
  change (fixedTensor D).toLinearMap _ = _
  rw [fixedTensor_toLinearMap D]
  exact congrArg Subtype.val ((D.action.tensorEquiv D.action).apply_symm_apply _)

@[simp] private theorem fixedCounit_apply (x : D.fixed) :
    algebraMap k K (fixedCounit D x) = counit (R := K) (x : A) :=
  congrArg Subtype.val ((SemilinearAction.unitEquiv (k := k) (K := K)).apply_symm_apply _)

omit [FiniteDimensional k K] [IsGalois k K] in
@[simp] private theorem fixedAntipode_apply (x : D.fixed) :
    (fixedAntipode D x : A) = antipode K (x : A) := rfl


private theorem fixed_coassoc (x : D.fixed) :
    TensorProduct.assoc k D.fixed D.fixed D.fixed
      ((fixedComul D).rTensor D.fixed (fixedComul D x)) =
      (fixedComul D).lTensor D.fixed (fixedComul D x) := by
  apply fixedTriple_injective D
  have hleft (t : D.fixed ⊗[k] D.fixed) :
      tensorAlong (K := K) D.fixed.val (fixedTensor D)
        (TensorProduct.assoc k D.fixed D.fixed D.fixed ((fixedComul D).rTensor D.fixed t)) =
      TensorProduct.assoc K A A A ((comul (R := K)).rTensor A (fixedTensor D t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul y z =>
      have hassoc (s : D.fixed ⊗[k] D.fixed) :
          tensorAlong (K := K) D.fixed.val (fixedTensor D)
            (TensorProduct.assoc k D.fixed D.fixed D.fixed (s ⊗ₜ[k] z)) =
          TensorProduct.assoc K A A A (fixedTensor D s ⊗ₜ[K] (z : A)) := by
        induction s using TensorProduct.inductionOn with
        | tmul a b => simp
        | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
      rw [LinearMap.rTensor_tmul, tensorAlong_tmul]
      exact (hassoc (fixedComul D y)).trans (by rw [fixedComul_apply, LinearMap.rTensor_tmul]; rfl)
    | add a b ha hb => simp only [map_add, ha, hb]
  have hright (t : D.fixed ⊗[k] D.fixed) :
      tensorAlong (K := K) D.fixed.val (fixedTensor D) ((fixedComul D).lTensor D.fixed t) =
        (comul (R := K)).lTensor A (fixedTensor D t) := by
    induction t using TensorProduct.inductionOn with
    | tmul y z => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [hleft, hright, fixedComul_apply, coassoc_apply]

private theorem fixed_right_counit (x : D.fixed) :
    (fixedCounit D).rTensor D.fixed (fixedComul D x) = 1 ⊗ₜ[k] x := by
  apply (TensorProduct.lid k D.fixed).injective
  apply (Subtype.val_injective : Function.Injective (D.fixed.val : D.fixed →ₐ[k] A))
  have h (t : D.fixed ⊗[k] D.fixed) :
      (TensorProduct.lid k D.fixed ((fixedCounit D).rTensor D.fixed t) : A) =
      TensorProduct.lid K A ((counit (R := K)).rTensor A (fixedTensor D t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul y z =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, tensorAlong_tmul]
      change ((fixedCounit D y • z : D.fixed) : A) = counit (R := K) (y : A) • (z : A)
      rw [← fixedCounit_apply D y, IsScalarTower.algebraMap_smul]
      rfl
    | add a b ha hb =>
      change D.fixed.val (TensorProduct.lid k D.fixed ((fixedCounit D).rTensor D.fixed (a + b))) = _
      simp only [map_add, ha, hb, Subalgebra.val_apply]
  rw [h, fixedComul_apply, rTensor_counit_comul]
  simp

private theorem fixed_left_counit (x : D.fixed) :
    (fixedCounit D).lTensor D.fixed (fixedComul D x) = x ⊗ₜ[k] 1 := by
  apply (TensorProduct.rid k D.fixed).injective
  apply (Subtype.val_injective : Function.Injective (D.fixed.val : D.fixed →ₐ[k] A))
  have h (t : D.fixed ⊗[k] D.fixed) :
      (TensorProduct.rid k D.fixed ((fixedCounit D).lTensor D.fixed t) : A) =
      TensorProduct.rid K A ((counit (R := K)).lTensor A (fixedTensor D t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul y z =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, tensorAlong_tmul]
      change ((fixedCounit D z • y : D.fixed) : A) = counit (R := K) (z : A) • (y : A)
      rw [← fixedCounit_apply D z, IsScalarTower.algebraMap_smul]
      rfl
    | add a b ha hb =>
      change D.fixed.val (TensorProduct.rid k D.fixed ((fixedCounit D).lTensor D.fixed (a + b))) = _
      simp only [map_add, ha, hb, Subalgebra.val_apply]
  rw [h, fixedComul_apply, lTensor_counit_comul]
  simp

private theorem fixed_antipode_right (x : D.fixed) :
    LinearMap.mul' k D.fixed ((fixedAntipode D).rTensor D.fixed (fixedComul D x)) =
      algebraMap k D.fixed (fixedCounit D x) := by
  apply (Subtype.val_injective : Function.Injective (D.fixed.val : D.fixed →ₐ[k] A))
  have h (t : D.fixed ⊗[k] D.fixed) :
      (LinearMap.mul' k D.fixed ((fixedAntipode D).rTensor D.fixed t) : A) =
      LinearMap.mul' K A ((antipode K).rTensor A (fixedTensor D t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul y z => simp
    | add a b ha hb =>
      change D.fixed.val (LinearMap.mul' k D.fixed ((fixedAntipode D).rTensor D.fixed (a + b))) = _
      simp only [map_add, ha, hb, Subalgebra.val_apply]
  rw [h, fixedComul_apply, mul_antipode_rTensor_comul_apply]
  rw [← fixedCounit_apply D x, ← IsScalarTower.algebraMap_apply]
  rfl

private theorem fixed_antipode_left (x : D.fixed) :
    LinearMap.mul' k D.fixed ((fixedAntipode D).lTensor D.fixed (fixedComul D x)) =
      algebraMap k D.fixed (fixedCounit D x) := by
  apply (Subtype.val_injective : Function.Injective (D.fixed.val : D.fixed →ₐ[k] A))
  have h (t : D.fixed ⊗[k] D.fixed) :
      (LinearMap.mul' k D.fixed ((fixedAntipode D).lTensor D.fixed t) : A) =
      LinearMap.mul' K A ((antipode K).lTensor A (fixedTensor D t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul y z => simp
    | add a b ha hb =>
      change D.fixed.val (LinearMap.mul' k D.fixed ((fixedAntipode D).lTensor D.fixed (a + b))) = _
      simp only [map_add, ha, hb, Subalgebra.val_apply]
  rw [h, fixedComul_apply, mul_antipode_lTensor_comul_apply]
  rw [← fixedCounit_apply D x, ← IsScalarTower.algebraMap_apply]
  rfl

private def fixedOperations : HopfOperations k D.fixed where
  coalgebra :=
    { comul := fixedComul D
      counit := fixedCounit D
      coassoc := LinearMap.ext (fixed_coassoc D)
      rTensor_counit_comp_comul := LinearMap.ext (fixed_right_counit D)
      lTensor_counit_comp_comul := LinearMap.ext (fixed_left_counit D) }
  counit_one := by
    apply (algebraMap k K).injective
    change algebraMap k K (fixedCounit D 1) = _
    rw [fixedCounit_apply, Subalgebra.coe_one, Bialgebra.counit_one, map_one]
  counit_mul x y := by
    apply (algebraMap k K).injective
    change algebraMap k K (fixedCounit D (x * y)) =
      algebraMap k K (fixedCounit D x * fixedCounit D y)
    rw [map_mul (algebraMap k K), fixedCounit_apply, fixedCounit_apply, fixedCounit_apply,
      Subalgebra.coe_mul, Bialgebra.counit_mul]
  comul_one := by
    apply fixedTensor_injective D
    change fixedTensor D (fixedComul D 1) = _
    rw [fixedComul_apply, Subalgebra.coe_one, Bialgebra.comul_one, map_one]
  comul_mul x y := by
    apply fixedTensor_injective D
    change fixedTensor D (fixedComul D (x * y)) =
      fixedTensor D (fixedComul D x * fixedComul D y)
    rw [map_mul (fixedTensor D), fixedComul_apply, fixedComul_apply, fixedComul_apply,
      Subalgebra.coe_mul, Bialgebra.comul_mul]
  antipode := fixedAntipode D
  right_inverse := fixed_antipode_right D
  left_inverse := fixed_antipode_left D

section Comparison

variable {R : Type u} [CommRing R] [HopfAlgebra k R]

omit [FiniteDimensional k K] [IsGalois k K] in
omit [FiniteDimensional k K] [IsGalois k K] in
private theorem comparison_counit_base (x : R) :
    counit (R := K) (1 ⊗ₜ[k] x : K ⊗[k] R) =
      algebraMap k K (counit (R := k) x) := by
  rw [TensorProduct.counit_tmul, Bialgebra.counit_one]
  simp [Algebra.smul_def]

omit [FiniteDimensional k K] [IsGalois k K] in
omit [FiniteDimensional k K] [IsGalois k K] in
private theorem comparison_comul_base (f : K ⊗[k] R →ₐ[K] A)
    (j : R →ₐ[k] A) (hf : ∀ x, f (1 ⊗ₜ[k] x) = j x) (x : R) :
    Algebra.TensorProduct.map f f (comul (R := K) (1 ⊗ₜ[k] x)) =
      tensorAlong (K := K) j j (comul (R := k) x) := by
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  generalize comul (R := k) x = t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.map_tmul, hf, tensorAlong_tmul]
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]

end Comparison

private def fixedComparisonAlg : K ⊗[k] D.fixed →ₐ[K] A :=
  (AlgHom.liftEquiv k K D.fixed A) D.fixed.val

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem fixedComparisonAlg_tmul (r : K) (x : D.fixed) :
    fixedComparisonAlg D (r ⊗ₜ[k] x) = r • (x : A) := rfl

private def fixedComparison :
    letI := (fixedOperations D).toHopfAlgebra
    (K ⊗[k] D.fixed) ≃ₐc[K] A := by
  letI := (fixedOperations D).toHopfAlgebra
  let f := fixedComparisonAlg D
  have h : Function.Bijective f := fixed_lift_bijective D
  let b := AlgEquiv.ofBijective f h
  apply BialgEquiv.ofAlgEquiv b
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change counit (R := K) (f (1 ⊗ₜ[k] x)) = counit (R := K) (1 ⊗ₜ[k] x : K ⊗[k] D.fixed)
    rw [fixedComparisonAlg_tmul, one_smul, comparison_counit_base (K := K)]
    exact (fixedCounit_apply D x).symm
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change Algebra.TensorProduct.map f f (comul (R := K) (1 ⊗ₜ[k] x)) =
      comul (R := K) (f (1 ⊗ₜ[k] x))
    rw [comparison_comul_base f D.fixed.val (fun y => by rw [fixedComparisonAlg_tmul, one_smul]; rfl),
      fixedComparisonAlg_tmul, one_smul]
    exact fixedComul_apply D x

/-- The fixed algebra endowed with the descended Hopf operations. -/
def descendHopf : HopfDescent D where
  operations := fixedOperations D
  comparison := fixedComparison D
  comparison_tmul := fixedComparisonAlg_tmul D

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem comparison_tmul {D : HopfDescentDatum k A} (H : HopfDescent D)
    (r : K) (x : D.fixed) : H.iso.hom.hom (r ⊗ₜ[k] x) = r • (x : A) :=
  H.comparison_tmul r x

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem comparison_equivariant {D : HopfDescentDatum k A} (H : HopfDescent D) :
    (SemilinearAction.scalarExtension (K := K) D.fixed).Equivariant D.action
      H.iso.hom.hom.toLinearMap := by
  have eq : H.iso.hom.hom.toLinearMap = D.action.descentMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    exact H.comparison_tmul r x
  rw [eq]
  exact D.action.descent_equivariant

theorem affineHopfDescent : AffineGroupSpecs.Effective.{u} := by
  intro k K _ _ _ _ _ A D
  exact ⟨descendHopf D, comparison_equivariant (descendHopf D)⟩

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem comparison_comul {D : HopfDescentDatum k A} (H : HopfDescent D)
    (x : H.algebra) :
    fixedTensor D (H.operations.coalgebra.comul x) = comul (R := K) (x : A) := by
  letI := H.operations.toHopfAlgebra
  let f := H.iso.hom.hom
  have hx : ∀ y : D.fixed, f (1 ⊗ₜ[k] y) = D.fixed.val y := fun y =>
    (comparison_tmul H 1 y).trans (one_smul K _)
  have h := CoalgHomClass.map_comp_comul_apply f (1 ⊗ₜ[k] x)
  change Algebra.TensorProduct.map f.toAlgHom f.toAlgHom
    (comul (R := K) (1 ⊗ₜ[k] x)) = comul (R := K) (f (1 ⊗ₜ[k] x)) at h
  rw [comparison_comul_base f.toAlgHom D.fixed.val hx, hx] at h
  exact h

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem comparison_counit {D : HopfDescentDatum k A} (H : HopfDescent D)
    (x : H.algebra) :
    algebraMap k K (H.operations.coalgebra.counit x) = counit (R := K) (x : A) := by
  letI := H.operations.toHopfAlgebra
  have h := CoalgHomClass.counit_comp_apply H.iso.hom.hom (1 ⊗ₜ[k] x)
  change counit (R := K) (H.iso.hom.hom (1 ⊗ₜ[k] x)) =
    counit (R := K) (1 ⊗ₜ[k] (x : D.fixed) : K ⊗[k] D.fixed) at h
  rw [comparison_tmul H, one_smul, comparison_counit_base] at h
  exact h.symm

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem comparison_antipode {D : HopfDescentDatum k A} (H : HopfDescent D)
    (x : H.algebra) : (H.operations.antipode x : A) = antipode K (x : A) := by
  letI := H.operations.toHopfAlgebra
  have h := DFunLike.congr_fun (hopfSpecMorphism K H.iso.hom).2 (1 ⊗ₜ[k] x)
  change H.iso.hom.hom (antipode K (1 ⊗ₜ[k] x)) =
    antipode K (H.iso.hom.hom (1 ⊗ₜ[k] x)) at h
  have ht : antipode K (1 ⊗ₜ[k] x : K ⊗[k] D.fixed) = 1 ⊗ₜ[k] antipode k (x : D.fixed) := by
    rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul, antipode_one]
  rw [ht, comparison_tmul H, comparison_tmul H, one_smul, one_smul] at h
  exact h

theorem affineDescentStructureMaps : AffineGroupSpecs.StructureMaps.{u} := by
  intro k K _ _ _ A D H x
  refine ⟨?_, comparison_counit H x, comparison_antipode H x⟩
  have h := comparison_comul H x
  change (fixedTensor D).toLinearMap (H.operations.coalgebra.comul x) = _ at h
  rw [fixedTensor_toLinearMap] at h
  exact h

section Morphisms

variable {D : HopfDescentDatum k A} {E : HopfDescentDatum k B}
  (H : HopfDescent D) (L : HopfDescent E)

private def restrictAlgHom (f : A ⟶ B) (hf : D.Equivariant E f) :
    H.algebra →ₐ[k] L.algebra :=
  ((f.hom.toAlgHom.restrictScalars k).comp D.fixed.val).codRestrict E.fixed fun x g =>
    (hf g (x : A)).symm.trans (congrArg f.hom (x.property g))

private def restrictHopfHom (f : A ⟶ B) (hf : D.Equivariant E f) :
    H.algebra ⟶ L.algebra := by
  letI := H.operations.toHopfAlgebra
  letI := L.operations.toHopfAlgebra
  let g := restrictAlgHom H L f hf
  refine CommHopfAlgCat.ofHom (BialgHom.ofAlgHom g ?_ ?_)
  · apply AlgHom.ext
    intro x
    apply (algebraMap k K).injective
    change algebraMap k K (counit (R := k) (g x)) = algebraMap k K (counit (R := k) x)
    rw [comparison_counit L, comparison_counit H]
    exact CoalgHomClass.counit_comp_apply f.hom (x : A)
  · apply AlgHom.ext
    intro x
    apply fixedTensor_injective E
    have ht (t : H.algebra ⊗[k] H.algebra) :
        fixedTensor E (Algebra.TensorProduct.map g g t) =
          Algebra.TensorProduct.map f.hom.toAlgHom f.hom.toAlgHom (fixedTensor D t) := by
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, tensorAlong_tmul]
        rfl
      | add a b ha hb => simp only [map_add, ha, hb]
    change fixedTensor E (Algebra.TensorProduct.map g g (comul (R := k) x)) =
      fixedTensor E (comul (R := k) (g x))
    rw [ht, comparison_comul H, comparison_comul L]
    exact CoalgHomClass.map_comp_comul_apply f.hom (x : A)

private theorem restrictHopfHom_base (f : A ⟶ B) (hf : D.Equivariant E f) :
    H.iso.hom ≫ f = extendedHopfMap K (restrictHopfHom H L f hf) ≫ L.iso.hom := by
  let g := restrictHopfHom H L f hf
  apply CommHopfAlgCat.hom_ext
  have h : (H.iso.hom ≫ f).hom.toAlgHom =
      (extendedHopfMap K g ≫ L.iso.hom).hom.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change f.hom (H.iso.hom.hom (1 ⊗ₜ[k] x)) =
      L.iso.hom.hom (1 ⊗ₜ[k] g.hom x)
    rw [comparison_tmul H, comparison_tmul L, one_smul, one_smul]
    rfl
  exact BialgHom.ext fun x => DFunLike.congr_fun h x

theorem affineDescentMorphisms : AffineGroupSpecs.Morphisms.{u} := by
  intro k K _ _ _ _ _ A B D E H L
  constructor
  · intro f hf
    let g := restrictHopfHom H L f hf
    refine ⟨g, restrictHopfHom_base H L f hf, ?_⟩
    intro g' hg'
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro x
    apply (Subtype.val_injective : Function.Injective (E.fixed.val : E.fixed →ₐ[k] B))
    have h := ConcreteCategory.congr_hom hg' (1 ⊗ₜ[k] x : K ⊗[k] D.fixed)
    change f.hom (H.iso.hom.hom (1 ⊗ₜ[k] x)) =
      L.iso.hom.hom (1 ⊗ₜ[k] g'.hom x) at h
    rw [comparison_tmul H, comparison_tmul L, one_smul, one_smul] at h
    exact h.symm
  · intro g
    letI := H.operations.toHopfAlgebra
    letI := L.operations.toHopfAlgebra
    have hg := SemilinearAction.scalarExtension_equivariant (K := K) g.hom.toLinearMap
    have hH := comparison_equivariant H
    have hL := comparison_equivariant L
    intro s x
    obtain ⟨y, rfl⟩ := H.comparison.surjective x
    have hy : H.iso.inv.hom (H.comparison y) = y := H.comparison.symm_apply_apply y
    have hs : H.iso.inv.hom (D.action.act s (H.comparison y)) =
        (SemilinearAction.scalarExtension D.fixed).act s y := by
      have h := hH s y
      change H.comparison ((SemilinearAction.scalarExtension D.fixed).act s y) =
        D.action.act s (H.comparison y) at h
      rw [← h]
      exact H.comparison.symm_apply_apply _
    change L.iso.hom.hom ((extendedHopfMap K g).hom (H.iso.inv.hom
      (D.action.act s (H.comparison y)))) = E.action.act s
        (L.iso.hom.hom ((extendedHopfMap K g).hom (H.iso.inv.hom (H.comparison y))))
    rw [hs, hy]
    exact (congrArg L.iso.hom.hom (hg s y)).trans (hL s _)

end Morphisms

theorem affineDescentProperties : AffineGroupSpecs.Properties.{u} := by
  intro k K _ _ _ A D H
  letI := H.operations.toHopfAlgebra
  constructor
  · intro h
    haveI : Algebra.FiniteType K (K ⊗[k] D.fixed) :=
      Algebra.FiniteType.of_surjective H.comparison.toAlgEquiv.symm.toAlgHom
        H.comparison.toAlgEquiv.symm.surjective
    exact Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat K
  · intro h
    haveI : Algebra.Smooth K (K ⊗[k] D.fixed) :=
      Algebra.Smooth.of_equiv H.comparison.toAlgEquiv.symm
    exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K

private theorem specGroup_smooth_iff (A : HopfAlgebraCategory k) :
    AlgebraicGeometry.Smooth (specGroup A).X.hom ↔ Algebra.Smooth k A := by
  change AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
  exact RingHom.smooth_algebraMap

theorem affineGroupDescentProperties : AffineGroupSpecs.GroupProperties.{u} := by
  intro k K _ _ _ A D H
  constructor
  · intro h
    refine ⟨(hopfSpec_locallyOfFiniteType_iff k H.algebra).mpr
      ((affineDescentProperties H).1 ((hopfSpec_locallyOfFiniteType_iff K A).mp h)), ?_⟩
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k H.algebra)))
    infer_instance
  · intro h
    exact (specGroup_smooth_iff H.algebra).mpr
      ((affineDescentProperties H).2 ((specGroup_smooth_iff A).mp h))

open private LinearAlgebraicGroups.extendedGroupIso LinearAlgebraicGroups.extendedSpecIso_natural
  LinearAlgebraicGroups.specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

/-- The descended affine group identifies with the original one after base change. -/
def groupDescentComparison {D : HopfDescentDatum k A} (H : HopfDescent D) :
    specGroup A ≅ (groupBaseChange k K).obj (specGroup H.algebra) :=
  (hopfSpec (CommRingCat.of K)).mapIso H.iso.op ≪≫
    LinearAlgebraicGroups.extendedGroupIso K H.algebra

theorem affineGroupDescent : AffineGroupSpecs.Groups.{u} := by
  intro k K _ _ _
  refine ⟨fun H => groupDescentComparison H, ?_⟩
  intro A B D E H L f g h
  have h' : specGroupMap f ≫ specGroupMap H.iso.hom =
      specGroupMap L.iso.hom ≫ specGroupMap (extendedHopfMap K g) := by
    rw [← LinearAlgebraicGroups.specGroupMap_comp, ← LinearAlgebraicGroups.specGroupMap_comp, h]
  have hn : specGroupMap (extendedHopfMap K g) ≫
        (LinearAlgebraicGroups.extendedGroupIso K H.algebra).hom =
      (LinearAlgebraicGroups.extendedGroupIso K L.algebra).hom ≫
        (groupBaseChange k K).map (specGroupMap g) := by
    apply Grp.hom_ext
    exact LinearAlgebraicGroups.extendedSpecIso_natural K g
  change specGroupMap f ≫ specGroupMap H.iso.hom ≫ _ =
    (specGroupMap L.iso.hom ≫ _) ≫ _
  rw [← Category.assoc, h', Category.assoc, hn, ← Category.assoc]

section Ideals

variable {D : HopfDescentDatum k A} (H : HopfDescent D)

/-- Each action operator is a ring endomorphism with its prescribed semilinearity. -/
private def actionRingHom (D : HopfDescentDatum k A) (s : Gal(K/k)) : A →+* A :=
  { (D.action.act s).toAddMonoidHom with
    map_one' := D.map_one s
    map_mul' := D.map_mul s }

variable (J : Ideal A) (hJ : D.Stable J) [J.IsHopfIdeal K]

private def quotientActionMap (s : Gal(K/k)) : (A ⧸ J) →+* (A ⧸ J) :=
  Ideal.Quotient.lift J ((Ideal.Quotient.mk J).comp (actionRingHom D s))
    fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ s x hx)

omit [FiniteDimensional k K] [IsGalois k K] [J.IsHopfIdeal K] in
private theorem quotientActionMap_mk (s : Gal(K/k)) (x : A) :
    quotientActionMap J hJ s (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk J (D.action.act s x) := rfl

private def quotientAction : SemilinearAction k K (A ⧸ J) where
  act s :=
    { (quotientActionMap J hJ s).toAddMonoidHom with
      invFun := quotientActionMap J hJ s⁻¹
      left_inv := by
        intro q
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
        change quotientActionMap J hJ s⁻¹ (quotientActionMap J hJ s (Ideal.Quotient.mk J x)) = _
        rw [quotientActionMap_mk, quotientActionMap_mk, ← D.action.mul_act,
          inv_mul_cancel, D.action.one_act]
      right_inv := by
        intro q
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
        change quotientActionMap J hJ s (quotientActionMap J hJ s⁻¹ (Ideal.Quotient.mk J x)) = _
        rw [quotientActionMap_mk, quotientActionMap_mk, ← D.action.mul_act,
          mul_inv_cancel, D.action.one_act] }
  one_act := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    change quotientActionMap J hJ 1 (Ideal.Quotient.mk J x) = _
    rw [quotientActionMap_mk, D.action.one_act]
  mul_act := by
    intro s t q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    change quotientActionMap J hJ (s * t) (Ideal.Quotient.mk J x) =
      quotientActionMap J hJ s (quotientActionMap J hJ t (Ideal.Quotient.mk J x))
    simp only [quotientActionMap_mk, D.action.mul_act]
  map_smul := by
    intro s r q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    change quotientActionMap J hJ s (r • Ideal.Quotient.mk J x) =
      s r • quotientActionMap J hJ s (Ideal.Quotient.mk J x)
    have hs : r • Ideal.Quotient.mk J x = Ideal.Quotient.mk J (r • x) :=
      (map_smul (Ideal.Quotient.mkₐ K J) r x).symm
    rw [hs]
    rw [quotientActionMap_mk, D.action.map_smul, quotientActionMap_mk]
    exact map_smul (Ideal.Quotient.mkₐ K J) _ _

private def quotientDatum : HopfDescentDatum k (hopfQuotient A J) where
  action := quotientAction J hJ
  map_one s := map_one (quotientActionMap J hJ s)
  map_mul s := map_mul (quotientActionMap J hJ s)
  comul_equivariant := by
    let q := (hopfQuotientMap A J).hom
    have hq (s : Gal(K/k)) (x : A) :
        q (D.action.act s x) = (quotientAction J hJ).act s (q x) := rfl
    have ht := D.action.tensor_equivariant D.action (quotientAction J hJ) (quotientAction J hJ)
      q.toLinearMap hq q.toLinearMap hq
    intro s y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    change comul (R := K) ((quotientAction J hJ).act s (q x)) =
      ((quotientAction J hJ).tensor (quotientAction J hJ)).act s (comul (R := K) (q x))
    rw [← hq, ← CoalgHomClass.map_comp_comul_apply q, ← CoalgHomClass.map_comp_comul_apply q,
      D.comul_equivariant s x]
    exact ht s (comul (R := K) x)
  counit_equivariant := by
    intro s y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    let q := (hopfQuotientMap A J).hom
    change counit (R := K) (q (D.action.act s x)) =
      SemilinearAction.unit.act s (counit (R := K) (q x))
    rw [CoalgHomClass.counit_comp_apply q, CoalgHomClass.counit_comp_apply q]
    exact D.counit_equivariant s x
  antipode_equivariant := by
    intro s y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    let q := (hopfQuotientMap A J).hom
    have h (a : A) : q (antipode K a) = antipode K (q a) :=
      DFunLike.congr_fun (hopfSpecMorphism K (hopfQuotientMap A J)).2 a
    change antipode K (q (D.action.act s x)) = (quotientAction J hJ).act s (antipode K (q x))
    rw [← h, ← h]
    exact congrArg q (D.antipode_equivariant s x)

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem quotientMap_equivariant :
    D.Equivariant (quotientDatum J hJ) (hopfQuotientMap A J) := fun _ _ => rfl

open private LinearAlgebraicGroups.hopfMap_ker LinearAlgebraicGroups.liftHopfQuotient
  LinearAlgebraicGroups.extendedQuotientMap_ker from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem descendedMap_surjective {E : HopfDescentDatum k B} (L : HopfDescent E)
    (f : A ⟶ B) (hf : D.Equivariant E f) (hs : Function.Surjective f.hom) :
    Function.Surjective (restrictHopfHom H L f hf).hom := by
  let g := restrictHopfHom H L f hf
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k K g.hom.toLinearMap).mp
  intro y
  obtain ⟨x, hx⟩ := hs (L.iso.hom.hom y)
  obtain ⟨t, ht⟩ := H.comparison.surjective x
  refine ⟨t, L.comparison.injective ?_⟩
  have e := ConcreteCategory.congr_hom (restrictHopfHom_base H L f hf) t
  change f.hom (H.iso.hom.hom t) = L.iso.hom.hom ((extendedHopfMap K g).hom t) at e
  change L.iso.hom.hom ((extendedHopfMap K g).hom t) = L.iso.hom.hom y
  change H.iso.hom.hom t = x at ht
  rw [← e, ht, hx]

private theorem descendedQuotient_ker :
    RingHom.ker (restrictHopfHom H (descendHopf (quotientDatum J hJ))
      (hopfQuotientMap A J) (quotientMap_equivariant J hJ)).hom.toAlgHom =
      D.contract J := by
  ext x
  change (restrictHopfHom H (descendHopf (quotientDatum J hJ)) (hopfQuotientMap A J)
    (quotientMap_equivariant J hJ)).hom x = 0 ↔ (x : A) ∈ J
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

include hJ in
private theorem contract_isHopfIdeal : H.IsHopfIdeal (D.contract J) := by
  let L := descendHopf (quotientDatum J hJ)
  let q := hopfQuotientMap A J
  have hs := descendedMap_surjective H L q (quotientMap_equivariant J hJ)
    Ideal.Quotient.mk_surjective
  letI := H.operations.toHopfAlgebra
  change (D.contract J : Ideal H.algebra).IsHopfIdeal k
  rw [← descendedQuotient_ker H J hJ]
  exact LinearAlgebraicGroups.hopfMap_ker _ hs

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem extension_eq_map (I : Ideal H.algebra) :
    (extendedIdeal K I).map H.iso.hom.hom.toAlgHom = I.map D.fixed.val := by
  let j : D.fixed →+* K ⊗[k] D.fixed := Algebra.TensorProduct.includeRight.toRingHom
  let f := H.iso.hom.hom.toAlgHom.toRingHom
  change (I.map j).map f = I.map D.fixed.val.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  change H.iso.hom.hom (1 ⊗ₜ[k] x) = (x : A)
  exact (comparison_tmul H 1 x).trans (one_smul K _)

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem extension_stable (I : Ideal H.algebra) :
    D.Stable ((extendedIdeal K I).map H.iso.hom.hom.toAlgHom) := by
  rw [extension_eq_map H]
  intro s x hx
  have h : (I.map D.fixed.val).map (actionRingHom D s) ≤ I.map D.fixed.val := by
    rw [← Ideal.map_coe (f := D.fixed.val), Ideal.map_map]
    exact Ideal.map_le_iff_le_comap.mpr fun y hy =>
      show D.action.act s (y : A) ∈ I.map D.fixed.val by
        rw [y.property s]
        exact Ideal.mem_map_of_mem D.fixed.val hy
  exact h (Ideal.mem_map_of_mem (actionRingHom D s) hx)

private abbrev extendedQuotient (I : Ideal H.algebra) [H.IsHopfIdeal I] :
    A ⟶ extendedHopf K (H.quotient I) :=
  H.iso.inv ≫ extendedHopfMap K (H.quotientMap I)

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem extendedQuotient_surjective (I : Ideal H.algebra) [H.IsHopfIdeal I] :
    Function.Surjective (extendedQuotient H I).hom := by
  letI := H.operations.toHopfAlgebra
  have hq : Function.Surjective (extendedHopfMap K (H.quotientMap I)).hom :=
    Algebra.TensorProduct.map_surjective (AlgHom.id k K) (Ideal.Quotient.mkₐ k I)
      Function.surjective_id Ideal.Quotient.mk_surjective
  exact hq.comp H.comparison.symm.surjective

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem extendedQuotient_ker (I : Ideal H.algebra) [H.IsHopfIdeal I] :
    RingHom.ker (extendedQuotient H I).hom.toAlgHom =
      (extendedIdeal K I).map H.iso.hom.hom.toAlgHom := by
  letI := H.operations.toHopfAlgebra
  rw [← LinearAlgebraicGroups.extendedQuotientMap_ker K H.algebra I]
  ext x
  obtain ⟨t, rfl⟩ := H.comparison.surjective x
  change (extendedHopfMap K (H.quotientMap I)).hom (H.comparison.symm (H.comparison t)) = 0 ↔
    H.iso.hom.hom.toAlgHom t ∈ (RingHom.ker
      (extendedHopfMap K (H.quotientMap I)).hom.toAlgHom).map H.iso.hom.hom.toAlgHom
  have hsymm : H.comparison.symm (H.comparison t) = t := H.comparison.symm_apply_apply t
  rw [hsymm]
  let q := (extendedHopfMap K (H.quotientMap I)).hom.toAlgHom
  exact (SetLike.ext_iff.mp (Ideal.comap_map_of_bijective H.iso.hom.hom.toAlgHom
    H.comparison.bijective (I := RingHom.ker q)) t).symm

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem extension_isHopfIdeal (I : Ideal H.algebra) [H.IsHopfIdeal I] :
    ((extendedIdeal K I).map H.iso.hom.hom.toAlgHom).IsHopfIdeal K :=
  extendedQuotient_ker H I ▸
    LinearAlgebraicGroups.hopfMap_ker _ (extendedQuotient_surjective H I)

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem contract_extension (I : Ideal H.algebra) [H.IsHopfIdeal I] :
    D.contract ((extendedIdeal K I).map H.iso.hom.hom.toAlgHom) = I := by
  ext x
  letI := H.operations.toHopfAlgebra
  have hi := LinearAlgebraicGroups.extendedQuotientMap_ker K H.algebra I
  change D.fixed.val x ∈ (extendedIdeal K I).map H.iso.hom.hom.toAlgHom ↔ _
  have hx : H.iso.hom.hom (1 ⊗ₜ[k] x) = D.fixed.val x :=
    (comparison_tmul H 1 x).trans (one_smul K _)
  rw [← hx]
  change (1 ⊗ₜ[k] x : K ⊗[k] D.fixed) ∈
    ((extendedIdeal K I).map H.iso.hom.hom.toAlgHom).comap H.iso.hom.hom.toAlgHom ↔ _
  rw [Ideal.comap_map_of_bijective H.iso.hom.hom.toAlgHom H.comparison.bijective, ← hi]
  change (1 ⊗ₜ[k] (Ideal.Quotient.mk I x) : K ⊗[k] (H.algebra ⧸ I)) = 0 ↔ x ∈ I
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K)
    (H.algebra ⧸ I) (h.trans (TensorProduct.tmul_zero _ _).symm),
    fun h => by rw [h, TensorProduct.tmul_zero]⟩

include hJ in
private theorem extension_contract :
    (extendedIdeal K (D.contract J : Ideal H.algebra)).map H.iso.hom.hom.toAlgHom = J := by
  let L := descendHopf (quotientDatum J hJ)
  let q := hopfQuotientMap A J
  let g := restrictHopfHom H L q (quotientMap_equivariant J hJ)
  have hs := descendedMap_surjective H L q (quotientMap_equivariant J hJ) Ideal.Quotient.mk_surjective
  have hg := restrictHopfHom_base H L q (quotientMap_equivariant J hJ)
  have hk : RingHom.ker (extendedHopfMap K g).hom.toAlgHom =
      extendedIdeal K (D.contract J : Ideal H.algebra) := by
    have hs' : Function.Surjective g.hom.toAlgHom := hs
    have hker : RingHom.ker g.hom.toAlgHom = (D.contract J : Ideal H.algebra) :=
      descendedQuotient_ker H J hJ
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) g.hom.toAlgHom) = _
    exact (Algebra.TensorProduct.lTensor_ker (A := K) g.hom.toAlgHom hs').trans
      (congrArg (extendedIdeal (A := H.algebra) K) hker)
  rw [← hk]
  apply (Ideal.comap_injective_of_surjective H.iso.hom.hom.toAlgHom H.comparison.surjective)
  rw [Ideal.comap_map_of_bijective H.iso.hom.hom.toAlgHom H.comparison.bijective]
  ext t
  have h := ConcreteCategory.congr_hom hg t
  change Ideal.Quotient.mk J (H.iso.hom.hom t) =
    L.iso.hom.hom ((extendedHopfMap K g).hom t) at h
  change (extendedHopfMap K g).hom t = 0 ↔ H.iso.hom.hom t ∈ J
  have ht : H.iso.hom.hom t ∈ J ↔ Ideal.Quotient.mk J (H.iso.hom.hom t) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.symm
  rw [ht, h]
  exact ⟨fun e => by rw [e, map_zero], fun e => L.comparison.injective (e.trans (map_zero _).symm)⟩

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem descentQuotientIso (I : Ideal H.algebra) [H.IsHopfIdeal I]
    (hI : (extendedIdeal K I).map H.iso.hom.hom.toAlgHom = J) :
    ∃ q : extendedHopf K (H.quotient I) ≅ hopfQuotient A J,
      extendedHopfMap K (H.quotientMap I) ≫ q.hom =
        H.iso.hom ≫ hopfQuotientMap A J := by
  let f := extendedQuotient H I
  have hs := extendedQuotient_surjective H I
  have hk : RingHom.ker f.hom.toAlgHom = J := (extendedQuotient_ker H I).trans hI
  let b := LinearAlgebraicGroups.liftHopfQuotient J f
    (fun x hx => show x ∈ RingHom.ker f.hom.toAlgHom from hk.symm ▸ hx)
  have hb : Function.Bijective b.hom := by
    constructor
    · intro x y he
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply sub_eq_zero.mp
      rw [← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hk, RingHom.mem_ker]
      change f.hom (x - y) = 0
      change f.hom x = f.hom y at he
      rw [map_sub, he, sub_self]
    · intro y
      obtain ⟨x, hx⟩ := hs y
      exact ⟨Ideal.Quotient.mk J x, hx⟩
  let e := CommHopfAlgCat.isoMk (BialgEquiv.ofBijective b.hom hb)
  have he : hopfQuotientMap A J ≫ e.hom = f := by
    apply CommHopfAlgCat.hom_ext
    exact BialgHom.ext fun x => rfl
  refine ⟨e.symm, ?_⟩
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, Category.assoc, he]
  change _ = H.iso.hom ≫ H.iso.inv ≫ _
  rw [Iso.hom_inv_id_assoc]

theorem affineDescentIdeals : AffineGroupSpecs.Ideals.{u} := by
  intro k K _ _ _ _ _ A D H
  let e : {J : Ideal A // J.IsHopfIdeal K ∧ D.Stable J} ≃o
      {I : Ideal H.algebra // H.IsHopfIdeal I} :=
    { toFun := fun J =>
        letI := J.2.1
        ⟨D.contract J.1, contract_isHopfIdeal H J.1 J.2.2⟩
      invFun := fun I =>
        letI := I.2
        ⟨(extendedIdeal K I.1).map H.iso.hom.hom.toAlgHom,
          extension_isHopfIdeal H I.1, extension_stable H I.1⟩
      left_inv := fun J =>
        letI := J.2.1
        Subtype.ext (extension_contract H J.1 J.2.2)
      right_inv := fun I =>
        letI := I.2
        Subtype.ext (contract_extension H I.1)
      map_rel_iff' := by
        intro J J'
        change D.contract J.1 ≤ D.contract J'.1 ↔ J.1 ≤ J'.1
        refine ⟨fun h => ?_, Ideal.comap_mono⟩
        letI := J.2.1
        letI := J'.2.1
        rw [← extension_contract H J.1 J.2.2, ← extension_contract H J'.1 J'.2.2]
        exact Ideal.map_mono (Ideal.map_mono h) }
  refine ⟨e, fun _ => rfl, fun _ => rfl, ?_⟩
  intro J
  dsimp only
  letI := J.2.1
  letI := (e J).2
  exact descentQuotientIso H J.1 (e J).1 (extension_contract H J.1 J.2.2)

theorem affineDescentSubgroups : AffineGroupSpecs.Subgroups.{u} := by
  intro k K _ _ _ _ _ A D H S i
  obtain ⟨e, hcontract, _, _⟩ := affineDescentIdeals H
  let P (I : Ideal H.algebra) : Prop :=
    ∃ (_ : H.IsHopfIdeal I), ∃ j : S ≅ specGroup (H.quotient I),
      j.hom ≫ specGroupMap (H.quotientMap I) = i
  change IsClosedImmersion i.hom.hom.left ↔
    ∃! J : {J : Ideal A // J.IsHopfIdeal K ∧ D.Stable J}, P (D.contract J.1)
  have hclass : IsClosedImmersion i.hom.hom.left ↔ ∃! I, P I :=
    closedSubgroupClassification k H.algebra S i
  have hg (J : {J : Ideal A // J.IsHopfIdeal K ∧ D.Stable J}) :
      P (e J).1 ↔ P (D.contract J.1) := Iff.of_eq (congrArg P (hcontract J))
  constructor
  · intro hi
    obtain ⟨I, hI, huniq⟩ := hclass.mp hi
    let I' : {I : Ideal H.algebra // H.IsHopfIdeal I} := ⟨I, by obtain ⟨h, _⟩ := hI; exact h⟩
    let J := e.symm I'
    have hJ : e J = I' := e.apply_symm_apply I'
    refine ⟨J, (hg J).mp (by rw [hJ]; exact hI), ?_⟩
    intro J' hJ'
    apply e.injective
    rw [hJ]
    exact Subtype.ext (huniq _ ((hg J').mpr hJ'))
  · rintro ⟨J, hJ, huniq⟩
    apply hclass.mpr
    refine ⟨(e J).1, (hg J).mpr hJ, ?_⟩
    intro I hI
    let I' : {I : Ideal H.algebra // H.IsHopfIdeal I} := ⟨I, by obtain ⟨h, _⟩ := hI; exact h⟩
    let J' := e.symm I'
    have hJ' : e J' = I' := e.apply_symm_apply I'
    have hj : J' = J := huniq J' ((hg J').mp (by rw [hJ']; exact hI))
    exact congrArg Subtype.val (hJ'.symm.trans (congrArg e hj))

end Ideals

end
end LinearAlgebraicGroups.Descent
