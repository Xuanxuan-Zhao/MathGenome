import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.BaseChange
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Group
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Tensor
import Mathlib.Algebra.Group.Subgroup.Ker
import Batteries.Tactic.OpenPrivate

/-! Scalar extension of Brauer classes and the relative Brauer subgroup. -/

namespace RM03.Brauer

open Specs.RM03.Brauer (IsScalarExtension)

open scoped TensorProduct
open private oneMatrixEquiv from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Equivalence
open Algebra.TensorProduct (assoc congr rid lid)

universe u w x v

variable (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]

/-- Scalar extension commutes with square matrix algebras. -/
noncomputable def baseChangeMatrix (n : ℕ) (A : Type v) [Ring A] [Algebra k A] :
    L ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[L] Matrix (Fin n) (Fin n) (L ⊗[k] A) :=
  (congr (oneMatrixEquiv L L).symm
      (AlgEquiv.refl : Matrix (Fin n) (Fin n) A ≃ₐ[k] _)).trans
    ((Matrix.kroneckerTMulAlgEquiv (Fin 1) (Fin n) k L L A).trans
      (Matrix.reindexAlgEquiv L (L ⊗[k] A) (Equiv.uniqueProd (Fin n) (Fin 1))))

@[simp]
theorem baseChangeMatrix_tmul (n : ℕ) (A : Type v) [Ring A] [Algebra k A]
    (l : L) (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    baseChangeMatrix k L n A (l ⊗ₜ[k] M) i j = l ⊗ₜ[k] M i j := by
  simp only [baseChangeMatrix, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply,
    Matrix.kroneckerTMulAlgEquiv_apply, kroneckerTMulLinearEquiv_tmul, Matrix.coe_reindexAlgEquiv]
  change Matrix.scalar (Fin 1) l 0 0 ⊗ₜ[k] M i j = _
  simp [Matrix.scalar_apply]

theorem scalarExtensionMatrix : Specs.RM03.Brauer.ScalarExtensionMatrix.{u, w, v} :=
  fun k _ L _ _ n A _ _ ↦ ⟨baseChangeMatrix k L n A, baseChangeMatrix_tmul k L n A⟩

/-- Scalar extension commutes with the tensor product of algebras. -/
def baseChangeTensor (A : Type v) [Ring A] [Algebra k A]
    (B : Type x) [Ring B] [Algebra k B] :
    L ⊗[k] (A ⊗[k] B) ≃ₐ[L] (L ⊗[k] A) ⊗[L] (L ⊗[k] B) :=
  (assoc k k L L A B).symm.trans <|
    (congr (rid L L (L ⊗[k] A)).symm (AlgEquiv.refl : B ≃ₐ[k] B)).trans
      (assoc k L L (L ⊗[k] A) L B)

@[simp]
theorem baseChangeTensor_tmul (A : Type v) [Ring A] [Algebra k A]
    (B : Type x) [Ring B] [Algebra k B] (l : L) (a : A) (b : B) :
    baseChangeTensor k L A B (l ⊗ₜ[k] (a ⊗ₜ[k] b)) =
      (l ⊗ₜ[k] a) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] b) := rfl

theorem scalarExtensionTensor : Specs.RM03.Brauer.ScalarExtensionTensor.{u, w, x, v} :=
  fun k _ L _ _ A _ _ B _ _ ↦ ⟨baseChangeTensor k L A B, baseChangeTensor_tmul k L A B⟩

/-- The canonical identification of iterated scalar extension with direct scalar extension. -/
def baseChangeTower (F : Type x) [Field F] [Algebra k F] [Algebra L F] [IsScalarTower k L F]
    (A : Type v) [Ring A] [Algebra k A] :
    F ⊗[L] (L ⊗[k] A) ≃ₐ[F] F ⊗[k] A :=
  (assoc k L F F L A).symm.trans
    (congr (rid L F F) (AlgEquiv.refl : A ≃ₐ[k] A))

@[simp]
theorem baseChangeTower_tmul
    (F : Type x) [Field F] [Algebra k F] [Algebra L F] [IsScalarTower k L F]
    (A : Type v) [Ring A] [Algebra k A] (f : F) (l : L) (a : A) :
    baseChangeTower k L F A (f ⊗ₜ[L] (l ⊗ₜ[k] a)) = (l • f) ⊗ₜ[k] a := rfl

theorem scalarExtensionTowerEquiv : Specs.RM03.Brauer.ScalarExtensionTowerEquiv.{u, w, x, v} :=
  fun k _ L _ _ F _ _ _ _ A _ _ ↦ ⟨baseChangeTower k L F A, baseChangeTower_tmul k L F A⟩

/-- A central simple algebra over the extension field, on the scalar-extended carrier. -/
def baseChangeCSA (A : _root_.CSA.{u, v} k) : _root_.CSA.{w, max w v} L :=
  CSA.toCSA (A := CSA.BaseChange k L A)
    (CSA.isCentralSimple_baseChange ⟨A.isSimple, A.isCentral, A.fin_dim⟩)

theorem baseChange_respects_equivalence
    {A : Type v} [Ring A] [Algebra k A] {B : Type x} [Ring B] [Algebra k B]
    (h : Equivalent k A B) : Equivalent L (CSA.BaseChange k L A) (CSA.BaseChange k L B) := by
  obtain ⟨p, q, hp, hq, ⟨e⟩⟩ := h
  exact ⟨p, q, hp, hq, ⟨(baseChangeMatrix k L p A).symm.trans <|
    (congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans (baseChangeMatrix k L q B)⟩⟩

/-- Scalar extension on the Brauer quotient before equipping it with the homomorphism laws. -/
def baseChangeClass : BrauerGroup.{u, v} k → BrauerGroup.{w, max w v} L :=
  Quotient.map (baseChangeCSA k L) fun A B h ↦
    (equivalent_iff_isBrauerEquivalent L (baseChangeCSA k L A) (baseChangeCSA k L B)).mp
      (baseChange_respects_equivalence k L ((equivalent_iff_isBrauerEquivalent k A B).mpr h))

theorem baseChangeClass_isScalarExtension :
    IsScalarExtension k L (baseChangeClass.{u, w, v} k L) :=
  fun A ↦ ⟨baseChangeCSA k L A, rfl, rfl⟩

private theorem csa_eq_of_toAlgCat_eq {S : Type u} [Field S]
    {A B : _root_.CSA.{u, v} S} (h : A.toAlgCat = B.toAlgCat) : A = B := by
  cases A with
  | mk A =>
    cases B with
    | mk B =>
      change A = B at h
      subst B
      rfl

private theorem eq_baseChangeClass
    {f : BrauerGroup.{u, v} k → BrauerGroup.{w, max w v} L}
    (hf : IsScalarExtension k L f) : f = baseChangeClass k L := by
  funext a
  refine Quotient.inductionOn a fun A ↦ ?_
  obtain ⟨B, hAlg, hClass⟩ := hf A
  have hB : B = baseChangeCSA k L A := csa_eq_of_toAlgCat_eq hAlg
  rw [hB] at hClass
  exact hClass

theorem scalarExtensionOnClasses : Specs.RM03.Brauer.ScalarExtensionOnClasses.{u, w, v} :=
  fun k _ L _ _ ↦ ⟨baseChangeClass k L, baseChangeClass_isScalarExtension k L,
    fun _ hf ↦ eq_baseChangeClass k L hf⟩

/-- Scalar extension induces an additive homomorphism of Brauer groups. -/
def baseChange :
    letI := instAddCommGroup.{u, max w v} k
    letI := instAddCommGroup.{w, max u v} L
    BrauerGroup.{u, max u w v} k →+ BrauerGroup.{w, max u w v} L := by
  letI := instAddCommGroup.{u, max w v} k
  letI := instAddCommGroup.{w, max u v} L
  refine { toFun := baseChangeClass k L, map_zero' := ?_, map_add' := ?_ }
  · change classOf (baseChangeCSA k L (scalarCSA.{u, max w v} k)) =
      classOf (scalarCSA.{w, max u v} L)
    apply classOf_eq_of_algEquiv
    exact (congr (AlgEquiv.refl : L ≃ₐ[L] L) (ULift.algEquiv (R := k))).trans
      ((rid k L L).trans (ULift.algEquiv (R := L)).symm)
  · intro a b
    exact Quotient.inductionOn₂ a b fun A B ↦
      classOf_eq_of_algEquiv (baseChangeTensor k L A B)

@[simp]
theorem baseChange_classOf (A : _root_.CSA.{u, max u w v} k) :
    baseChange.{u, w, v} k L (classOf A) = classOf (baseChangeCSA k L A) := rfl

@[simp]
theorem baseChange_self :
    baseChange.{u, u, v} k k = AddMonoidHom.id (BrauerGroup.{u, max u v} k) := by
  ext a
  exact Quotient.inductionOn a fun A ↦ classOf_eq_of_algEquiv (lid k A)

theorem baseChange_comp (F : Type x) [Field F] [Algebra k F] [Algebra L F] [IsScalarTower k L F] :
    (baseChange.{w, x, max u v} L F).comp (baseChange.{u, w, max x v} k L) =
      baseChange.{u, x, max w v} k F := by
  ext a
  exact Quotient.inductionOn a fun A ↦ classOf_eq_of_algEquiv (baseChangeTower k L F A)

/-- The relative Brauer subgroup attached to a scalar-extension homomorphism. -/
def relativeSubgroup {B : Type u} {C : Type w} [AddGroup B] [AddGroup C]
    (f : B →+ C) : AddSubgroup B :=
  f.ker

/-- The relative Brauer subgroup, defined for any extension and in particular for finite Galois
extensions. -/
def relativeBrauerGroup :
    letI := instAddCommGroup.{u, max w v} k
    AddSubgroup (BrauerGroup.{u, max u w v} k) :=
  letI := instAddCommGroup.{u, max w v} k
  relativeSubgroup (baseChange.{u, w, v} k L)

@[simp]
theorem classOf_mem_relativeBrauerGroup_iff (A : _root_.CSA.{u, max u w v} k) :
    letI := instAddCommGroup.{w, max u v} L
    classOf A ∈ relativeBrauerGroup.{u, w, v} k L ↔ CSA.Splits k L A := by
  change classOf (baseChangeCSA k L A) = 0 ↔ CSA.Splits k L A
  exact classOf_eq_zero_iff_split (baseChangeCSA k L A)

/-- In a tower, every class split by the intermediate field is split by the top field. -/
theorem relativeBrauerGroup_le (F : Type x) [Field F] [Algebra k F] [Algebra L F]
    [IsScalarTower k L F] :
    letI := instAddCommGroup.{u, max w x v} k
    relativeBrauerGroup.{u, w, max x v} k L ≤ relativeBrauerGroup.{u, x, max w v} k F := by
  intro a ha
  change baseChange.{u, w, max x v} k L a = 0 at ha
  change baseChange.{u, x, max w v} k F a = 0
  rw [← baseChange_comp.{u, w, x, v} k L F, AddMonoidHom.comp_apply, ha, map_zero]

/-- The inclusion of relative Brauer groups is induced by the identity of the ambient group. -/
def relativeBrauerInclusion (F : Type x) [Field F] [Algebra k F] [Algebra L F]
    [IsScalarTower k L F] :
    letI := instAddCommGroup.{u, max w x v} k
    relativeBrauerGroup.{u, w, max x v} k L →+
      relativeBrauerGroup.{u, x, max w v} k F :=
  letI := instAddCommGroup.{u, max w x v} k
  AddSubgroup.inclusion (relativeBrauerGroup_le.{u, w, x, v} k L F)

@[simp]
theorem coe_relativeBrauerInclusion (F : Type x) [Field F] [Algebra k F] [Algebra L F]
    [IsScalarTower k L F] (a : relativeBrauerGroup.{u, w, max x v} k L) :
    (relativeBrauerInclusion.{u, w, x, v} k L F a : BrauerGroup.{u, max u w x v} k) = a := rfl

private theorem groupLaws (k : Type u) [Field k] :
    Specs.RM03.Brauer.GroupLaws.{u, v} k (instAddCommGroup.{u, v} k) :=
  ⟨zero_eq_classOf_scalar k,
    fun A B ↦ ⟨tensorCSA A B, rfl, classOf_add A B⟩,
    fun A ↦ ⟨oppositeCSA A, rfl, classOf_neg A⟩, classOf_eq_zero_iff_split⟩

theorem scalarExtensionGroupLaw : Specs.RM03.Brauer.ScalarExtensionGroupLaw.{u, w, v} := by
  intro k _ L _ _
  exact ⟨instAddCommGroup.{u, max w v} k, instAddCommGroup.{w, max u v} L,
    groupLaws.{u, max w v} k, groupLaws.{w, max u v} L, baseChange.{u, w, v} k L,
    baseChangeClass_isScalarExtension k L, classOf_mem_relativeBrauerGroup_iff.{u, w, v} k L⟩

theorem scalarExtensionIdentity : Specs.RM03.Brauer.ScalarExtensionIdentity.{u, v} := by
  intro k _ f hf
  rw [eq_baseChangeClass k k hf]
  funext a
  exact DFunLike.congr_fun (baseChange_self.{u, v} k) a

theorem scalarExtensionTower : Specs.RM03.Brauer.ScalarExtensionTower.{u, w, x, v} := by
  intro k _ L _ _ F _ _ _ _ f g h hf hg hh
  rw [eq_baseChangeClass k L hf, eq_baseChangeClass L F hg, eq_baseChangeClass k F hh]
  funext a
  exact DFunLike.congr_fun (baseChange_comp.{u, w, x, v} k L F) a

theorem relativeSubgroupTower : Specs.RM03.Brauer.RelativeSubgroupTower.{u, w, x, v} := by
  intro k _ L _ _ F _ _ _ _ _ _ _ f g h hf hg hh
  have hcomp := scalarExtensionTower.{u, w, x, v} k L F f g h hf hg hh
  have hle : relativeSubgroup f ≤ relativeSubgroup h := by
    intro a ha
    change f a = 0 at ha
    change h a = 0
    rw [← congrFun hcomp a]
    exact (congrArg g ha).trans (map_zero g)
  exact ⟨AddSubgroup.inclusion hle, AddSubgroup.inclusion_injective hle, fun _ ↦ rfl⟩

end RM03.Brauer
