import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.Group
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Equivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Tensor
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.RingTheory.MatrixAlgebra

/-! The additive group law on the Brauer quotient. -/

namespace RM03.Brauer

open scoped TensorProduct
open MulOpposite

universe u v w

variable {k : Type u} [Field k]

/-- Tensor products of central simple algebras as representatives of Brauer classes. -/
def tensorCSA (A B : _root_.CSA.{u, v} k) : _root_.CSA.{u, v} k :=
  CSA.toCSA (A := A ⊗[k] B)
    (CSA.isCentralSimple_tensor ⟨A.isSimple, A.isCentral, A.fin_dim⟩
      ⟨B.isSimple, B.isCentral, B.fin_dim⟩)

/-- The opposite of a central simple algebra as a representative of a Brauer class. -/
def oppositeCSA (A : _root_.CSA.{u, v} k) : _root_.CSA.{u, v} k :=
  CSA.toCSA (A := Aᵐᵒᵖ) ⟨inferInstance, inferInstance, inferInstance⟩

theorem classOf_eq_of_algEquiv {A B : _root_.CSA.{u, v} k} (e : A ≃ₐ[k] B) :
    classOf A = classOf B :=
  (classOf_eq_iff k A B).mpr ⟨1, 1, Nat.one_pos, Nat.one_pos, ⟨e.mapMatrix⟩⟩

/-- Tensoring two matrix algebras is matrix stabilization of the tensor product. -/
private def matrixTensorEquiv (n m : ℕ) (A : Type v) [Ring A] [Algebra k A]
    (B : Type w) [Ring B] [Algebra k B] :
    Matrix (Fin n) (Fin n) A ⊗[k] Matrix (Fin m) (Fin m) B ≃ₐ[k]
      Matrix (Fin (n * m)) (Fin (n * m)) (A ⊗[k] B) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin m) k k A B).trans
    (Matrix.reindexAlgEquiv k (A ⊗[k] B) finProdFinEquiv)

theorem tensor_respects_equivalence
    {A A' : Type v} [Ring A] [Ring A'] [Algebra k A] [Algebra k A']
    {B B' : Type w} [Ring B] [Ring B'] [Algebra k B] [Algebra k B']
    (hA : Equivalent k A A') (hB : Equivalent k B B') :
    Equivalent k (A ⊗[k] B) (A' ⊗[k] B') := by
  obtain ⟨p, q, hp, hq, ⟨e⟩⟩ := hA
  obtain ⟨r, s, hr, hs, ⟨f⟩⟩ := hB
  exact ⟨p * r, q * s, Nat.mul_pos hp hr, Nat.mul_pos hq hs,
    ⟨(matrixTensorEquiv p r A B).symm.trans <|
      (Algebra.TensorProduct.congr e f).trans (matrixTensorEquiv q s A' B')⟩⟩

theorem opposite_respects_equivalence
    {A : Type v} [Ring A] [Algebra k A] {B : Type w} [Ring B] [Algebra k B]
    (h : Equivalent k A B) : Equivalent k Aᵐᵒᵖ Bᵐᵒᵖ := by
  obtain ⟨p, q, hp, hq, ⟨e⟩⟩ := h
  exact ⟨p, q, hp, hq, ⟨AlgEquiv.mopMatrix.trans (e.op.trans AlgEquiv.mopMatrix.symm)⟩⟩

theorem tensor_opposite_split (A : _root_.CSA.{u, v} k) :
    CSA.IsSplit k (A ⊗[k] Aᵐᵒᵖ) := by
  obtain ⟨e, -⟩ := CSA.enveloping_isomorphism
    (A := A) ⟨A.isSimple, A.isCentral, A.fin_dim⟩
  exact ⟨Module.finrank k A, Module.finrank_pos, ⟨e.trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis k A))⟩⟩

private def addClasses : BrauerGroup.{u, v} k → BrauerGroup.{u, v} k → BrauerGroup.{u, v} k :=
  Quotient.map₂ tensorCSA fun _ _ hA _ _ hB ↦
    (equivalent_iff_isBrauerEquivalent k _ _).mp <|
      tensor_respects_equivalence
        ((equivalent_iff_isBrauerEquivalent k _ _).mpr hA)
        ((equivalent_iff_isBrauerEquivalent k _ _).mpr hB)

private def negClass : BrauerGroup.{u, v} k → BrauerGroup.{u, v} k :=
  Quotient.map oppositeCSA fun _ _ h ↦
    (equivalent_iff_isBrauerEquivalent k _ _).mp <|
      opposite_respects_equivalence ((equivalent_iff_isBrauerEquivalent k _ _).mpr h)

instance instAddCommGroup (k : Type u) [Field k] :
    AddCommGroup (BrauerGroup.{u, max u v} k) := by
  let Br := BrauerGroup.{u, max u v} k
  letI : Add Br := ⟨addClasses⟩
  letI : Neg Br := ⟨negClass⟩
  letI : Zero Br := ⟨classOf (scalarCSA.{u, v} k)⟩
  have assoc (a b c : Br) : (a + b) + c = a + (b + c) := by
    refine Quotient.inductionOn₃ a b c fun A B C ↦ ?_
    exact classOf_eq_of_algEquiv (Algebra.TensorProduct.assoc k k k A B C)
  have add_scalar (a : Br) : a + 0 = a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    let e : ULift.{v} k ≃ₐ[k] k := ULift.algEquiv
    exact classOf_eq_of_algEquiv
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) e).trans
        (Algebra.TensorProduct.rid k k A))
  have add_opposite (a : Br) : a + -a = 0 := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact (classOf_eq_scalar_iff_split k (tensorCSA A (oppositeCSA A))).mpr
      (tensor_opposite_split A)
  exact
    { AddGroup.ofRightAxioms assoc add_scalar add_opposite with
      add_comm := fun a b ↦ Quotient.inductionOn₂ a b fun A B ↦
        classOf_eq_of_algEquiv (Algebra.TensorProduct.comm k A B) }

@[simp]
theorem classOf_add (A B : _root_.CSA.{u, max u v} k) :
    classOf A + classOf B = classOf (tensorCSA A B) := rfl

theorem zero_eq_classOf_scalar (k : Type u) [Field k] :
    (0 : BrauerGroup.{u, max u v} k) = classOf (scalarCSA.{u, v} k) := rfl

@[simp]
theorem classOf_neg (A : _root_.CSA.{u, max u v} k) :
    -classOf A = classOf (oppositeCSA A) := rfl

theorem classOf_eq_zero_iff_split (A : _root_.CSA.{u, max u v} k) :
    classOf A = 0 ↔ CSA.IsSplit k A :=
  classOf_eq_scalar_iff_split k A

theorem group_law (k : Type u) [Field k] :
    ∃ g : AddCommGroup (BrauerGroup.{u, max u v} k), Specs.RM03.Brauer.GroupLaws.{u, v} k g :=
  ⟨instAddCommGroup k, zero_eq_classOf_scalar k,
    fun A B ↦ ⟨tensorCSA A B, rfl, classOf_add A B⟩,
    fun A ↦ ⟨oppositeCSA A, rfl, classOf_neg A⟩, classOf_eq_zero_iff_split⟩

end RM03.Brauer
