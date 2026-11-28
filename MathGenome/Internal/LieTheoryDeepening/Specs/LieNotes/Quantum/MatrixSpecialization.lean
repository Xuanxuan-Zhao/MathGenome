import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Hopf
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.TriangularPBW
import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWOrdered
import Mathlib.Algebra.Lie.Classical
import Mathlib.RingTheory.Polynomial.Quotient

/-! The comparison of the level-one quantum presentation with the ordinary
enveloping algebra of the traceless three-by-three matrices. -/

noncomputable section

open scoped TensorProduct

namespace Specs.LieNotes.Quantum.MatrixSpecialization

open Presentation
open _root_.Shared.Lie.PBW (OrderedWord)

universe u

abbrev LevelOne (k : Type u) [Field k] [CharZero k] := Uₙ k 1

abbrev Sl3 (k : Type u) [Field k] := LieAlgebra.SpecialLinear.sl (Fin 3) k

abbrev Classical (k : Type u) [Field k] := UniversalEnvelopingAlgebra k (Sl3 k)

/-- The scalar identification is evaluation at the zero value of the parameter. -/
def coefficientEquiv (k : Type u) [Field k] : Truncations.A k 1 ≃ₐ[k] k := by
  refine (Ideal.quotientEquivAlgOfEq k ?_).trans (Polynomial.quotientSpanXSubCAlgEquiv 0)
  simp [Truncations.truncationIdeal]

/-- Restrict the scalars of the level-one presentation along the constant polynomials. -/
scoped instance levelOneAlgebra (k : Type u) [Field k] [CharZero k] :
    Algebra k (LevelOne k) :=
  Algebra.compHom _ (algebraMap k (Truncations.A k 1))

scoped instance levelOneScalarTower (k : Type u) [Field k] [CharZero k] :
    IsScalarTower k (Truncations.A k 1) (LevelOne k) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := Truncations.A k 1) (A := LevelOne k)
    fun _ => rfl

section Matrices

variable (k : Type u) [Field k]

def matrixUnit (i j : Fin 3) (h : i ≠ j) : Sl3 k :=
  LieAlgebra.SpecialLinear.single i j h 1

def matrixE (i : Root) : Sl3 k :=
  matrixUnit k i.castSucc i.succ (by
    intro h
    exact Nat.ne_of_lt (Nat.lt_succ_self i.val) (congrArg Fin.val h))

def matrixF (i : Root) : Sl3 k :=
  matrixUnit k i.succ i.castSucc (by
    intro h
    exact Nat.ne_of_lt (Nat.lt_succ_self i.val) (congrArg Fin.val h.symm))

def matrixH (i : Root) : Sl3 k :=
  LieAlgebra.SpecialLinear.singleSubSingle i.castSucc i.succ 1

/-- Negative roots, Cartan elements, and positive roots in the source PBW order. -/
def matrixBasisVector : Fin 8 → Sl3 k :=
  ![matrixF k 0, -matrixUnit k 2 0 (by decide), matrixF k 1,
    matrixH k 0, matrixH k 1, matrixE k 0, matrixUnit k 0 2 (by decide), matrixE k 1]

end Matrices

/-- The ordinary type-A₂ commutator relations. -/
structure OrdinaryRelations {k : Type u} [Field k] {L : Type u} [LieRing L]
    [LieAlgebra k L] (e f h : Root → L) : Prop where
  cartan (l i : Root) : ⁅h l, h i⁆ = 0
  cartanE (l i : Root) : ⁅h l, e i⁆ = (cartanMatrix l i : k) • e i
  cartanF (l i : Root) : ⁅h l, f i⁆ = -(cartanMatrix l i : k) • f i
  mixed (i j : Root) : ⁅e i, f j⁆ = if i = j then h i else 0
  serreE (i j : Root) (hij : i ≠ j) : ⁅e i, ⁅e i, e j⁆⁆ = 0
  serreF (i j : Root) (hij : i ≠ j) : ⁅f i, ⁅f i, f j⁆⁆ = 0

attribute [local instance 100] LieRing.ofAssociativeRing

def LevelOneRelations : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    (truncated k 1).q = 1 ∧
    (∀ i, (truncated k 1).K i = 1 ∧ (truncated k 1).D i = MvPolynomial.X i) ∧
    OrdinaryRelations (k := k) (E (truncated k 1)) (F (truncated k 1)) (Coproduct.H k 1)

def MatrixRelations : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    OrdinaryRelations (k := k) (matrixE k) (matrixF k) (matrixH k) ∧
    ⁅matrixE k 0, matrixE k 1⁆ = matrixUnit k 0 2 (by decide) ∧
    ⁅matrixF k 0, matrixF k 1⁆ = -matrixUnit k 2 0 (by decide)

abbrev Index := TriangularPBW.PBWIndex (Root → ℕ)

/-- Counts in the order of the matrix basis, including both Cartan powers. -/
def exponentCounts (i : Index) : Fin 8 → ℕ :=
  ![i.1.1.1, i.1.1.2.1, i.1.1.2.2, i.1.2 0, i.1.2 1, i.2.1, i.2.2.1, i.2.2.2]

def quantumMonomial (k : Type u) [Field k] [CharZero k] (i : Index) : LevelOne k :=
  TriangularPBW.orderedMonomial (truncated k 1) i.1.1
    (∏ l : Root, (MvPolynomial.X l : TruncatedCartan k 1) ^ i.1.2 l) i.2

section Comparison

variable {k : Type u} [Field k] [CharZero k]

structure GeneratorImages (e : LevelOne k ≃ₐ[k] Classical k) : Prop where
  map_E (i : Root) : e (E (truncated k 1) i) = UniversalEnvelopingAlgebra.ι k (matrixE k i)
  map_F (i : Root) : e (F (truncated k 1) i) = UniversalEnvelopingAlgebra.ι k (matrixF k i)
  map_H (i : Root) : e (Coproduct.H k 1 i) = UniversalEnvelopingAlgebra.ι k (matrixH k i)
  map_zPlus : e (TriangularPBW.zPlus (truncated k 1)) =
    UniversalEnvelopingAlgebra.ι k (matrixUnit k 0 2 (by decide))
  map_zMinus : e (TriangularPBW.zMinus (truncated k 1)) =
    UniversalEnvelopingAlgebra.ι k (-matrixUnit k 2 0 (by decide))

def PBWComparison (e : LevelOne k ≃ₐ[k] Classical k) : Prop :=
  ∃ b : Module.Basis (Fin 8) k (Sl3 k), (∀ j, b j = matrixBasisVector k j) ∧
    ∃ words : OrderedWord (Fin 8) ≃ Index,
      (∀ w j, exponentCounts (words w) j = w.val.count j) ∧
      ∃ B : Module.Basis (OrderedWord (Fin 8)) k (Classical k),
        (∀ w, B w = _root_.Shared.Lie.PBW.orderedMonomial b w) ∧
        ∀ w, e (quantumMonomial k (words w)) = B w

/-- The ordinary enveloping Hopf structure, with operations over the canonical
k-algebra of the enveloping construction. -/
structure ClassicalHopf (k : Type u) [Field k] where
  comul : Classical k →ₐ[k] Classical k ⊗[k] Classical k
  counit : Classical k →ₐ[k] k
  antipode : Classical k →ₗ[k] Classical k
  coassoc : (Algebra.TensorProduct.assoc k k k (Classical k) (Classical k) (Classical k)).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (AlgHom.id k (Classical k))).comp comul) =
    (Algebra.TensorProduct.map (AlgHom.id k (Classical k)) comul).comp comul
  left_counit : (Algebra.TensorProduct.map counit (AlgHom.id k (Classical k))).comp comul =
    (Algebra.TensorProduct.lid k (Classical k)).symm
  right_counit : (Algebra.TensorProduct.map (AlgHom.id k (Classical k)) counit).comp comul =
    (Algebra.TensorProduct.rid k k (Classical k)).symm
  left_antipode : LinearMap.mul' k (Classical k) ∘ₗ antipode.rTensor (Classical k) ∘ₗ
      comul.toLinearMap = Algebra.linearMap k (Classical k) ∘ₗ counit.toLinearMap
  right_antipode : LinearMap.mul' k (Classical k) ∘ₗ antipode.lTensor (Classical k) ∘ₗ
      comul.toLinearMap = Algebra.linearMap k (Classical k) ∘ₗ counit.toLinearMap
  comul_ι (x : Sl3 k) : comul (UniversalEnvelopingAlgebra.ι k x) =
    UniversalEnvelopingAlgebra.ι k x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] UniversalEnvelopingAlgebra.ι k x
  counit_ι (x : Sl3 k) : counit (UniversalEnvelopingAlgebra.ι k x) = 0
  antipode_ι (x : Sl3 k) : antipode (UniversalEnvelopingAlgebra.ι k x) =
    -UniversalEnvelopingAlgebra.ι k x

abbrev ClassicalHopf.toHopfAlgebra (c : ClassicalHopf k) : HopfAlgebra k (Classical k) where
  toBialgebra := Bialgebra.ofAlgHom c.comul c.counit c.coassoc c.left_counit c.right_counit
  antipode := c.antipode
  mul_antipode_rTensor_comul := c.left_antipode
  mul_antipode_lTensor_comul := c.right_antipode

/-- Intertwining on the whole algebra, using scalar evaluation and the tensor
map induced by the algebra isomorphism on both factors. -/
def PreservesHopf (e : LevelOne k ≃ₐ[k] Classical k) (c : ClassicalHopf k)
    (d : Coproduct.TruncatedData k 1) (s : Hopf.TruncatedData k 1 d) : Prop :=
  ∃ t : (LevelOne k ⊗[Truncations.A k 1] LevelOne k) ≃+*
      (Classical k ⊗[k] Classical k),
    (∀ x y : LevelOne k, t (x ⊗ₜ[Truncations.A k 1] y) = e x ⊗ₜ[k] e y) ∧
    ∀ x : LevelOne k,
      t (d.comul x) = c.comul (e x) ∧
      coefficientEquiv k (d.counit x) = c.counit (e x) ∧
      e (Hopf.antipodeLinear s.antipode x) = c.antipode (e x)

end Comparison

def Specialization : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ e : LevelOne k ≃ₐ[k] Classical k, GeneratorImages e ∧ PBWComparison e ∧
      ∃ c : ClassicalHopf k, ∀ (d : Coproduct.TruncatedData k 1) (s : Hopf.TruncatedData k 1 d),
        PreservesHopf e c d s

end Specs.LieNotes.Quantum.MatrixSpecialization
