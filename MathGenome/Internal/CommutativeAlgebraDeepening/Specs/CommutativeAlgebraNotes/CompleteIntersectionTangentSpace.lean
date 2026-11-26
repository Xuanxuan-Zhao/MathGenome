import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FlatSquareZeroLifts
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Group.TransferInstance

noncomputable section

open scoped BigOperators TensorProduct

namespace Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

open _root_.CommutativeAlgebraNotes
open SquareZeroLift

universe u z

variable {k : Type u} [Field k] {n s : ℕ}

abbrev P (k : Type u) [Field k] (n : ℕ) := MvPolynomial (Fin n) k

def J (f : Fin s → P k n) : Ideal (P k n) := Ideal.span (Set.range f)

abbrev B (f : Fin s → P k n) := P k n ⧸ J f

abbrev q (f : Fin s → P k n) : P k n →ₐ[k] B f := Ideal.Quotient.mkₐ k (J f)

/-- The Jacobian evaluated in the complete intersection. -/
def jacobian (f : Fin s → P k n) : (Fin n → B f) →ₗ[B f] (Fin s → B f) where
  toFun a i := ∑ j, q f (MvPolynomial.pderiv j (f i)) * a j
  map_add' a b := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    ext i
    change (∑ j, q f (MvPolynomial.pderiv j (f i)) * (c * a j)) =
      c * ∑ j, q f (MvPolynomial.pderiv j (f i)) * a j
    simp [Finset.mul_sum, mul_left_comm]

abbrev JacobianCokernel (f : Fin s → P k n) :=
  (Fin s → B f) ⧸ (jacobian f).range

def generators (f : Fin s → P k n) : Algebra.Generators k (B f) (Fin n) :=
  Algebra.Generators.ofAlgHom (q f) (show Function.Surjective (q f) from
    Ideal.Quotient.mk_surjective)

theorem generators_ker (f : Fin s → P k n) : (generators f).ker = J f := by
  exact (Algebra.Generators.ker_ofAlgHom (q f) _).trans Ideal.mk_ker

/-- The images of the specified equations in the conormal module. -/
def relationClass (f : Fin s → P k n) (i : Fin s) :
    (generators f).toExtension.Cotangent :=
  Algebra.Extension.Cotangent.mk ⟨f i, by
    change f i ∈ (generators f).ker
    rw [generators_ker]
    exact Ideal.subset_span (Set.mem_range_self i)⟩

def ConormalBasis : Prop :=
  ∀ {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n),
    RingTheory.Sequence.IsRegular (P k n) (List.ofFn f) →
    ∃ b : Module.Basis (Fin s) (B f) (generators f).toExtension.Cotangent,
      ∀ i, b i = relationClass f i

def JacobianIntertwines : Prop :=
  ∀ {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n)
    (h : (generators f).toExtension.CotangentSpace →ₗ[B f] B f) (i : Fin s),
    h ((generators f).toExtension.cotangentComplex (relationClass f i)) =
      jacobian f (fun j => h ((generators f).cotangentSpaceBasis j)) i

abbrev dual (k : Type u) [Field k] := LocalArtinAlgebra.dualModel k

/-- The constant family over the dual numbers, with its identity marking at the
closed fibre. -/
def trivial (k : Type u) [Field k] (C : Type u) [CommRing C] [Algebra k C] :
    MarkedDeformation.{u,u,u,z} (dual k) C := by
  let R := dual k
  let h : k ⊗[R] R ≃ₐ[k] k := Algebra.TensorProduct.rid R k k
  exact {
    carrier := ULift.{z} (R ⊗[k] C)
    marking := (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) ULift.algEquiv).trans <|
      (Algebra.TensorProduct.assoc k R k k R C).symm.trans
      ((Algebra.TensorProduct.congr h (AlgEquiv.refl : C ≃ₐ[k] C)).trans
      (Algebra.TensorProduct.lid k C)) }

abbrev dualResidue (k : Type u) [Field k] : LocalArtinAlgebra.Hom (dual k) (LocalArtinAlgebra.fieldModel k) :=
  ⟨(dual k).residue, (dual k).localResidue⟩

theorem dualResidue_squareZero (k : Type u) [Field k] :
    RingHom.ker ((dualResidue k : (dual k) →ₐ[k] k).toRingHom) ^ 2 = ⊥ :=
  TrivSqZeroExt.kerIdeal_sq k k

abbrev dualExtension (k : Type u) [Field k] : BaseExtension (dual k) k :=
  FlatSquareZeroLifts.extension (dualResidue k) (dual k).residue_surjective (dualResidue_squareZero k)

def presentation (f : Fin s → P k n) : Presentation (dualExtension k) (B f) (Fin n) where
  map := (q f).toRingHom.comp (MvPolynomial.map (dualExtension k).hom)
  surjective := Ideal.Quotient.mk_surjective.comp
    (MvPolynomial.map_surjective _ (dualExtension k).surjective)
  over a := by
    change q f (MvPolynomial.map (dualExtension k).hom (MvPolynomial.C a)) = _
    rw [MvPolynomial.map_C]
    exact (q f).commutes _

/-- The reduction map specified by a marking. -/
def reduction {C : Type u} [CommRing C] [Algebra k C]
    (D : MarkedDeformation.{u,u,u,z} (dual k) C) : D →+* C :=
  D.marking.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

/-- The unit vector of the kernel determined by the distinguished dual number ε. -/
def epsilon (k : Type u) [Field k] : (dualExtension k).I :=
  ⟨TrivSqZeroExt.inr 1, rfl⟩

abbrev Coeff (C : Type u) [CommRing C] [Algebra k C] :=
  FlatSquareZeroLifts.Coefficients (dualExtension k) C

abbrev c (C : Type u) [CommRing C] [Algebra k C] :=
  FlatSquareZeroLifts.coefficientMap (B := C) (dualExtension k)

theorem barMap_eq (f : Fin s → P k n) (x : (presentation f).Bar) :
    (presentation f).barMap x = q f ((presentation f).barPolynomialEquiv x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (presentation f).barMap ((presentation f).reduce y) = _
  rw [Presentation.barMap_reduce, Presentation.barPolynomialEquiv_reduce]
  rfl

def reducedRelation (f : Fin s → P k n) (i : Fin s) :
    (presentation f).BarConormal :=
  Algebra.Extension.Cotangent.mk ⟨(presentation f).barPolynomialEquiv.symm (f i), by
    apply RingHom.mem_ker.mpr
    change (presentation f).barMap _ = _
    rw [barMap_eq, AlgEquiv.apply_symm_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))⟩

abbrev LiftClasses (C : Type u) [CommRing C] [Algebra k C] :=
  Lift.Classes.{u,u,u,u,u} (c (k := k) C)

abbrev restriction (f : Fin s → P k n) :=
  Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor.conormalRestriction
    (presentation f) (Coeff (k := k) (B f))

abbrev TangentModule (f : Fin s → P k n) :=
  Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor.T1 (presentation f) (Coeff (k := k) (B f))

def Corresponds {C : Type u} [CommRing C] [Algebra k C]
    (D : MarkedDeformation.{u,u,u,z} (dual k) C)
    (L : Lift.{u,u,u,u,u} (dualExtension k) (c (k := k) C)) : Prop :=
  ∃ j : D ≃ₐ[dual k] L.Ring, ∀ d, L.map (j d) = reduction D d

private def evaluates
    {R A C N : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup N] [Module C N] {e : BaseExtension R A}
    (p : Presentation e C (Fin n)) (d : (Fin n → C) →ₗ[C] (Fin s → C))
    (r : Fin s → p.BarConormal) (U : N ≃ₗ[C] C)
    (E : Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor.T1 p N ≃ₗ[C]
      ((Fin s → C) ⧸ d.range)) : Prop :=
  ∀ g : p.BarConormal →ₗ[C] N,
    E ((Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor.conormalRestriction p N).range.mkQ g) =
      d.range.mkQ (fun i => U (g (r i)))

/-- Evaluation on the equations, with coefficients measured in units of ε. -/
def EvaluatesRelations (f : Fin s → P k n) (U : Coeff (k := k) (B f) ≃ₗ[B f] B f)
    (E : TangentModule f ≃ₗ[B f] JacobianCokernel f) : Prop :=
  U (c (k := k) (B f) (epsilon k)) = 1 ∧
    evaluates (presentation f) (jacobian f) (reducedRelation f) U E

def CokernelIdentification : Prop :=
  ∀ {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n),
    RingTheory.Sequence.IsRegular (P k n) (List.ofFn f) →
    ∃ (U : Coeff (k := k) (B f) ≃ₗ[B f] B f) (E : TangentModule f ≃ₗ[B f] JacobianCokernel f),
      EvaluatesRelations f U E

abbrev DeformationClasses (f : Fin s → P k n) :=
  MarkedDeformation.Classes.{u,u,u,z} (dual k) (B f)

open Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor (ActsByReduction liftClass)

set_option maxHeartbeats 1500000 in
/-- The pointed Jacobian identification and the vector-space structure induced
by the action on lifts. -/
def TangentSpace : Prop :=
  ∀ {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n),
    RingTheory.Sequence.IsRegular (P k n) (List.ofFn f) →
    ∃ (F : DeformationClasses.{u,z} f ≃ LiftClasses (k := k) (B f))
      (a : AddTorsor (TangentModule f) (LiftClasses (k := k) (B f)))
      (U : Coeff (k := k) (B f) ≃ₗ[B f] B f)
      (E : TangentModule f ≃ₗ[B f] JacobianCokernel f)
      (G : DeformationClasses.{u,z} f ≃ JacobianCokernel f),
      (∀ D L, Corresponds D L → F (MarkedDeformation.classModel D) = liftClass L) ∧
      ActsByReduction (presentation f) a.toAddAction.toVAdd ∧
      EvaluatesRelations f U E ∧
      (∀ X, G X = E (a.vsub (F X) (F (MarkedDeformation.classModel (trivial.{u,z} k (B f)))))) ∧
      (letI := G.addCommGroup
       letI := G.addEquiv.module k
       ∃ H : DeformationClasses.{u,z} f ≃ₗ[k] JacobianCokernel f,
         H.toEquiv = G ∧ H (MarkedDeformation.classModel (trivial.{u,z} k (B f))) = 0)

end Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
