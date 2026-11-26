import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.HopfAlgebras
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.MvPolynomial

open CategoryTheory Opposite AlgebraicGeometry Coalgebra HopfAlgebra WithConv
open scoped TensorProduct Ring

universe u

namespace LinearAlgebraicGroups
namespace Specs
namespace StandardGroups

noncomputable section

variable (k : Type u) [Field k]

/-- The generic matrix over the polynomial algebra on its entries. -/
def genericMatrix (ι : Type u) : Matrix ι ι (MvPolynomial (ι × ι) k) :=
  fun i j => MvPolynomial.X (i, j)

section Matrices

variable (ι : Type u) [Fintype ι] [DecidableEq ι]

def genericDeterminant : MvPolynomial (ι × ι) k := (genericMatrix k ι).det

abbrev GLCoordinates := Localization.Away (genericDeterminant k ι)

/-- The entries of the universal invertible matrix in the localized coordinate algebra. -/
def universalMatrix : Matrix ι ι (GLCoordinates k ι) :=
  (algebraMap (MvPolynomial (ι × ι) k) (GLCoordinates k ι)).mapMatrix (genericMatrix k ι)

def UniversalMatrixType :=
  ∀ (k : Type u) [Field k] (ι : Type u) [Fintype ι] [DecidableEq ι], Matrix ι ι (GLCoordinates k ι)

def determinantOneIdeal : Ideal (GLCoordinates k ι) :=
  Ideal.span {(universalMatrix k ι).det - 1}

abbrev SLCoordinates := GLCoordinates k ι ⧸ determinantOneIdeal k ι

end Matrices

/-- The standard point functors use the ordinary maps on the test algebras. -/
def additivePoints : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Multiplicative R)
  map a := GrpCat.ofHom a.hom.toRingHom.toAddMonoidHom.toMultiplicative
  map_id _ := by apply GrpCat.ext; intro x; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; rfl

def multiplicativePoints : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of Rˣ
  map a := GrpCat.ofHom (Units.map a.hom.toMonoidHom)
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

def generalLinearPoints (ι : Type u) [Fintype ι] [DecidableEq ι] :
    TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.GeneralLinearGroup ι R)
  map a := GrpCat.ofHom (Matrix.GeneralLinearGroup.map a.hom.toRingHom)
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

def specialLinearPoints (ι : Type u) [Fintype ι] [DecidableEq ι] :
    TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup ι R)
  map a := GrpCat.ofHom (Matrix.SpecialLinearGroup.map a.hom.toRingHom)
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- Spectrum of a finite-type Hopf algebra, in the common category of affine algebraic groups. -/
abbrev spectrum (A : Type u) [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] : AffineAlgebraicGroup k :=
  (finiteTypeHopfSpec k).obj (op ⟨CommHopfAlgCat.of k A, (inferInstance : Algebra.FiniteType k A)⟩)

variable {k}

/-- A specified coordinate evaluation describes the group points naturally in the test algebra. -/
def Represents (A : Type u) [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] (F : TestAlgebra k ⥤ GrpCat.{u})
    (eval : ∀ R : TestAlgebra k, (A →ₐ[k] R) → F.obj R → Prop) : Prop :=
  ∃ e : convolutionPoints (CommHopfAlgCat.of k A) ≅
      (groupPointsFunctor k).obj (spectrum k A).val,
    (∀ (R : TestAlgebra k) (f : A →ₐ[k] R),
      (e.hom.app R (toConv f) : Points (spectrum k A).val.X R).left =
        Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
    ∃ c : (groupPointsFunctor k).obj (spectrum k A).val ≅ F,
      ∀ (R : TestAlgebra k) (f : A →ₐ[k] R),
        eval R f (c.hom.app R (e.hom.app R (toConv f)))

open Algebra.TensorProduct in
/-- The three structure maps and Hopf identities with the coordinate algebra fixed. -/
structure HopfOperations (k A : Type u) [Field k] [CommRing A] [Algebra k A] where
  delta : A →ₐ[k] A ⊗[k] A
  epsilon : A →ₐ[k] k
  inverse : A →ₐ[k] A
  coassoc : (Algebra.TensorProduct.assoc k k k A A A).toAlgHom.comp
      ((map delta (.id k A)).comp delta) = (map (.id k A) delta).comp delta
  counitLeft : (map epsilon (.id k A)).comp delta = (Algebra.TensorProduct.lid k A).symm
  counitRight : (map (.id k A) epsilon).comp delta = (Algebra.TensorProduct.rid k k A).symm
  inverseLeft : (lift inverse (.id k A) (fun _ _ => Commute.all _ _)).comp delta =
    (Algebra.ofId k A).comp epsilon
  inverseRight : (lift (.id k A) inverse (fun _ _ => Commute.all _ _)).comp delta =
    (Algebra.ofId k A).comp epsilon

@[instance_reducible]
def HopfOperations.hopf {A : Type u} [CommRing A] [Algebra k A]
    (h : HopfOperations k A) : HopfAlgebra k A :=
  letI := Bialgebra.ofAlgHom h.delta h.epsilon h.coassoc h.counitLeft h.counitRight
  HopfAlgebra.ofAlgHom h.inverse h.inverseLeft h.inverseRight

instance : Algebra.FiniteType k (LaurentPolynomial k) :=
  inferInstanceAs (Algebra.FiniteType k (AddMonoidAlgebra k ℤ))

def AdditiveGroup : Prop :=
  ∀ (k : Type u) [Field k], ∃ h : HopfOperations k (Polynomial k),
    letI := h.hopf
    h.delta (Polynomial.X : Polynomial k) =
      Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X ∧
    h.epsilon (Polynomial.X : Polynomial k) = 0 ∧
    h.inverse (Polynomial.X : Polynomial k) = -Polynomial.X ∧
    Represents (Polynomial k) (additivePoints k)
      (fun _ f a => Multiplicative.toAdd a = f Polynomial.X)

def MultiplicativeGroup : Prop :=
  ∀ (k : Type u) [Field k], ∃ h : HopfOperations k (LaurentPolynomial k),
    letI := h.hopf
    h.delta (LaurentPolynomial.T 1 : LaurentPolynomial k) =
      LaurentPolynomial.T 1 ⊗ₜ[k] LaurentPolynomial.T 1 ∧
    h.epsilon (LaurentPolynomial.T 1 : LaurentPolynomial k) = 1 ∧
    h.inverse (LaurentPolynomial.T 1 : LaurentPolynomial k) = LaurentPolynomial.T (-1) ∧
    Represents (LaurentPolynomial k) (multiplicativePoints k)
      (fun _ f a => a.val = f (LaurentPolynomial.T 1))

def GeneralLinearGroup : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι],
    ∃ h : HopfOperations k (GLCoordinates k ι),
      letI := h.hopf
      let X := universalMatrix k ι
      let d := X.det
      (∀ i j, h.delta (X i j) = ∑ l, X i l ⊗ₜ[k] X l j) ∧
      (∀ i j, h.epsilon (X i j) = if i = j then 1 else 0) ∧
      (∀ i j, h.inverse (X i j) = d⁻¹ʳ * X.adjugate i j) ∧
      h.delta d = d ⊗ₜ[k] d ∧
      h.epsilon d = 1 ∧
      h.inverse d = d⁻¹ʳ ∧
      Represents (GLCoordinates k ι) (generalLinearPoints k ι)
        (fun _ f M => M.val = f.mapMatrix X)

def SpecialLinearGroup : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι],
    ∃ (gl : HopfOperations k (GLCoordinates k ι)) (sl : HopfOperations k (SLCoordinates k ι)),
      let X := universalMatrix k ι
      let d := X.det
      let q := Ideal.Quotient.mkₐ k (determinantOneIdeal k ι)
      letI := gl.hopf
      Ideal.IsHopfIdeal k (determinantOneIdeal k ι) ∧
      gl.delta (d - 1) = (d - 1) ⊗ₜ[k] d + 1 ⊗ₜ[k] (d - 1) ∧
      gl.epsilon (d - 1) = 0 ∧
      gl.inverse (d - 1) = -d⁻¹ʳ * (d - 1) ∧
      (Algebra.TensorProduct.map q q).comp gl.delta = sl.delta.comp q ∧
      gl.epsilon = sl.epsilon.comp q ∧
      q.comp gl.inverse = sl.inverse.comp q ∧
      (letI := sl.hopf
       Represents (SLCoordinates k ι) (specialLinearPoints k ι)
        (fun R f M => (show Matrix.SpecialLinearGroup ι R from M).val = (f.comp q).mapMatrix X))

variable (k)

/-- The Laurent monomial with exponent vector `m` is `single m 1`. -/
abbrev LaurentPowerCoordinates (ι : Type u) := AddMonoidAlgebra k (ι → ℤ)

def MultiplicativePowerGroupType :=
  ∀ (k ι : Type u) [Field k] [Fintype ι], AffineAlgebraicGroup k

def multiplicativePowerGroup (k ι : Type u) [Field k] [Fintype ι] : AffineAlgebraicGroup k :=
  spectrum k (LaurentPowerCoordinates k ι)

def laurentVariable (ι : Type u) [DecidableEq ι] (i : ι) : LaurentPowerCoordinates k ι :=
  AddMonoidAlgebra.single (Pi.single i 1) 1

def additivePowerPoints (ι : Type u) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (ι → Multiplicative R)
  map a := GrpCat.ofHom (MonoidHom.pi fun i =>
    a.hom.toRingHom.toAddMonoidHom.toMultiplicative.comp (Pi.evalMonoidHom _ i))
  map_id _ := by apply GrpCat.ext; intro f; rfl
  map_comp _ _ := by apply GrpCat.ext; intro f; rfl

def multiplicativePowerPoints (ι : Type u) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (ι → Rˣ)
  map a := GrpCat.ofHom (MonoidHom.pi fun i =>
    (Units.map a.hom.toMonoidHom).comp (Pi.evalMonoidHom _ i))
  map_id _ := by apply GrpCat.ext; intro f; rfl
  map_comp _ _ := by apply GrpCat.ext; intro f; rfl

def AdditivePower : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι],
    ∃ h : HopfOperations k (MvPolynomial ι k),
      letI := h.hopf
      (∀ i, h.delta (MvPolynomial.X i) = MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i) ∧
      (∀ i, h.epsilon (MvPolynomial.X i) = 0) ∧
      (∀ i, h.inverse (MvPolynomial.X i) = -MvPolynomial.X i) ∧
      Represents (MvPolynomial ι k) (additivePowerPoints k ι)
        (fun R f a => ∀ i, Multiplicative.toAdd ((show ι → Multiplicative R from a) i) =
          f (MvPolynomial.X i))

def MultiplicativePower : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι],
    (∀ i, Coalgebra.comul (R := k) (laurentVariable k ι i) =
      laurentVariable k ι i ⊗ₜ[k] laurentVariable k ι i) ∧
    (∀ i, Coalgebra.counit (R := k) (laurentVariable k ι i) = 1) ∧
    (∀ i, antipode k (laurentVariable k ι i) =
      AddMonoidAlgebra.single (-Pi.single i (1 : ℤ)) 1) ∧
    Represents (LaurentPowerCoordinates k ι) (multiplicativePowerPoints k ι)
      (fun R f a => ∀ i, ((show ι → Rˣ from a) i).val = f (laurentVariable k ι i))

/-- Tensor decomposition with the two factors' displayed generators. -/
def TensorPowerCoordinates : Prop :=
  (∀ (k ι : Type u) [Field k] [IsEmpty ι],
    Nonempty (MvPolynomial ι k ≃ₐ[k] k) ∧ Nonempty (LaurentPowerCoordinates k ι ≃ₐ[k] k)) ∧
  (∀ (k ι : Type u) [Field k] [Unique ι] [DecidableEq ι],
    ∃ (a : MvPolynomial ι k ≃ₐ[k] Polynomial k)
      (m : LaurentPowerCoordinates k ι ≃ₐ[k] LaurentPolynomial k),
      (∀ i, a (MvPolynomial.X i) = Polynomial.X) ∧
      (∀ i, m (laurentVariable k ι i) = LaurentPolynomial.T 1)) ∧
  (∀ (k ι κ : Type u) [Field k] [DecidableEq ι] [DecidableEq κ],
    ∃ (a : (MvPolynomial ι k ⊗[k] MvPolynomial κ k) ≃ₐ[k] MvPolynomial (ι ⊕ κ) k)
      (m : (LaurentPowerCoordinates k ι ⊗[k] LaurentPowerCoordinates k κ) ≃ₐ[k]
        LaurentPowerCoordinates k (ι ⊕ κ)),
      (∀ i, a (MvPolynomial.X i ⊗ₜ[k] 1) = MvPolynomial.X (Sum.inl i)) ∧
      (∀ j, a (1 ⊗ₜ[k] MvPolynomial.X j) = MvPolynomial.X (Sum.inr j)) ∧
      (∀ i, m (laurentVariable k ι i ⊗ₜ[k] 1) = laurentVariable k (ι ⊕ κ) (Sum.inl i)) ∧
      (∀ j, m (1 ⊗ₜ[k] laurentVariable k κ j) = laurentVariable k (ι ⊕ κ) (Sum.inr j)))

/-- The coordinate identifications respect the Hopf structures on the tensor products. -/
def TensorPowerHopf : Prop :=
  ∀ (k ι κ : Type u) [Field k],
    ∃ (l : HopfOperations k (MvPolynomial ι k))
      (r : HopfOperations k (MvPolynomial κ k))
      (s : HopfOperations k (MvPolynomial (ι ⊕ κ) k)),
      (∀ i, l.delta (MvPolynomial.X i) = MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i) ∧
      (∀ j, r.delta (MvPolynomial.X j) = MvPolynomial.X j ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X j) ∧
      (∀ h, s.delta (MvPolynomial.X h) = MvPolynomial.X h ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X h) ∧
      (letI : CoalgebraStruct k (MvPolynomial ι k) := l.hopf.toBialgebra.toCoalgebra.toCoalgebraStruct
       letI : CoalgebraStruct k (MvPolynomial κ k) := r.hopf.toBialgebra.toCoalgebra.toCoalgebraStruct
       letI : CoalgebraStruct k (MvPolynomial (ι ⊕ κ) k) :=
         s.hopf.toBialgebra.toCoalgebra.toCoalgebraStruct
       ∃ a : (MvPolynomial ι k ⊗[k] MvPolynomial κ k) ≃ₐc[k] MvPolynomial (ι ⊕ κ) k,
         a.toAlgEquiv = MvPolynomial.tensorEquivSum k ι κ k) ∧
      (∃ m : (LaurentPowerCoordinates k ι ⊗[k] LaurentPowerCoordinates k κ) ≃ₐc[k]
          LaurentPowerCoordinates k (ι ⊕ κ),
        ∀ d : ι ⊕ κ → ℤ, m.symm (AddMonoidAlgebra.single d 1) =
          AddMonoidAlgebra.single (fun i => d (Sum.inl i)) 1 ⊗ₜ[k]
            AddMonoidAlgebra.single (fun j => d (Sum.inr j)) 1)

end
end StandardGroups
end Specs
end LinearAlgebraicGroups
