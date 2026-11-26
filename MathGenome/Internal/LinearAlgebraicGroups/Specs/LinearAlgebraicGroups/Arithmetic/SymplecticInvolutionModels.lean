import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionHermitianCocharacters
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped WithZero TensorProduct Matrix
open ValuativeRel

universe u v z w

namespace LinearAlgebraicGroups.Specs.SymplecticInvolutionModels

/-- A first-kind anti-automorphism of a central division algebra is an algebra
equivalence to the opposite algebra over the original center. -/
abbrev AntiAutomorphism (F : Type u) (B : Type v) [Field F] [Ring B] [Algebra F B] :=
  B ≃ₐ[F] Bᵐᵒᵖ

/-- The possible division degrees at a nonarchimedean local field for a
division factor with a center-preserving anti-automorphism. -/
def LocalDivisionDegreeBound : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B],
    _root_.Specs.RM03.CSA.isCentralSimple F B →
    AntiAutomorphism F B → _root_.Specs.RM03.CSA.degree F B ≤ 2

/-- An algebra presentation over a division ring transports a first-kind
anti-automorphism to the division factor. -/
def DivisionFactorAntiAutomorphism : Prop :=
  ∀ {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A]
    {B : Type w} [DivisionRing B] [Algebra F B] {r : ℕ}, 0 < r →
    _root_.Specs.RM03.CSA.isCentralSimple F A →
    (A ≃ₐ[F] Matrix (Fin r) (Fin r) B) →
    AntiAutomorphism F A → Nonempty (AntiAutomorphism F B)

/-- The field or degree-two division alternative holds in every positive-size
matrix presentation of a first-kind algebra with involution at a finite place. -/
def NonarchimedeanDivisionFactor : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {A : Type v} [Ring A] [Algebra F A]
    {B : Type w} [DivisionRing B] [Algebra F B] {r : ℕ}, 0 < r →
    _root_.Specs.RM03.CSA.isCentralSimple F A →
    _root_.Specs.RM03.CSA.isCentralSimple F B →
    (A ≃ₐ[F] Matrix (Fin r) (Fin r) B) → AntiAutomorphism F A →
    Nonempty (B ≃ₐ[F] F) ∨ _root_.Specs.RM03.CSA.degree F B = 2

def DegreeOneDivision : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B],
    _root_.Specs.RM03.CSA.isCentralSimple F B →
    _root_.Specs.RM03.CSA.degree F B = 1 → Nonempty (B ≃ₐ[F] F)

def AlgebraicallyClosedDivision : Prop :=
  ∀ {F : Type u} [Field F] [IsAlgClosed F] {B : Type v} [DivisionRing B] [Algebra F B],
    _root_.Specs.RM03.CSA.isCentralSimple F B → Nonempty (B ≃ₐ[F] F)

def RealDivision : Prop :=
  ∀ {B : Type v} [DivisionRing B] [Algebra ℝ B],
    _root_.Specs.RM03.CSA.isCentralSimple ℝ B →
      Nonempty (B ≃ₐ[ℝ] ℝ) ∨ Nonempty (B ≃ₐ[ℝ] Quaternion ℝ)

def NonarchimedeanPresentations : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {A : Type v} [Ring A] [Algebra F A],
    _root_.Specs.RM03.CSA.isCentralSimple F A → AntiAutomorphism F A →
    ∃ (B : Type v) (_ : DivisionRing B) (_ : Algebra F B) (r : ℕ),
      _root_.Specs.RM03.CSA.isCentralSimple F B ∧ 0 < r ∧
      Nonempty (A ≃ₐ[F] Matrix (Fin r) (Fin r) B) ∧
      (Nonempty (B ≃ₐ[F] F) ∨ _root_.Specs.RM03.CSA.degree F B = 2)

def ArchimedeanPresentations : Prop :=
  (∀ {A : Type v} [Ring A] [Algebra ℝ A], _root_.Specs.RM03.CSA.isCentralSimple ℝ A →
    ∃ r : ℕ, 0 < r ∧ (Nonempty (A ≃ₐ[ℝ] Matrix (Fin r) (Fin r) ℝ) ∨
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin r) (Fin r) (Quaternion ℝ)))) ∧
  (∀ {A : Type v} [Ring A] [Algebra ℂ A], _root_.Specs.RM03.CSA.isCentralSimple ℂ A →
    ∃ r : ℕ, 0 < r ∧ Nonempty (A ≃ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ))

/-- Right Hermitian pairings are additive and right-linear in the second
argument. The Hermitian identity imposes the corresponding left rule. -/
structure HermitianPairing {F : Type u} [Field F] {B : Type v} [Ring B] [Algebra F B]
    (s : AntiAutomorphism F B) (V : Type*) [AddCommGroup V] [Module Bᵐᵒᵖ V] where
  value : V → V → B
  add_right : ∀ x y z, value x (y + z) = value x y + value x z
  smul_right : ∀ x y (a : B), value x (MulOpposite.op a • y) = value x y * a
  hermitian : ∀ x y, value y x = MulOpposite.unop (s (value x y))
  nondegenerate : ∀ x, x ≠ 0 → ∃ y, value x y ≠ 0
  central_norm : ∀ x, ∃ b : F, value x x = algebraMap F B b

/-- Surjectivity of the trace operator gives a hyperbolic partner for any
nonzero isotropic vector. For canonical quaternion conjugation the trace
operator is the reduced trace followed by the scalar embedding. -/
def HyperbolicPartner : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
    (s : AntiAutomorphism F B),
    (∀ b : F, ∃ a : B, a + MulOpposite.unop (s a) = algebraMap F B b) →
    ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] (h : HermitianPairing s V)
      (e : V), e ≠ 0 → h.value e e = 0 →
      ∃ f : V, h.value e f = 1 ∧ h.value f e = 1 ∧ h.value f f = 0

open LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)

/-- The canonical symplectic conjugation on a quaternion division algebra.
Here degree two, rather than a presentation with signed generators, includes
quaternion algebras in characteristic two. -/
noncomputable def quaternionConjugate {F : Type u} [Field F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (x : B) : B :=
  algebraMap F B (reducedTrace hB x) - x

def QuaternionConjugation : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∃ s : AntiAutomorphism F B,
      (∀ x, MulOpposite.unop (s x) = quaternionConjugate hB x) ∧
      (∀ x, MulOpposite.unop (s (MulOpposite.unop (s x))) = x) ∧
      (∀ (L : Type w) [Field L] [Algebra F L]
        (e : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (x : B),
        e (1 ⊗ₜ[F] MulOpposite.unop (s x)) = (e (1 ⊗ₜ[F] x)).adjugate) ∧
      Function.Surjective (reducedTrace hB)

/-- The alternating form used on each split quaternion block. -/
def alternatingPlane (F : Type*) [Field F] : Matrix (Fin 2) (Fin 2) F :=
  !![0, 1; -1, 0]

def QuaternionAlternatingPlane : Prop :=
  ∀ (F : Type u) [Field F], let J := alternatingPlane F
    (∀ X : Matrix (Fin 2) (Fin 2) F, X.adjugate = (-J) * X.transpose * J) ∧
    ∀ X : Matrix (Fin 2) (Fin 2) F,
      (J * X).transpose = -(J * X) → (∀ i, (J * X) i i = 0) →
      ∃ a : F, X = Matrix.scalar (Fin 2) a

def QuaternionHyperbolicPartner : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
      (∀ x, MulOpposite.unop (s x) = quaternionConjugate hB x) →
      ∀ {V : Type z} [AddCommGroup V] [Module Bᵐᵒᵖ V] (h : HermitianPairing s V)
        (e : V), e ≠ 0 → h.value e e = 0 →
        ∃ f : V, h.value e f = 1 ∧ h.value f e = 1 ∧ h.value f f = 0

section TypeC

open AlgebraicGeometry CategoryTheory Opposite
open TypeCSplitRecognition (MatrixTwisting sliceTest HasGeometricCartanTypeC)
open SymplecticDatumTorusAndBorel (HyperbolicIndex)
open SymplecticMatrixStructure (PointGroup symplecticPoints)
open GeometricRadicals (IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Arithmetic.SymplecticIsometryDescent
  (AdjointPresentation PointsOf SplitComparison Model overBase)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {n : ℕ} {G H : AffineAlgebraicGroup k}
variable {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))}
variable {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}

/-- Local lifts and the induced action on symplectic isometries for the
same quotient and algebra action as the recognized twisting cocycle. -/
structure TwistingActions (t : MatrixTwisting n G H c f) where
  lifts : ∀ (R : TestAlgebra k) (a : (PointsOf t.quotient.val).obj R),
    ∃ (S : TestAlgebra k) (b : R ⟶ S) (g : (PointsOf H.val).obj S),
      b.hom.toRingHom.FaithfullyFlat ∧ b.hom.toRingHom.FinitePresentation ∧
        ((groupPointsFunctor k).map t.projection).app S g = (PointsOf t.quotient.val).map b a
  groupAction : ∀ R : TestAlgebra k, (PointsOf t.quotient.val).obj R →*
    MulAut (PointGroup (HyperbolicIndex.{u} (n + 1)) R)
  onMatrix : ∀ (R : TestAlgebra k) (a : (PointsOf t.quotient.val).obj R)
    (g : PointGroup (HyperbolicIndex.{u} (n + 1)) R),
    (groupAction R a g).val = t.action R a g.val

def TwistingActions.presentation {t : MatrixTwisting n G H c f} (a : TwistingActions t) :
    AdjointPresentation k (HyperbolicIndex.{u} (n + 1)) where
  splitGroup := H
  splitPoints := c
  centre := t.centre
  centre_spec := t.isCentre
  centre_scalar := t.scalar
  quotient := t.quotient
  projection := t.projection
  kernel := t.kernel
  represents := t.represents
  localLift := a.lifts
  onAlgebra := t.action
  onGroup := a.groupAction
  preservesAdjoint := t.preservesAdjoint
  algebraNatural := t.naturality
  onLift := t.onLift
  groupMatrix := a.onMatrix

/-- Descent of the algebra with involution and of its isometries using the
cocycle of the specified finite Galois trivialization. -/
structure DescendedTypeC (t : MatrixTwisting n G H c f) where
  actions : TwistingActions t
  splitComparison : SplitComparison actions.presentation G t.cocycle
  comparisonFormula : ∀ (R : TestAlgebra K) (x : (PointsOf G.val).obj (overBase k K R)),
    splitComparison.iso.hom.app R x =
      c.hom.app (overBase k K R) (t.comparison.inv.app (op (sliceTest (k := k) R)) x)
  model : Model actions.presentation G t.cocycle splitComparison

/-- Every simply connected form of absolute Cartan type C has the first-kind
symplectic involution model on a central simple algebra of degree twice its rank.
The represented isometry equations and the equivariant split comparison are
those of the fixed algebra for the actual adjoint cocycle. -/
def GlobalTypeCModel : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (n : ℕ) (G : AffineAlgebraicGroup k), IsSemisimple G →
    GeometricallySimplyConnected G → HasGeometricCartanTypeC n G →
    ∃ (H : AffineAlgebraicGroup k)
      (c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1)))
      (L : FiniteGaloisIntermediateField k S)
      (f : (groupBaseChange k L).obj H.val ≅ (groupBaseChange k L).obj G.val)
      (t : MatrixTwisting n G H c f) (d : DescendedTypeC t),
      _root_.Specs.RM03.CSA.degree k d.model.fixed.action.fixedSubalgebra = 2 * (n + 1)

end TypeC

section LocalModels

open AlgebraicGeometry CategoryTheory
open Arithmetic.SymplecticIsometryDescent (isometryPoints)

namespace DivisionForms

open SymplecticDivisionForms (HermitianLaws dagger intoTensor tensorMap)
open SymplecticDatumTorusAndBorel (HyperbolicIndex)
open SymplecticMatrixStructure (symplecticPoints)
open Arithmetic.SymplecticIsometryDescent (Involution)
open _root_.LinearAlgebraicGroups.QuaternionHermitianCocharacters
  (pairing multiplicativePoints IsNoncentral)

variable {F A B : Type u} [Field F] [Ring A] [Algebra F A]
variable [DivisionRing B] [Algebra F B]

/-- The algebra with involution in the form used for the local matrix comparison. -/
def toDivisionInvolution (s : Involution F A) : SymplecticDivisionForms.Involution F A where
  anti :=
    { toFun := fun a => MulOpposite.op (s.toLinearMap a)
      invFun := fun a => s.toLinearMap (MulOpposite.unop a)
      left_inv := s.involutive
      right_inv := fun a => MulOpposite.unop_injective (s.involutive (MulOpposite.unop a))
      map_mul' := fun a b => congrArg MulOpposite.op (s.map_mul a b)
      map_add' := fun a b => congrArg MulOpposite.op (s.toLinearMap.map_add a b)
      commutes' := fun a => congrArg MulOpposite.op (s.fixesScalar a) }
  square := s.involutive

/-- The split hyperbolic matrix coordinates with indices in the base universe
are relabelled by the usual finite indices. -/
abbrev unliftHyperbolicMatrix (n : ℕ) (R : Type u) [CommRing R] :
    Matrix (HyperbolicIndex.{u} n ⊕ HyperbolicIndex.{u} n)
      (HyperbolicIndex.{u} n ⊕ HyperbolicIndex.{u} n) R ≃ₐ[R]
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.reindexAlgEquiv R R
    (Equiv.sumCongr (Equiv.ulift : HyperbolicIndex.{u} n ≃ Fin n) Equiv.ulift)

/-- Split symplectic matrix equations over every test algebra of the local field,
with the scalar-extension maps respected. -/
def SplitLocalModel (s : Involution F A) (n : ℕ) : Prop :=
  ∃ (r : ℕ) (_ : 0 < r) (_ : A ≃ₐ[F] Matrix (Fin r) (Fin r) F)
    (E : ∀ (R : Type u) [CommRing R] [Algebra F R],
      (R ⊗[F] A) ≃ₐ[R] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R),
    (∀ (R : Type u) [CommRing R] [Algebra F R] (x : R ⊗[F] A),
      E R x ∈ Matrix.symplecticGroup (Fin n) R ↔
        (s.baseChange R).toLinearMap x * x = 1) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      (b : R →ₐ[F] S) (x : R ⊗[F] A), E S (tensorMap A b x) = (E R x).map b) ∧
    ∃ i : isometryPoints s ≅ symplecticPoints F (HyperbolicIndex.{u} n),
      ∀ (R : TestAlgebra F) (g : (isometryPoints s).obj R),
        unliftHyperbolicMatrix n R (i.hom.app R g).val = E R (g.val : R ⊗[F] A)

/-- The same canonical Hermitian form models the involution, its isometry
functor, and the isotropic and hyperbolic vectors supplied by a cocharacter. -/
def QuaternionLocalModel (s : Involution F A) (n : ℕ)
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) : Prop :=
  ∃ (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) B)
    (b : AntiAutomorphism F B) (H : (Matrix (Fin n) (Fin n) B)ˣ),
    (∀ x, MulOpposite.unop (b x) = quaternionConjugate hB x) ∧
    dagger b H.val = H.val ∧
    (∀ a, e (s.toLinearMap a) = H.inv * dagger b (e a) * H.val) ∧
    (∀ i, ∃ a : F, H.val i i = algebraMap F B a) ∧
    HermitianLaws b (pairing b.toAlgHom H.val) ∧
    (∀ x, x ≠ 0 → ∃ y, pairing b.toAlgHom H.val x y ≠ 0) ∧
    (∀ x, ∃ a : F, pairing b.toAlgHom H.val x x = algebraMap F B a) ∧
    (∃ (E : ∀ (R : Type u) [CommRing R] [Algebra F R],
        (R ⊗[F] A) ≃ₐ[R] Matrix (Fin n) (Fin n) (R ⊗[F] B))
      (i : isometryPoints s ≅
        _root_.LinearAlgebraicGroups.QuaternionHermitianCocharacters.isometryPoints b.toAlgHom H.val),
      (∀ (R : Type u) [CommRing R] [Algebra F R] (a : A),
        E R (1 ⊗ₜ[F] a) = (e a).map (intoTensor R B)) ∧
      ∀ (R : TestAlgebra F) (g : (isometryPoints s).obj R),
        (i.hom.app R g).val.val = E R (g.val : R ⊗[F] A)) ∧
    let hasHyperbolicPair := ∃ x y : Fin n → B,
      x ≠ 0 ∧ pairing b.toAlgHom H.val x x = 0 ∧
      pairing b.toAlgHom H.val x y = 1 ∧ pairing b.toAlgHom H.val y x = 1 ∧
      pairing b.toAlgHom H.val y y = 0
    ∀ (cochar : multiplicativePoints.{u,u} F ⟶
        _root_.LinearAlgebraicGroups.QuaternionHermitianCocharacters.isometryPoints b.toAlgHom H.val),
      (IsNoncentral cochar → hasHyperbolicPair) ∧
      ((¬ ∀ (R : TestAlgebra F) (t : (multiplicativePoints.{u,u} F).obj R),
        cochar.app R t = 1) → hasHyperbolicPair)

def NonarchimedeanLocalAlternatives (s : Involution F A) (n : ℕ) : Prop :=
  SplitLocalModel s n ∨
    ∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B)
      (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
      _root_.Specs.RM03.CSA.degree F B = 2 ∧ QuaternionLocalModel s n hB

def RealLocalAlternatives {A : Type} [Ring A] [Algebra ℝ A]
    (s : Involution ℝ A) (n : ℕ) : Prop :=
  SplitLocalModel s n ∨
    ∃ (B : Type) (_ : DivisionRing B) (_ : Algebra ℝ B)
      (hB : _root_.Specs.RM03.CSA.isCentralSimple ℝ B),
      Nonempty (B ≃ₐ[ℝ] Quaternion ℝ) ∧ QuaternionLocalModel s n hB

def NonarchimedeanTypeC : Prop :=
  ∀ {F A L : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Ring A] [Algebra F A] [Field L] [Algebra F L]
    (_hA : _root_.Specs.RM03.CSA.isCentralSimple F A) (s : Involution F A) (n : ℕ),
    SymplecticDivisionForms.SplitComparison (toDivisionInvolution s) L n →
    NonarchimedeanLocalAlternatives s n

def RealTypeC : Prop :=
  ∀ {A L : Type} [Ring A] [Algebra ℝ A] [Field L] [Algebra ℝ L]
    (_hA : _root_.Specs.RM03.CSA.isCentralSimple ℝ A) (s : Involution ℝ A) (n : ℕ),
    SymplecticDivisionForms.SplitComparison (toDivisionInvolution s) L n →
    RealLocalAlternatives s n

def ComplexTypeC : Prop :=
  ∀ {A L : Type} [Ring A] [Algebra ℂ A] [Field L] [Algebra ℂ L]
    (_hA : _root_.Specs.RM03.CSA.isCentralSimple ℂ A) (s : Involution ℂ A) (n : ℕ),
    SymplecticDivisionForms.SplitComparison (toDivisionInvolution s) L n →
      SplitLocalModel s n

end DivisionForms

open Arithmetic.SymplecticIsometryDescent (PointsOf)
open SymplecticDatumTorusAndBorel (HyperbolicIndex)
open SymplecticMatrixStructure (symplecticPoints)
open TypeCSplitRecognition (MatrixTwisting)
open DivisionForms (toDivisionInvolution NonarchimedeanLocalAlternatives
  RealLocalAlternatives SplitLocalModel)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n : ℕ} {G H : AffineAlgebraicGroup k}
  {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))}
  {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}
  {t : MatrixTwisting n G H c f}

/-- Both base changes are those of the descended objects, with their test
algebra functors identified over the extension field. -/
abbrev IsometryComparisonAtExtension (d : DescendedTypeC t)
    (F : Type u) [Field F] [Algebra k F] :=
  (groupPointsFunctor F).obj ((groupBaseChange k F).obj G.val) ≅
    isometryPoints (d.model.fixed.involution.baseChange F)

/-- The trace of the involution attains one, including in characteristic two. -/
def DescendedTypeCTraceOne : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} {G H : AffineAlgebraicGroup k}
    {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))}
    {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}
    {t : MatrixTwisting n G H c f} (d : DescendedTypeC t),
    ∃ z : (d.model.fixed.action.fixedSubalgebra : Type u),
      z + d.model.fixed.involution.toLinearMap z = 1

def DescendedTypeCBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    {n : ℕ} {G H : AffineAlgebraicGroup k}
    {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))}
    {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}
    {t : MatrixTwisting n G H c f} (d : DescendedTypeC t) (F : Type u) [Field F] [Algebra k F],
    _root_.Specs.RM03.CSA.isCentralSimple F (F ⊗[k] (d.model.fixed.action.fixedSubalgebra : Type u)) ∧
    Nonempty (SymplecticDivisionForms.SplitComparison
      (toDivisionInvolution (d.model.fixed.involution.baseChange F)) (AlgebraicClosure F) (n + 1)) ∧
    Nonempty (IsometryComparisonAtExtension d F)

/-- The nonarchimedean model applies to the scalar extension of the actual
descended pair, in particular at every finite completion. -/
def NonarchimedeanTypeCAtExtension : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    {n : ℕ} {G H : AffineAlgebraicGroup k}
    {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))}
    {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}
    {t : MatrixTwisting n G H c f} (d : DescendedTypeC t) (F : Type u) [Field F] [Algebra k F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    Nonempty (IsometryComparisonAtExtension d F) ∧
      NonarchimedeanLocalAlternatives (d.model.fixed.involution.baseChange F) (n + 1)

def RealTypeCAtExtension : Prop :=
  ∀ {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra k ℝ]
    {n : ℕ} {G H : AffineAlgebraicGroup k}
    {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex (n + 1))}
    {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}
    {t : MatrixTwisting n G H c f} (d : DescendedTypeC t),
    Nonempty (IsometryComparisonAtExtension d ℝ) ∧
      RealLocalAlternatives (d.model.fixed.involution.baseChange ℝ) (n + 1)

def ComplexTypeCAtExtension : Prop :=
  ∀ {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra k ℂ]
    {n : ℕ} {G H : AffineAlgebraicGroup k}
    {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex (n + 1))}
    {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}
    {t : MatrixTwisting n G H c f} (d : DescendedTypeC t),
    Nonempty (IsometryComparisonAtExtension d ℂ) ∧
      SplitLocalModel (d.model.fixed.involution.baseChange ℂ) (n + 1)

end LocalModels

end LinearAlgebraicGroups.Specs.SymplecticInvolutionModels
