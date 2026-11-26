import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticInvolutionTensors
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.GroupTheory.GroupAction.Basic

namespace LinearAlgebraicGroups.Specs.AnisotropicTensorQuotients

/-- If rational changes of basis move a closed subgroup into a compact set and
only finitely many labels occur among these changes, a label that determines the
basis up to a rational member of the subgroup suffices for compactness. -/
def CompactOfFiniteBasisLabels : Prop :=
  ∀ {A P T : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group P]
    (G : Subgroup A) (i : P →* A) (C : Set A) (label : P → T) (S : Set T),
    IsClosed (G : Set A) → IsCompact C → S.Finite →
    (∀ r s, label r = label s → i (r * s⁻¹) ∈ G) →
    (∀ g : G, ∃ r : P, (g : A) * i r ∈ C ∧ label r ∈ S) →
    CompactSpace (G ⧸ i.range.subgroupOf G)

/-- A continuous orbit map sends a compact adelic basis set to a compact set of
transformed tensors. Its intersection with the rational diagonal is finite. -/
def CompactOfTensorReduction : Prop :=
  ∀ {A P T : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group P]
    [TopologicalSpace T] [MulAction A T]
    (G : Subgroup A) (i : P →* A) (C : Set A) (t : T) (D : Set T),
    IsClosed (G : Set A) → IsCompact C → IsClosed D → IsDiscrete D →
    Continuous (fun a : A => a⁻¹ • t) →
    (∀ g : G, (g : A) • t = t) →
    (∀ r : P, i r • t = t → i r ∈ G) →
    (∀ r : P, (i r)⁻¹ • t ∈ D) →
    (∀ g : G, ∃ r : P, (g : A) * i r ∈ C) →
    CompactSpace (G ⧸ i.range.subgroupOf G)

/-- For the norm-one correction, first reduce by the larger rational group
`P`. The norm of the rational multiplier equals the norm of the reduced adelic
point. Only finitely many rational norms occur in that compact norm image. -/
def CompactOfNormCorrection : Prop :=
  ∀ {A P U : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group P]
    [Group U] [TopologicalSpace U] [T1Space U]
    (i : P →* A) (ν : A →* U) (C : Set A) (D : Set U),
    IsCompact C → Continuous ν → IsClosed D → IsDiscrete D →
    (∀ r : P, ν (i r) ∈ D) →
    (∀ g : ν.ker, ∃ r : P, (g : A) * i r ∈ C) →
    CompactSpace (ν.ker ⧸ i.range.subgroupOf ν.ker)

open Arithmetic Arithmetic.AdelicLatticeBounds IsDedekindDomain

universe u v z

/-- A finite tuple of rational coefficients can take only finitely many values
in a compact set of tuples over the full scalar adele ring. -/
def FiniteRationalTensorCoordinates : Prop :=
  ∀ {k : Type u} [Field k] (D : GlobalFieldData.{u, v} k)
    {J : Type*} [Finite J] (e : k →+* D.AdeleRing)
    (_he : Function.Injective e) (_hcoord : ∀ w x, D.coordinate w (e x) = D.embedding w x)
    (C : Set (J → D.AdeleRing)), IsCompact C →
    {x : J → k | (fun j => e (x j)) ∈ C}.Finite

/-- The operators of right multiplication by a basis determine the left
multiplication subgroup, over the ground field or a coefficient field. -/
def RightMultiplicationCentralizer : Prop :=
  ∀ {k D J : Type*} [Field k] [Ring D] [Algebra k D] (b : Module.Basis J k D)
    (f : D ≃ₗ[k] D),
    (∀ j x, f (x * b j) = f x * b j) ↔
      ∃ u : Dˣ, ∀ x, f x = (u : D) * x

/-- The division hypothesis makes the homogeneous reduced-norm polynomial
nonzero at every nonzero coordinate vector. -/
def DivisionNormAnisotropic : Prop :=
  ∀ {k D J : Type*} [Field k] [DivisionRing D] [Algebra k D] [Fintype J]
    (hD : _root_.Specs.RM03.CSA.isCentralSimple k D) (b : Module.Basis J k D),
    0 < _root_.Specs.RM03.CSA.degree k D ∧
    (_root_.Specs.RM03.CSA.genericReducedNorm hD b).IsHomogeneous
      (_root_.Specs.RM03.CSA.degree k D) ∧
    ∀ x : J → k, x ≠ 0 → (_root_.Specs.RM03.CSA.genericReducedNorm hD b).eval x ≠ 0

/-- Multiplying a polynomial by a nonzero scalar clears its coefficients over
the reference integer ring without changing its zero locus or invariance. -/
def ClearPolynomialDenominators : Prop :=
  ∀ {R k J : Type*} [CommRing R] [IsDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] (p : MvPolynomial J k),
    ∃ (a : R) (q : MvPolynomial J R),
      a ≠ 0 ∧ MvPolynomial.map (algebraMap R k) q = MvPolynomial.C (algebraMap R k a) * p

/-- The adelic tensor comparison in finite coefficient coordinates. The
coordinate identity is the invariance of the original tensor under the given
adelic subgroup, after it is expressed in the reduced basis. -/
def CompactOfAdelicTensorCoordinates : Prop :=
  ∀ {k : Type u} [Field k] (D : GlobalFieldData.{u, v} k)
    (e : k →+* D.AdeleRing), Function.Injective e →
    (∀ w x, D.coordinate w (e x) = D.embedding w x) →
    ∀ {A P J : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group P]
      [Finite J] (G : Subgroup A) (i : P →* A) (C : Set A)
      (label : P → J → k) (orbit : A → J → D.AdeleRing),
    IsClosed (G : Set A) → IsCompact C → Continuous orbit →
    (∀ r s, label r = label s → i (r * s⁻¹) ∈ G) →
    (∀ g : G, ∃ r : P, (g : A) * i r ∈ C ∧ orbit ((g : A) * i r) = e ∘ label r) →
    CompactSpace (G ⧸ i.range.subgroupOf G)

/-- The reduced norm values permitted by preservation of the top exterior
form in the special-unitary correction form a finite set. -/
def FiniteRootsOfUnity : Prop :=
  ∀ {k : Type*} [Field k] (d : ℕ), 0 < d → {a : k | a ^ d = 1}.Finite

/-- The determinant on the regular module is the degree-th power of the
reduced norm. This controls both determinant one and integrality of norms. -/
def DetLeftMulEqReducedNormPow : Prop :=
  ∀ {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (hA : _root_.Specs.RM03.CSA.isCentralSimple k A) (a : A),
    LinearMap.det (LinearMap.mul k A a) =
      _root_.Specs.RM03.CSA.reducedNorm hA a ^ _root_.Specs.RM03.CSA.degree k A

/-- Trace one and an isotropic idempotent give the two orthogonal
idempotents used to construct a split cocharacter of the isometry group. -/
def OrthogonalAdjointIdempotents : Prop :=
  ∀ {A : Type*} [Ring A] (σ : A ≃+* Aᵐᵒᵖ),
    let s (x : A) := MulOpposite.unop (σ x)
    Function.Involutive s →
    ∀ z e : A, z + s z = 1 → e ≠ 0 → e * e = e → s e * e = 0 →
    ∃ p : A, p ≠ 0 ∧ p * p = p ∧ s p * p = 0 ∧ p * s p = 0

/-- Basis adeles give invertible matrices over the product of the finite
scalar adele ring and the distinguished completion. Both the entries and the
inverse entries are continuous in the restricted product topology. -/
def AdelicBasisMatrixCoordinates : Prop :=
  ∀ {R k B J : Type*} [CommRing R] [IsDedekindDomain R]
    [Field k] [Algebra R k] [IsFractionRing R k] [Field B] [TopologicalSpace B]
    [Fintype J] [DecidableEq J],
    ∃ m : BasisAdeles R k B J →*
        Matrix.GeneralLinearGroup J (FiniteAdeleRing R k × B),
      Continuous m ∧ Function.Injective m ∧
      (∀ (a : BasisAdeles R k B J) p i j, ((m a).val i j).1 p = (a.1 p).val i j) ∧
      (∀ (a : BasisAdeles R k B J) i j, ((m a).val i j).2 = a.2.val i j)

open scoped MatrixGroups NumberField RestrictedProduct
open Arithmetic.TensorAdelicReduction

/-- The subgroup of matrix adeles whose coordinates belong to the given local groups. -/
def localConditions {A W : Type*} {B : W → Type*} [Group A] [∀ w, Group (B w)]
    (atPlace : ∀ w, A →* B w) (H : ∀ w, Subgroup (B w)) : Subgroup A :=
  ⨅ w, (H w).comap (atPlace w)

/-- Compactness of the right quotient by the image of the stated rational point group. -/
def CompactMatrixQuotient {A P : Type*} [Group A] [Group P] [TopologicalSpace A]
    (G : Subgroup A) (Γ : Subgroup P) (δ : P →* A) : Prop :=
  Γ.map δ ≤ G ∧ CompactSpace (G ⧸ (Γ.map δ).subgroupOf G)

section MatrixAdeles

variable {k : Type u} {I : Type*} [Field k] [Fintype I] [DecidableEq I]

/-- A family of matrix groups in the same basis over coefficient fields. -/
abbrev MatrixModel (k : Type u) (I : Type*) [Field k] [Fintype I] [DecidableEq I] :=
  ∀ (L : Type u) [Field L], (k →+* L) → Subgroup (GL I L)

def functionAtPlace (w : FunctionPlace k) :
    FunctionMatrixAdeles k I →* GL I w.Completion where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl

def numberAtPlace [NumberField k] (w : NumberPlace k) :
    NumberMatrixAdeles k I →* GL I w.Completion :=
  match w with
  | .inl w =>
    { toFun := fun a => a.1 w
      map_one' := rfl
      map_mul' _ _ := rfl }
  | .inr w =>
    { toFun := fun a => a.2 w
      map_one' := rfl
      map_mul' _ _ := rfl }

/-- The function-field quotient in the intrinsic matrix restricted product.
The integral reference subgroup at each place is the intersection with
the integral general linear group, so the subgroup topology is given by
the restricted-product boxes for the local groups. -/
def FunctionMatrixQuotientCompact (H : MatrixModel k I) : Prop :=
  ∃ δ : GL I k →* FunctionMatrixAdeles k I,
    (∀ r w, δ r w = Matrix.GeneralLinearGroup.map w.embedding r) ∧
      CompactMatrixQuotient
        (localConditions functionAtPlace (fun w => H w.Completion w.embedding))
        (H k (RingHom.id k)) δ

/-- The number-field quotient in the finite restricted product times the
archimedean matrix groups, using the induced topology from the matrix adeles. -/
def NumberMatrixQuotientCompact [NumberField k] (H : MatrixModel k I) : Prop :=
  ∃ δ : GL I k →* NumberMatrixAdeles k I,
    (∀ r w, numberAtPlace w (δ r) = Matrix.GeneralLinearGroup.map w.embedding r) ∧
      CompactMatrixQuotient
        (localConditions numberAtPlace (fun w => H w.Completion w.embedding))
        (H k (RingHom.id k)) δ

/-- The same conclusion for both kinds of global fields. -/
def GlobalMatrixQuotientCompact (D : GlobalFieldData.{u,v} k) (H : MatrixModel k I) : Prop :=
  match D with
  | .number h => letI := h; NumberMatrixQuotientCompact H
  | @GlobalFieldData.function _ _ _ _ _ _ _ => FunctionMatrixQuotientCompact H

end MatrixAdeles

open DivisionOctonionOrthogonalTensors Composition.Specification
open Composition.OctonionAutomorphismSpecification (AutomorphismGroup)

noncomputable section

variable {k : Type u} [Field k] {C : Type v} [NonAssocRing C] [Module k C]
  [IsScalarTower k C C] [SMulCommClass k C C]

/-- Matrices of the actual octonion algebra automorphism scheme in the given basis. -/
def octonionMatrixModel (b : Module.Basis (Fin 8) k C) (A : AutomorphismGroup k C) :
    MatrixModel k (Fin 8) := fun L _ e =>
  letI : Algebra k L := e.toAlgebra
  (octonionMatrixHom (L := L) b A).range

/-- The adelic quotient of the automorphism group of an anisotropic octonion
algebra over a number field or a global function field. -/
def OctonionCompactness : Prop :=
  ∀ {k : Type u} [Field k] (D : GlobalFieldData.{u, z} k)
    {C : Type v} [NonAssocRing C] [Module k C] [IsScalarTower k C C]
    [SMulCommClass k C C] (b : Module.Basis (Fin 8) k C) (q : QuadraticForm k C)
    (A : AutomorphismGroup k C),
    OctonionNormConditions q → (∀ x, q x = 0 → x = 0) →
    GlobalMatrixQuotientCompact D (octonionMatrixModel b A)

end

section Orthogonal

variable {k : Type u} [Field k] [NumberField k] {V : Type v}
  [AddCommGroup V] [Module k V] {n : ℕ}

/-- The determinant-one isometries in the extended basis of the quadratic space. -/
noncomputable def orthogonalMatrixModel (b : Module.Basis (Fin n) k V) (q : QuadraticForm k V) :
    MatrixModel k (Fin n) := fun L _ e =>
  letI : Algebra k L := e.toAlgebra
  (matrixCoordinates (b.baseChange L)).toMonoidHom.comp
    (specialOrthogonalGroup (normBaseChange L q)).subtype |>.range

/-- The special orthogonal quotient of a nondegenerate anisotropic quadratic
space of dimension at least five over a number field. -/
def OrthogonalCompactness : Prop :=
  ∀ {k : Type u} [Field k] [NumberField k] {V : Type v} [AddCommGroup V] [Module k V]
    {n : ℕ} (b : Module.Basis (Fin n) k V) (q : QuadraticForm k V),
    5 ≤ n → q.polarBilin.Nondegenerate → (∀ x, q x = 0 → x = 0) →
    NumberMatrixQuotientCompact (orthogonalMatrixModel b q)

end Orthogonal

section DivisionAlgebra

open _root_.RM03.CSA (IsCentralSimple)

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {I : Type} [Fintype I] [DecidableEq I]

/-- The reduced-norm-one units, acting by left multiplication in the extended basis. -/
noncomputable def divisionMatrixModel (hA : IsCentralSimple k A) (b : Module.Basis I k A) :
    MatrixModel k I := fun L _ e =>
  letI : Algebra k L := e.toAlgebra
  (divisionNormOneMatrixHom (L := L) hA b).range

/-- The full adelic quotient of the reduced-norm-one group of a central division algebra. -/
def DivisionCompactness : Prop :=
  ∀ {k : Type u} [Field k] (D : GlobalFieldData.{u, z} k)
    {A : Type v} [DivisionRing A] [Algebra k A] {I : Type} [Fintype I] [DecidableEq I]
    (hA : IsCentralSimple k A) (b : Module.Basis I k A),
    GlobalMatrixQuotientCompact D (divisionMatrixModel hA b)

end DivisionAlgebra

section ColumnRepresentations

open scoped TensorProduct

variable {R B V I J : Type*} [CommRing R]

/-- A representation on a free module sends algebra units to invertible
matrices in its given basis. -/
noncomputable def matrixOfUnits [Ring B] [Algebra R B] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I R V)
    (ρ : B →ₐ[R] Module.End R V) : Bˣ →* GL I R :=
  (matrixCoordinates b).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V).toMonoidHom.comp
      (Units.map ρ.toMonoidHom))

/-- Product coordinates for the column space of a division matrix algebra. -/
noncomputable def columnBasis [AddCommGroup V] [Module R V]
    [Fintype I] [Fintype J] (b : Module.Basis J R V) : Module.Basis (I × J) R (I → V) :=
  Module.Basis.ofEquivFun
    { toFun := fun x ij => b.equivFun (x ij.1) ij.2
      invFun := fun x i => b.equivFun.symm (fun j => x (i, j))
      left_inv := fun x => funext fun i => b.equivFun.symm_apply_apply (x i)
      right_inv := fun x => funext fun ij =>
        congrFun (b.equivFun.apply_symm_apply (fun j => x (ij.1, j))) ij.2
      map_add' := fun x y => funext fun ij => congrFun (b.equivFun.map_add (x ij.1) (y ij.1)) ij.2
      map_smul' := fun a x => funext fun ij => congrFun (b.equivFun.map_smul a (x ij.1)) ij.2 }

/-- The algebra action by left matrix multiplication on columns. -/
def matrixColumnAction [Ring B] [Algebra R B] [Fintype I] [DecidableEq I] :
    Matrix I I B →ₐ[R] Module.End R (I → B) where
  toFun := AnisotropicSymplecticInvolutionTensors.columnAction (R := R)
  map_zero' := LinearMap.ext fun x => Matrix.zero_mulVec x
  map_one' := LinearMap.ext fun x => Matrix.one_mulVec x
  map_add' a b := LinearMap.ext fun x => Matrix.add_mulVec a b x
  map_mul' a b := LinearMap.ext fun x => (Matrix.mulVec_mulVec x a b).symm
  commutes' c := LinearMap.ext fun x => by
    change (algebraMap R (Matrix I I B) c).mulVec x = c • x
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

end ColumnRepresentations

section SymplecticInvolution

open scoped TensorProduct
open Arithmetic.SymplecticIsometryDescent (Involution)
open AnisotropicSymplecticInvolutionTensors (HermitianModel IsAnisotropic)
open SymplecticDivisionForms (SplitComparison)
open SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)

variable {k A B : Type u} [Field k] [Ring A] [Algebra k A] [DivisionRing B] [Algebra k B]
  {r : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- The column action of the original symplectic involution group after
coefficient extension to a field. -/
noncomputable def symplecticMatrixModel (s : Involution k A) (b : Module.Basis J k B)
    (E : ∀ (R : Type u) [CommRing R] [Algebra k R],
      (R ⊗[k] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[k] B)) :
    MatrixModel k (Fin r × J) := fun L _ e =>
  letI : Algebra k L := e.toAlgebra
  let c := columnBasis (I := Fin r) (b.baseChange L)
  (s.baseChange L).isometries.map (matrixOfUnits c (matrixColumnAction.comp (E L).toAlgHom))

/-- The adelic quotient of the original anisotropic symplectic involution
group, represented on the right module of its global division corner. -/
def SymplecticCompactness : Prop :=
  ∀ {k A K : Type u} [Field k] (D : GlobalFieldData.{u, z} k)
    [Ring A] [Algebra k A] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (_hA : _root_.Specs.RM03.CSA.isCentralSimple k A) (s : Involution k A) {n : ℕ},
    SplitComparison (toDivisionInvolution s) K n → IsAnisotropic s →
    ∃ (r : ℕ) (B : Type u) (_ : DivisionRing B) (_ : Algebra k B),
      _root_.Specs.RM03.CSA.isCentralDivision k B ∧
      ∃ (m : HermitianModel (toDivisionInvolution s) r (D := B)) (j : ℕ)
        (b : Module.Basis (ULift.{u} (Fin j)) k B)
        (E : ∀ (R : Type u) [CommRing R] [Algebra k R],
          (R ⊗[k] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[k] B)),
        (∀ (R : Type u) [CommRing R] [Algebra k R] (a : A),
          E R (1 ⊗ₜ[k] a) = (m.equiv a).map (SymplecticDivisionForms.intoTensor R B)) ∧
        GlobalMatrixQuotientCompact D (symplecticMatrixModel s b E)

end SymplecticInvolution

section SpecialUnitary

open scoped TensorProduct
open AnisotropicUnitaryTensors
  (Mat extendedColumnAction HasClosedSplitTorus IsSelfAdjointDivisionCorner HermitianMatrix form)
open OuterTypeAModels (RepresentsUnitary)
open LinearAlgebraicGroups.UnitaryNormEquations (SecondKind IsSpecialUnitary)

variable {K E A B : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing B] [Algebra K B] [Algebra E B] [IsScalarTower K E B]
  {r : ℕ} {I : Type u} [Fintype I] [DecidableEq I]

/-- In the coefficient-extended column basis, the special unitary equations
give the matrix image of the original group. -/
noncomputable def unitaryMatrixRepresentation {L : Type u} [Field L] [Algebra K L]
    (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I K (Fin r → B)) :
    (L ⊗[K] A)ˣ →* GL I L :=
  matrixOfUnits (v.baseChange L) (extendedColumnAction e)

/-- The full adelic quotient of the anisotropic special unitary group in
its Hermitian representation from the global self-adjoint division corner. -/
def UnitaryCompactness : Prop :=
  ∀ {k E A : Type u} [Field k] (D : GlobalFieldData.{u,z} k)
    [Field E] [Algebra k E] [Algebra.IsSeparable k E] [Ring A]
    [Algebra k A] [Algebra E A] [IsScalarTower k E A],
    Module.finrank k E = 2 →
    ∀ {I : Type u} [Fintype I] (hA : _root_.Specs.RM03.CSA.isCentralSimple E A),
    3 ≤ _root_.Specs.RM03.CSA.degree E A →
    ∀ (b : Module.Basis I E A) (s : SecondKind k E A) (G : AffineAlgebraicGroup k),
    RepresentsUnitary hA b s G → ¬ HasClosedSplitTorus G →
    ∃ (r : ℕ) (B : Type u) (_ : DivisionRing B) (_ : Algebra E B),
      letI : Algebra k B := Algebra.compHom B (algebraMap k E)
      letI : IsScalarTower k E B := IsScalarTower.of_algebraMap_eq fun _ => rfl
      _root_.Specs.RM03.CSA.isCentralDivision E B ∧
      ∃ (e : A ≃ₐ[E] Mat r B) (x : Fin r → B) (p : A) (i : B →ₗ[E] A)
        (τ : SecondKind k E B) (H : (Mat r B)ˣ),
        IsSelfAdjointDivisionCorner s e x p i τ ∧ HermitianMatrix s e τ H ∧
        (∀ y : Fin r → B, y ≠ 0 → form τ H.val y y ≠ 0) ∧
        ∃ (j : ℕ) (v : Module.Basis (ULift.{u} (Fin j)) k (Fin r → B))
          (M : MatrixModel k (ULift.{u} (Fin j))),
          (∀ (L : Type u) [Field L] (a : k →+* L),
            letI : Algebra k L := a.toAlgebra
            Function.Injective (unitaryMatrixRepresentation (L := L) e v) ∧
            ∀ g : GL (ULift.{u} (Fin j)) L, g ∈ M L a ↔
              ∃ x : (L ⊗[k] A)ˣ,
                IsSpecialUnitary hA b s x ∧ unitaryMatrixRepresentation e v x = g) ∧
          GlobalMatrixQuotientCompact D M

end SpecialUnitary

end LinearAlgebraicGroups.Specs.AnisotropicTensorQuotients
