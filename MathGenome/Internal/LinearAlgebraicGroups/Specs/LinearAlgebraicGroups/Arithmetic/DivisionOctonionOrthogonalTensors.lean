import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.Group.Matrix
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

open scoped TensorProduct MatrixGroups RestrictedProduct
open Matrix

namespace LinearAlgebraicGroups.Specs.DivisionOctonionOrthogonalTensors

open Composition.Specification (normBaseChange OctonionNormConditions)
open _root_.Specs.RM03.CSA (isCentralSimple degree genericReducedNorm reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open _root_.RM03.CSA (IsCentralSimple)
open _root_.RM03.CSA.NormOneGroup (normOne mapNormOne)

noncomputable section

variable {k L D V I : Type*} [Field k] [Field L] [Algebra k L]
  [Fintype I] [DecidableEq I]

/-- Conjugation to coordinates in a basis, as an isomorphism of groups. -/
def matrixCoordinates {R : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis I R V) : (V ≃ₗ[R] V) ≃* GL I R :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans Matrix.GeneralLinearGroup.toLin.symm)

/-- The field-valued alternating volume normalized to take value one on the basis. -/
def basisVolume [AddCommGroup V] [Module L V] (b : Module.Basis I L V) :
    AlternatingMap L V L I :=
  b.det

/-- The normalized field-valued volume extends with the coefficients. -/
def VolumeBaseChangeComparison : Prop :=
  ∀ {k L V I : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]
    (b : Module.Basis I k V) (x : I → V),
    basisVolume (b.baseChange L) (fun i => (1 : L) ⊗ₜ[k] x i) =
      algebraMap k L (basisVolume b x)

/-- The homogeneous coordinate polynomial of a quadratic form, also valid
when the characteristic is two. -/
def quadraticPolynomial [AddCommGroup V] [Module k V] [LinearOrder I]
    (b : Module.Basis I k V) (q : QuadraticForm k V) : MvPolynomial I k :=
  ∑ i, ∑ j, MvPolynomial.C (q.toBilin b (b i) (b j)) *
    (MvPolynomial.X i * MvPolynomial.X j)

def MatrixCoordinateComparison : Prop :=
  ∀ {L V I : Type*} [CommRing L] [AddCommGroup V] [Module L V] [Fintype I] [DecidableEq I]
    (b : Module.Basis I L V) (f : V ≃ₗ[L] V) (x : V),
    (matrixCoordinates b f).val.mulVec (b.equivFun x) = b.equivFun (f x) ∧
    (matrixCoordinates b f).val.det = LinearMap.det f.toLinearMap

def QuadraticPolynomialComparison : Prop :=
  ∀ {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Fintype I] [DecidableEq I] [LinearOrder I]
    (b : Module.Basis I k V) (q : QuadraticForm k V),
    (quadraticPolynomial b q).IsHomogeneous 2 ∧
    ∀ (L : Type*) [Field L] [Algebra k L] (x : I → L),
      (quadraticPolynomial b q).eval₂ (algebraMap k L) x =
        normBaseChange L q ((b.baseChange L).equivFun.symm x)

def RightMultiplicationCentralizer : Prop :=
  ∀ {k D I : Type*} [Field k] [Ring D] [Algebra k D] (b : Module.Basis I k D)
    (f : D ≃ₗ[k] D),
    (∀ i x, f (x * b i) = f x * b i) ↔
      ∃ u : Dˣ, ∀ x, f x = (u : D) * x

def DivisionNormPolynomial : Prop :=
  ∀ {k D I : Type*} [Field k] [DivisionRing D] [Algebra k D] [Fintype I]
    (hD : isCentralSimple k D) (b : Module.Basis I k D),
    0 < degree k D ∧ (genericReducedNorm hD b).IsHomogeneous (degree k D) ∧
    ∀ x : I → k, x ≠ 0 → (genericReducedNorm hD b).eval x ≠ 0

/-- The action of a unit by regular left multiplication. -/
def leftUnit {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    Aˣ →* (A ≃ₗ[R] A) where
  toFun u :=
    { LinearMap.mul R A u.val with
      invFun := fun x => (↑u⁻¹ : A) * x
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc] }
  map_one' := by ext x; simp
  map_mul' u v := by ext x; exact mul_assoc _ _ _

/-- Matrix of left multiplication in the coefficient-extended basis. -/
def divisionMatrixHom [Ring D] [Algebra k D] (b : Module.Basis I k D) :
    (L ⊗[k] D)ˣ →* GL I L :=
  (matrixCoordinates (b.baseChange L)).toMonoidHom.comp leftUnit

/-- The norm-one points of the reduced-norm model as units of the extended algebra. -/
def normOneToUnits [Ring D] [Algebra k D] (hD : IsCentralSimple k D)
    (b : Module.Basis I k D) : normOne (R := L) hD b →* (L ⊗[k] D)ˣ :=
  (show normOne (R := L) hD b →* L ⊗[k] D from
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }).toHomUnits

/-- The left regular matrix action of the actual norm-one group. -/
def divisionNormOneMatrixHom [Ring D] [Algebra k D] (hD : IsCentralSimple k D)
    (b : Module.Basis I k D) : normOne (R := L) hD b →* GL I L :=
  (divisionMatrixHom b).comp (normOneToUnits hD b)

/-- The norm of the element recovered from a left multiplication matrix by
applying it to the identity. This polynomial also evaluates on other matrices. -/
def divisionNormInCoordinates [Ring D] [Algebra k D]
    (hD : isCentralSimple k D) (b : Module.Basis I k D) (M : GL I L) : L :=
  (genericReducedNorm hD b).eval₂ (algebraMap k L)
    (M.val.mulVec ((b.baseChange L).equivFun 1))

/-- The regular action of the full group of units, and its restriction to the
kernel of the actual reduced norm on the extended algebra. -/
def DivisionExtensionModel : Prop :=
  ∀ {k L D I : Type*} [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : isCentralSimple k D) (b : Module.Basis I k D),
    let ρ := divisionMatrixHom (L := L) b
    Function.Injective ρ ∧
      (∀ u x, (ρ u).val.mulVec ((b.baseChange L).equivFun x) =
        (b.baseChange L).equivFun (u.val * x)) ∧
      (∀ M : GL I L, (∃ u, ρ u = M) ↔
        ∀ i x, (matrixCoordinates (b.baseChange L)).symm M
            (x * (1 ⊗ₜ[k] b i)) =
          (matrixCoordinates (b.baseChange L)).symm M x * (1 ⊗ₜ[k] b i)) ∧
      (∀ u, (ρ u).val.det =
        normAt hD b u.val ^ degree k D) ∧
      (∀ u, normAt hD b u.val = 1 →
        (ρ u).det = 1 ∧ ∀ x : I → L,
          (genericReducedNorm hD b).eval₂ (algebraMap k L) ((ρ u).val.mulVec x) =
          (genericReducedNorm hD b).eval₂ (algebraMap k L) x)

/-- Commuting with the scalar operators of a basis forces linearity over the
original field in the restriction of scalars. -/
def ScalarOperatorComparison : Prop :=
  ∀ {k K V S : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (c : Module.Basis S k K) (f : V ≃ₗ[k] V),
    (∀ s x, f (c s • x) = c s • f x) ↔
      ∃ F : V ≃ₗ[K] V, ∀ x, F x = f x

/-- Stabilizer of a field-valued quadratic form and its field-valued volume.
The codomains of both tensors are fixed. -/
def QuadraticVolumeStabilizer : Prop :=
  ∀ {L V I : Type*} [Field L] [AddCommGroup V] [Module L V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I L V) (q : QuadraticForm L V)
    (f : V ≃ₗ[L] V),
    ((∀ x, q (f x) = q x) ∧ (∀ x, basisVolume b (fun i => f (x i)) = basisVolume b x)) ↔
    ((∀ x, q (f x) = q x) ∧ (matrixCoordinates b f).det = 1)

/-- The SO model of the given anisotropic nondegenerate form over a number
field and its polynomial input after every extension of coefficients. -/
def OrthogonalPolynomialModel : Prop :=
  ∀ {k V : Type*} [Field k] [NumberField k] [AddCommGroup V] [Module k V]
    {n : ℕ} (b : Module.Basis (Fin n) k V) (q : QuadraticForm k V),
    5 ≤ n → q.polarBilin.Nondegenerate → (∀ x, q x = 0 → x = 0) →
    let p := quadraticPolynomial b q
    p.IsHomogeneous 2 ∧ (∀ x, x ≠ 0 → p.eval x ≠ 0) ∧
    ∀ (L : Type*) [Field L] [Algebra k L] (f : (L ⊗[k] V) ≃ₗ[L] (L ⊗[k] V)),
      let bL := b.baseChange L
      let qL := normBaseChange L q
      (∀ x, qL (f x) = qL x) →
      (∀ x, basisVolume bL (fun i => f (x i)) = basisVolume bL x) →
      (matrixCoordinates bL f).det = 1 ∧
      ∀ x : Fin n → L, p.eval₂ (algebraMap k L) ((matrixCoordinates bL f).val.mulVec x) =
        p.eval₂ (algebraMap k L) x

universe u v w

/-- A linear bijection of octonions preserving multiplication has determinant one. -/
def OctonionDeterminant : Prop :=
  ∀ {L : Type u} [Field L] {C : Type v} [NonAssocRing C] [Module L C]
    [IsScalarTower L C C] [SMulCommClass L C C]
    (q : QuadraticForm L C), OctonionNormConditions q →
    ∀ f : C ≃ₗ[L] C, (∀ x y, f (x * y) = f x * f y) →
      LinearMap.det f.toLinearMap = 1

/-- The matrix stabilizer of the product of the coefficient-extended
octonion algebra preserves the original norm polynomial. -/
def OctonionPolynomialModel : Prop :=
  ∀ {k : Type u} [Field k] {C : Type v} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C]
    (b : Module.Basis (Fin 8) k C) (q : QuadraticForm k C),
    OctonionNormConditions q → (∀ x, q x = 0 → x = 0) →
    let p := quadraticPolynomial b q
    p.IsHomogeneous 2 ∧ (∀ x, x ≠ 0 → p.eval x ≠ 0) ∧
    ∀ (L : Type w) [Field L] [Algebra k L]
      (M : GL (Fin 8) L),
      let c := b.baseChange L
      let f := (matrixCoordinates c).symm M
      ((∀ x y, f (x * y) = f x * f y) ↔
        ∃ g : (L ⊗[k] C) ≃ₗ[L] (L ⊗[k] C),
          matrixCoordinates c g = M ∧ g 1 = 1 ∧ ∀ x y, g (x * y) = g x * g y) ∧
      ((∀ x y, f (x * y) = f x * f y) → M.det = 1 ∧
        ∀ x : Fin 8 → L, p.eval₂ (algebraMap k L) (M.val.mulVec x) = p.eval₂ (algebraMap k L) x)

/-- The actual norm-one points are the kernel of the norm on the unit
stabilizer. The norm is computed in the coefficient extension. -/
def DivisionStabilizerNorm : Prop :=
  ∀ {k L D I : Type*} [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : isCentralSimple k D) (b : Module.Basis I k D),
    (∀ u : (L ⊗[k] D)ˣ,
      divisionNormInCoordinates hD b (divisionMatrixHom b u) = normAt hD b u.val) ∧
    (∀ x : L ⊗[k] D, normAt hD b x = 1 →
      ∃ u : (L ⊗[k] D)ˣ, u.val = x) ∧
    (∀ M : GL I L, M ∈ (divisionMatrixHom (L := L) b).range →
      M.val.det = divisionNormInCoordinates hD b M ^ degree k D)

/-- Continuity on the full product of local stabilizers with the restricted
product topology. For an archimedean factor use the full field as its
reference subring, and at every finite factor use its valuation subring. -/
def DivisionAdelicNorm : Prop :=
  ∀ {k D I J : Type*} [Field k] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : isCentralSimple k D) (b : Module.Basis I k D)
    (L : J → Type*) [∀ j, Field (L j)] [∀ j, Algebra k (L j)]
    [∀ j, TopologicalSpace (L j)] [∀ j, IsTopologicalRing (L j)]
    (O : ∀ j, Subring (L j)),
    (∀ j, O j = ⊤ ∨ ∃ V : ValuationSubring (L j), O j = V.toSubring) →
    let T j := (divisionMatrixHom (L := L j) b).range
    let U j := ((Matrix.GeneralLinearGroup.map (n := I) (O j).subtype).range).comap (T j).subtype
    ∃ N : (Πʳ j : J, [T j, U j]) →* (Πʳ j : J, [L j, O j])ˣ,
      Continuous N ∧ ∀ (x : Πʳ j : J, [T j, U j]) j,
        (N x).val j = divisionNormInCoordinates hD b (x j).val

/-- Extending the coefficients of an action really maps every entry of its
matrix under the given field embedding. -/
def MatrixBaseChangeComparison : Prop :=
  ∀ {k L V I : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]
    (b : Module.Basis I k V) (f : V ≃ₗ[k] V),
    matrixCoordinates (b.baseChange L) (f.baseChange k L V V) =
      Matrix.GeneralLinearGroup.map (algebraMap k L) (matrixCoordinates b f)

/-- After restricting scalars, multiplication and the scalar operators
recover exactly the octonion automorphisms over the original field. -/
def RestrictedOctonionStabilizer : Prop :=
  ∀ {k K C S : Type*} [Field k] [Field K] [Algebra k K] [NonAssocRing C]
    [Module K C] [Module k C] [IsScalarTower k K C]
    (c : Module.Basis S k K) (f : C ≃ₗ[k] C),
    ((∀ s x, f (c s • x) = c s • f x) ∧ (∀ x y, f (x * y) = f x * f y)) ↔
      ∃ g : C ≃ₗ[K] C, (∀ x, g x = f x) ∧ g 1 = 1 ∧
        ∀ x y, g (x * y) = g x * g y

/-- After restricting scalars, the original field-valued tensors and the
scalar operators recover exactly the determinant-one isometries. -/
def RestrictedOrthogonalStabilizer : Prop :=
  ∀ {k K V S I : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [Fintype I] [DecidableEq I] (c : Module.Basis S k K) (b : Module.Basis I K V)
    (q : QuadraticForm K V) (f : V ≃ₗ[k] V),
    ((∀ s x, f (c s • x) = c s • f x) ∧ (∀ x, q (f x) = q x) ∧
      (∀ x, basisVolume b (fun i => f (x i)) = basisVolume b x)) ↔
      ∃ g : V ≃ₗ[K] V, (∀ x, g x = f x) ∧
        (∀ x, q (g x) = q x) ∧ (matrixCoordinates b g).det = 1

open Arithmetic in
/-- The actual local reference rings, with no integral restriction at an
archimedean place. -/
def completionReferenceRing {k : Type u} [Field k] (G : GlobalFieldData.{u,v} k)
    (w : G.Place) : Subring (G.Completion w) :=
  match w with
  | .inl w => (G.integers w).toSubring
  | .inr _ => ⊤

open Arithmetic in
/-- The reduced norm on the full adelic stabilizer takes its values in the
units of the actual scalar adele ring of the global field. -/
def DivisionGlobalAdelicNorm : Prop :=
  ∀ {k : Type u} {D : Type w} {I : Type*} [Field k] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (G : GlobalFieldData.{u,v} k)
    (hD : isCentralSimple k D) (b : Module.Basis I k D),
    letI (j : G.Place) : Algebra k (G.Completion j) := (G.embedding j).toAlgebra
    let T j := (divisionMatrixHom (L := G.Completion j) b).range
    let U j := ((Matrix.GeneralLinearGroup.map (n := I)
      (completionReferenceRing G j).subtype).range).comap (T j).subtype
    ∃ N : (Πʳ j : G.Place, [T j, U j]) →* G.AdeleRingˣ, Continuous N ∧
      ∀ (x : Πʳ j : G.Place, [T j, U j]) j,
        G.coordinate j (N x).val = divisionNormInCoordinates hD b (x j).val

/-- At a completion, the norm of a scalar-extended rational unit is the
image of its rational reduced norm. -/
def DivisionRationalNormComparison : Prop :=
  ∀ {k L D I : Type*} [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : isCentralSimple k D) (b : Module.Basis I k D) (u : Dˣ),
    let i : D →ₐ[k] L ⊗[k] D := Algebra.TensorProduct.includeRight
    divisionNormInCoordinates hD b (divisionMatrixHom b (Units.map i.toMonoidHom u)) =
      algebraMap k L (reducedNorm hD u.val)

/-- The matrix of a right multiplication tensor in the chosen basis. -/
def rightMultiplicationMatrix [Ring D] [Algebra k D]
    (b : Module.Basis I k D) (x : D) : Matrix I I k :=
  LinearMap.toMatrix b b ((LinearMap.mul k D).flip x)

/-- The larger matrix stabilizer is cut out by the coefficient-extended
right multiplication matrices. The reduced norm cuts out the norm-one group inside it. -/
def DivisionTensorStabilizer : Prop :=
  ∀ {k L D I : Type*} [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : isCentralSimple k D) (b : Module.Basis I k D),
    let ρ := divisionMatrixHom (L := L) b
    let R i := (rightMultiplicationMatrix b (b i)).map (algebraMap k L)
    (∀ M : GL I L, M ∈ ρ.range ↔ ∀ i, M.val * R i = R i * M.val) ∧
    (∀ M : GL I L, ((∀ i, M.val * R i = R i * M.val) ∧
      divisionNormInCoordinates hD b M = 1) ↔
        ∃ x : (L ⊗[k] D)ˣ, normAt hD b x.val = 1 ∧ ρ x = M) ∧
    (∀ x : Dˣ,
      ρ (Units.map (Algebra.TensorProduct.includeRight :
        D →ₐ[k] L ⊗[k] D).toMonoidHom x) =
        Matrix.GeneralLinearGroup.map (algebraMap k L) (matrixCoordinates b (leftUnit x)))

/-- The norm-one point group acts faithfully and its image is the norm-one
part of the right multiplication stabilizer. -/
def DivisionNormOneMatrixModel : Prop :=
  ∀ {k L D I : Type*} [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : IsCentralSimple k D) (b : Module.Basis I k D),
    let ρ := divisionNormOneMatrixHom (L := L) hD b
    let c := b.baseChange L
    let R i := (rightMultiplicationMatrix b (b i)).map (algebraMap k L)
    let p := genericReducedNorm hD b
    Function.Injective ρ ∧
      (∀ u x, (ρ u).val.mulVec (c.equivFun x) = c.equivFun (u.val * x)) ∧
      (∀ M : GL I L, M ∈ ρ.range ↔
        (∀ i, M.val * R i = R i * M.val) ∧ divisionNormInCoordinates hD b M = 1) ∧
      (∀ u, (ρ u).det = 1 ∧ ∀ x : I → L,
        p.eval₂ (algebraMap k L) ((ρ u).val.mulVec x) = p.eval₂ (algebraMap k L) x)

/-- The change of coefficients on norm-one points becomes the corresponding
entrywise map of matrices. -/
def DivisionNormOneMatrixNaturality : Prop :=
  ∀ {k L E D I : Type*} [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]
    [Ring D] [Algebra k D] [Fintype I] [DecidableEq I]
    (hD : IsCentralSimple k D) (b : Module.Basis I k D) (a : L →ₐ[k] E)
    (x : normOne (R := L) hD b),
    divisionNormOneMatrixHom hD b (mapNormOne hD b a x) =
      Matrix.GeneralLinearGroup.map a.toRingHom (divisionNormOneMatrixHom hD b x)

/-- Integrality of the regular left multiplication matrix implies integrality
of the reduced norm, even if the inverse matrix has nonintegral entries. -/
def DivisionNormIntegral : Prop :=
  ∀ {k L D I : Type*} [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : isCentralSimple k D) (b : Module.Basis I k D)
    (O : ValuationSubring L) (x : L ⊗[k] D),
    (∀ i j, LinearMap.toMatrix (b.baseChange L) (b.baseChange L)
      (LinearMap.mul L _ x) i j ∈ O) →
    normAt hD b x ∈ O

/-- The unit stabilizer and its norm-one subgroup are closed in the local
general linear group. -/
def DivisionClosedStabilizers : Prop :=
  ∀ {k L D I : Type*} [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L]
    (hD : isCentralSimple k D) (b : Module.Basis I k D),
    let T := (divisionMatrixHom (L := L) b).range
    IsClosed (T : Set (GL I L)) ∧
      IsClosed {M : GL I L | M ∈ T ∧ divisionNormInCoordinates hD b M = 1}

/-- The scalar operators of a field basis, as endomorphisms of the
restricted vector space, cut out the linear group over the original field. -/
def ScalarMatrixComparison : Prop :=
  ∀ {k K V S I : Type*} [Field k] [Field K] [Algebra k K] [AddCommGroup V]
    [Module K V] [Module k V] [IsScalarTower k K V] [Fintype I] [DecidableEq I]
    (c : Module.Basis S k K) (b : Module.Basis I k V) (M : GL I k),
    let T s := LinearMap.toMatrix b b (DistribSMul.toLinearMap k V (c s))
    (∀ s, M.val * T s = T s * M.val) ↔
      ∃ g : V ≃ₗ[K] V, matrixCoordinates b (g.restrictScalars k) = M

open Composition.OctonionAutomorphismSpecification (AutomorphismGroup octonionAlgebra)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (bilinearStabilizer schemePoints)

/-- Matrix action of the represented octonion automorphism group at a coefficient field. -/
def octonionMatrixHom {k L : Type u} [Field k] [Field L] [Algebra k L] {C : Type v}
    [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    (b : Module.Basis (Fin 8) k C) (A : AutomorphismGroup k C) :
    ((schemePoints k).obj A.group).obj (CommAlgCat.of k L) →* GL (Fin 8) L :=
  let B := bilinearStabilizer (octonionAlgebra (R := k) (C := C)) L
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv L (L ⊗[k] C)
  (matrixCoordinates (b.baseChange L)).toMonoidHom.comp
    (e.toMonoidHom.comp (B.subtype.comp (A.subgroupPoints (CommAlgCat.of k L)).toMonoidHom))

/-- The multiplication table in the extended basis is the original table
with its coefficients mapped to the extension field. -/
def OctonionMultiplicationCoordinates : Prop :=
  ∀ {k L C I : Type*} [Field k] [Field L] [Algebra k L] [NonAssocRing C]
    [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    [Fintype I] [DecidableEq I] (b : Module.Basis I k C) (i j a : I),
    let c := b.baseChange L
    c.equivFun (c i * c j) a = algebraMap k L (b.equivFun (b i * b j) a)

/-- The actual automorphism scheme's points in a coefficient field map
faithfully to matrices, with image given by the finite multiplication table. -/
def OctonionMatrixStabilizer : Prop :=
  ∀ {k L : Type u} [Field k] [Field L] [Algebra k L] {C : Type v}
    [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    (b : Module.Basis (Fin 8) k C) (A : AutomorphismGroup k C),
    let S := CommAlgCat.of k L
    let c := b.baseChange L
    let ρ := octonionMatrixHom (L := L) b A
    Function.Injective ρ ∧
      (∀ g x, (ρ g).val.mulVec (c.equivFun x) =
        c.equivFun ((A.subgroupPoints S g).val.val x)) ∧
      ∀ M,
        let f := (matrixCoordinates c).symm M
        (M ∈ ρ.range ↔ ∀ i j, f (c i * c j) = f (c i) * f (c j)) ∧
        ((∀ i j, f (c i * c j) = f (c i) * f (c j)) ↔
          ∀ x y, f (x * y) = f x * f y)

/-- The multiplication equations give a closed subgroup in local matrix coordinates. -/
def OctonionClosedStabilizer : Prop :=
  ∀ {k L : Type u} [Field k] [Field L] [Algebra k L]
    [TopologicalSpace L] [IsTopologicalRing L] [T2Space L] {C : Type v}
    [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    (b : Module.Basis (Fin 8) k C) (A : AutomorphismGroup k C),
    IsClosed ((octonionMatrixHom (L := L) b A).range : Set (GL (Fin 8) L))

/-- The determinant-one isometries of a quadratic form. -/
def specialOrthogonalGroup [AddCommGroup V] [Module L V] (q : QuadraticForm L V) :
    Subgroup (V ≃ₗ[L] V) where
  carrier := {f | (∀ x, q (f x) = q x) ∧ f.det = 1}
  one_mem' := ⟨fun _ => rfl, map_one _⟩
  mul_mem' := by
    rintro f g ⟨hf, df⟩ ⟨hg, dg⟩
    exact ⟨fun x => (hf (g x)).trans (hg x), by rw [map_mul, df, dg, mul_one]⟩
  inv_mem' := by
    rintro f ⟨hf, df⟩
    refine ⟨fun x => ?_, by rw [map_inv, df, inv_one]⟩
    change q (f.symm x) = q x
    simpa only [LinearEquiv.apply_symm_apply] using (hf (f.symm x)).symm

/-- The image of the coefficient-extended special orthogonal group in
matrix coordinates is the finite stabilizer of the quadratic form and volume. -/
def OrthogonalMatrixStabilizer : Prop :=
  ∀ {k L V I : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]
    (b : Module.Basis I k V) (q : QuadraticForm k V),
    let c := b.baseChange L
    let qL := normBaseChange L q
    let ρ := (matrixCoordinates c).toMonoidHom.comp (specialOrthogonalGroup qL).subtype
    Function.Injective ρ ∧
    (∀ f x, (ρ f).val.mulVec (c.equivFun x) = c.equivFun (f.val x)) ∧
    ∀ M : GL I L, M ∈ ρ.range ↔
      let f := (matrixCoordinates c).symm M
      (∀ i, qL (f (c i)) = qL (c i)) ∧
      (∀ i j, qL.polarBilin (f (c i)) (f (c j)) = qL.polarBilin (c i) (c j)) ∧
      basisVolume c (fun i => f (c i)) = basisVolume c c

/-- The special orthogonal image is closed in the local general linear group. -/
def OrthogonalClosedStabilizer : Prop :=
  ∀ {k L V : Type*} [Field k] [Field L] [Algebra k L]
    [TopologicalSpace L] [IsTopologicalRing L] [T2Space L]
    [AddCommGroup V] [Module k V] {n : ℕ}
    (b : Module.Basis (Fin n) k V) (q : QuadraticForm k V),
    let ρ := (matrixCoordinates (b.baseChange L)).toMonoidHom.comp
      (specialOrthogonalGroup (normBaseChange L q)).subtype
    IsClosed (ρ.range : Set (GL (Fin n) L))

end
end LinearAlgebraicGroups.Specs.DivisionOctonionOrthogonalTensors
