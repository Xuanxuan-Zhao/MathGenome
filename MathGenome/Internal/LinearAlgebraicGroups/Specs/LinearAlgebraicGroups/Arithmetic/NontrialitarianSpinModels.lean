import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

open Matrix CategoryTheory
open scoped Matrix TensorProduct

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels

open SymplecticDivisionForms (Involution antiValue)
open SymplecticInvolutionModels (AntiAutomorphism)
open OddSpinModels (coordinateVector evenSum)

/-- In vector-torus coordinates, the type-D coroots are the vectors with two
nonzero coordinates, each equal to 1 or -1. -/
def coroots (ι : Type u) [DecidableEq ι] : Set (ι → ℤ) :=
  {v | ∃ i j, i ≠ j ∧ (v = coordinateVector ι i - coordinateVector ι j ∨
    v = coordinateVector ι i + coordinateVector ι j ∨
    v = -(coordinateVector ι i + coordinateVector ι j))}

/-- The span of the type-D coroots is exactly the image of the cocharacter
lattice of the torus given by the spin equation `u² ∏ tᵢ = 1`. -/
def CorootLattice : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [Nontrivial ι],
    Submodule.span ℤ (coroots ι) = evenSum ι ∧
    ∀ v : ι → ℤ, (∃ a : ℤ, 2 * a + ∑ i, v i = 0) ↔ v ∈ evenSum ι

/-- The division algebra in an odd-characteristic local matrix model of an
algebra with first-kind involution has degree one or two. -/
def NonarchimedeanDivision : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {A : Type v} [Ring A] [Algebra F A],
    (2 : F) ≠ 0 → _root_.Specs.RM03.CSA.isCentralSimple F A → Involution F A →
    ∃ (B : Type v) (_ : DivisionRing B) (_ : Algebra F B) (r : ℕ),
      _root_.Specs.RM03.CSA.isCentralSimple F B ∧ 0 < r ∧
      Nonempty (A ≃ₐ[F] Matrix (Fin r) (Fin r) B) ∧
      (Nonempty (B ≃ₐ[F] F) ∨ _root_.Specs.RM03.CSA.degree F B = 2)

/-- The real and complex algebra presentations apply to the orthogonal case
since they hold for every central simple algebra over the respective field. -/
def ArchimedeanDivision : Prop :=
  (∀ {A : Type u} [Ring A] [Algebra ℝ A], _root_.Specs.RM03.CSA.isCentralSimple ℝ A →
    ∃ r : ℕ, 0 < r ∧ (Nonempty (A ≃ₐ[ℝ] Matrix (Fin r) (Fin r) ℝ) ∨
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin r) (Fin r) (Quaternion ℝ)))) ∧
  (∀ {A : Type u} [Ring A] [Algebra ℂ A], _root_.Specs.RM03.CSA.isCentralSimple ℂ A →
    ∃ r : ℕ, 0 < r ∧ Nonempty (A ≃ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ))

/-- A skew-Hermitian form on a right module, with the right action represented
by a left module over the opposite ring. -/
structure SkewHermitianPairing {F : Type u} {B V : Type v} [Field F] [Ring B]
    [Algebra F B] [AddCommGroup V] [Module Bᵐᵒᵖ V] (s : Involution F B) where
  value : V → V → B
  add_right : ∀ x y z, value x (y + z) = value x y + value x z
  smul_right : ∀ x y (a : B), value x (MulOpposite.op a • y) = value x y * a
  skew : ∀ x y, value y x = -antiValue s.anti (value x y)
  nondegenerate : ∀ x, x ≠ 0 → ∃ y, value x y ≠ 0

/-- Every isotropic line in a nondegenerate skew-Hermitian space has a
hyperbolic partner when two is invertible. -/
def HyperbolicPartner : Prop :=
  ∀ {F : Type u} {B V : Type v} [Field F] [DivisionRing B] [Algebra F B]
    [AddCommGroup V] [Module Bᵐᵒᵖ V], (2 : F) ≠ 0 →
    ∀ (s : Involution F B) (h : SkewHermitianPairing s) (e : V), e ≠ 0 →
      h.value e e = 0 →
      ∃ f : V, h.value e f = 1 ∧ h.value f e = -1 ∧ h.value f f = 0

section QuadraticPair

variable {R I : Type u} [CommRing R] [Fintype I] [DecidableEq I]

/-- The symmetric hyperbolic Gram matrix, in creation-contraction order. -/
def hyperbolicGram (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] :
    Matrix (I ⊕ I) (I ⊕ I) R := fromBlocks 0 1 1 0

/-- Projection onto the second isotropic summand. -/
def hyperbolicProjection (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] :
    Matrix (I ⊕ I) (I ⊕ I) R := fromBlocks 0 0 0 1

/-- The adjoint for a symmetric Gram matrix which is its own inverse. -/
def adjoint (J X : Matrix I I R) : Matrix I I R := J * X.transpose * J

/-- The value of a matrix bilinear form on the diagonal. -/
def diagonalValue (X : Matrix I I R) (x : I → R) : R := x ⬝ᵥ (X *ᵥ x)

/-- The self-adjoint part for the given Gram matrix. -/
def selfAdjoint (J : Matrix I I R) : Submodule R (Matrix I I R) where
  carrier := {X | adjoint J X = X}
  zero_mem' := by simp [adjoint]
  add_mem' {X Y} hX hY := by
    change adjoint J X = X at hX
    change adjoint J Y = Y at hY
    change adjoint J (X + Y) = X + Y
    simpa [adjoint, mul_add, add_mul] using congrArg₂ (· + ·) hX hY
  smul_mem' a X hX := by
    change adjoint J X = X at hX
    change adjoint J (a • X) = a • X
    simpa [adjoint] using congrArg (a • ·) hX

/-- The semitrace given by the trace pairing against a quadratic lift. -/
def semitrace (J L : Matrix I I R) : selfAdjoint J →ₗ[R] R where
  toFun X := (L * X.val).trace
  map_add' X Y := by change (L * (X.val + Y.val)).trace = _; simp [mul_add]
  map_smul' a X := by change (L * (a • X.val)).trace = _; simp

/-- Matrix conjugation by a unit. -/
def conjugate (g : (Matrix I I R)ˣ) (X : Matrix I I R) : Matrix I I R :=
  g.val * X * g.inv

/-- The full trace-orthogonality calculation over characteristic-two test rings. -/
def TraceOrthogonality : Prop :=
  ∀ {R I : Type u} [CommRing R] [Fintype I] [DecidableEq I], (2 : R) = 0 →
    ∀ (J L : Matrix I I R), J.transpose = J → J * J = 1 →
      ((∀ X : selfAdjoint J, semitrace J L X = 0) ↔
        (∀ x, diagonalValue (J * L) x = 0) ∧
          ∃ a : Matrix I I R, L = a + adjoint J a)

/-- On the split hyperbolic space the canonical lift gives the required
semitrace, independent of the lift having the same quadratic values. -/
def SplitSemitrace : Prop :=
  ∀ (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R], (2 : R) = 0 →
    let J := hyperbolicGram I R
    let L := hyperbolicProjection I R
    let q := OddSpinModels.hyperbolicForm I R
    adjoint J L + L = 1 ∧
    (∀ x, diagonalValue (J * L) x = q x) ∧
    (∀ X : Matrix (I ⊕ I) (I ⊕ I) R,
      ∃ h : X + adjoint J X ∈ selfAdjoint J,
        semitrace J L ⟨X + adjoint J X, h⟩ = X.trace) ∧
    ∀ L' : Matrix (I ⊕ I) (I ⊕ I) R,
      (∀ x, diagonalValue (J * L') x = q x) → semitrace J L' = semitrace J L

/-- Compatibility with the two operations on the split matrix algebra. -/
def PreservesQuadraticPair (J L : Matrix I I R)
    (f : Matrix I I R → Matrix I I R) : Prop :=
  (∀ X, adjoint J (f X) = f (adjoint J X)) ∧
  ∀ X : selfAdjoint J, (L * f X.val).trace = semitrace J L X

/-- The automorphisms of the split quadratic pair, with the matrix-unit
comparison valid over arbitrary characteristic-two test algebras and the
projective description on field points. -/
def ProjectiveSimilitudes : Prop :=
  (∀ (I R : Type u) [Fintype I] [DecidableEq I] [Nonempty I] [CommRing R], (2 : R) = 0 →
    let J := hyperbolicGram I R
    let L := hyperbolicProjection I R
    let q := OddSpinModels.hyperbolicForm I R
    ∀ g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ,
      (PreservesQuadraticPair J L (conjugate g) ↔
        ∃ c : Rˣ, ∀ x, q (g.val *ᵥ x) = (c : R) * q x) ∧
      ((∀ X, conjugate g X = X) ↔
        ∃ c : Rˣ, g.val = algebraMap R (Matrix (I ⊕ I) (I ⊕ I) R) (c : R))) ∧
  ∀ (I K : Type u) [Fintype I] [DecidableEq I] [Nonempty I] [Field K], (2 : K) = 0 →
    let J := hyperbolicGram I K
    let L := hyperbolicProjection I K
    let q := OddSpinModels.hyperbolicForm I K
    ∀ f : Matrix (I ⊕ I) (I ⊕ I) K ≃ₐ[K] Matrix (I ⊕ I) (I ⊕ I) K,
      PreservesQuadraticPair J L f ↔
        ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
          (∀ X, f X = conjugate g X) ∧
          ∀ x, q (g.val *ᵥ x) = (c : K) * q x

end QuadraticPair

section SplitOrthogonalModel

open AlgebraicGeometry CategoryTheory
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.StandardGroups (generalLinearPoints)
open scoped CategoryTheory.MonObj

/-- Isometries of the full hyperbolic quadratic form on a commutative test algebra. -/
def orthogonalMatrices (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] :
    Subgroup (Matrix.GeneralLinearGroup (I ⊕ I) R) where
  carrier := {g | ∀ x, OddSpinModels.hyperbolicForm I R (g.val *ᵥ x) = OddSpinModels.hyperbolicForm I R x}
  one_mem' := by intro x; rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' {g h} hg hh := by
    intro x
    change OddSpinModels.hyperbolicForm I R ((g.val * h.val) *ᵥ x) = _
    rw [← Matrix.mulVec_mulVec, hg (h.val *ᵥ x), hh x]
  inv_mem' {g} hg := by
    intro x
    have h := hg (g.inv *ᵥ x)
    rw [Matrix.mulVec_mulVec, g.val_inv, Matrix.one_mulVec] at h
    exact h.symm

/-- In the split matrix algebra, the unitary equation and preservation of
the pair are precisely the quadratic isometry condition over a test ring. -/
def SplitPairIsometries : Prop :=
  ∀ (I R : Type u) [Fintype I] [DecidableEq I] [Nonempty I] [CommRing R],
    let J := hyperbolicGram I R
    let L := hyperbolicProjection I R
    ∀ g : Matrix.GeneralLinearGroup (I ⊕ I) R,
      g ∈ orthogonalMatrices I R ↔
        adjoint J g.val * g.val = 1 ∧ PreservesQuadraticPair J L (conjugate g)

/-- The full split isometry scheme with the closed inclusion into the general
linear group, specified on all test algebras. -/
structure SplitOrthogonalPresentation (k I : Type u) [Field k] [Fintype I] [DecidableEq I] where
  group : AffineAlgebraicGroup k
  linearGroup : AffineAlgebraicGroup k
  linearPoints : (groupPointsFunctor k).obj linearGroup.val ≅ generalLinearPoints k (I ⊕ I)
  inclusion : group.val ⟶ linearGroup.val
  closed : AlgebraicGeometry.IsClosedImmersion inclusion.hom.hom.left
  points : ∀ R : TestAlgebra k, ((groupPointsFunctor k).obj group.val).obj R ≃*
    orthogonalMatrices I R
  naturality : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (g : ((groupPointsFunctor k).obj group.val).obj R),
    (points S (((groupPointsFunctor k).obj group.val).map f g)).val.val =
      (points R g).val.val.map f.hom
  matrixComparison : ∀ (R : TestAlgebra k) (g : ((groupPointsFunctor k).obj group.val).obj R),
    linearPoints.hom.app R (((groupPointsFunctor k).map inclusion).app R g) = (points R g).val

def SplitOrthogonalModel : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], Nonempty (SplitOrthogonalPresentation k I)

/-- The identity plus a matrix with coefficients in the square-zero ideal. -/
def infinitesimalOrthogonalMatrix {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    (X : Matrix (I ⊕ I) (I ⊕ I) k) : Matrix (I ⊕ I) (I ⊕ I) (DualNumber k) :=
  fun i j => ⟨(1 : Matrix (I ⊕ I) (I ⊕ I) k) i j, X i j⟩

/-- The tangent equation uses alternating matrices with zero diagonal,
including over fields of characteristic two. -/
def SplitOrthogonalTangent : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (X : Matrix (I ⊕ I) (I ⊕ I) k),
    let q := OddSpinModels.hyperbolicForm I (DualNumber k)
    let Y := hyperbolicGram I k * X
    (∀ x, q (infinitesimalOrthogonalMatrix X *ᵥ x) = q x) ↔
      (∀ i, Y i i = 0) ∧ Y + Y.transpose = 0

/-- The orthogonal tangent matrices in the hyperbolic basis, and the action
of the diagonal torus on the three independent blocks. -/
def SplitOrthogonalTangentBlocks : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (X : Matrix (I ⊕ I) (I ⊕ I) k),
    let q := OddSpinModels.hyperbolicForm I (DualNumber k)
    ((∀ x, q (infinitesimalOrthogonalMatrix X *ᵥ x) = q x) ↔
      X.toBlocks₂₂ = -X.toBlocks₁₁.transpose ∧
        (∀ i, X.toBlocks₁₂ i i = 0) ∧ (∀ i j, X.toBlocks₁₂ i j = - X.toBlocks₁₂ j i) ∧
        (∀ i, X.toBlocks₂₁ i i = 0) ∧ (∀ i j, X.toBlocks₂₁ i j = - X.toBlocks₂₁ j i)) ∧
    ∀ (R : Type u) [CommRing R] [Algebra k R] (t : I → Rˣ),
      let T := Specs.SymplecticMatrixStructure.hyperbolicDiagonal t
      let T' := Specs.SymplecticMatrixStructure.hyperbolicDiagonal (fun i => (t i)⁻¹)
      let Y := T * X.map (algebraMap k R) * T'
      ∀ i j,
        Y.toBlocks₁₁ i j = (t i : R) * (↑(t j)⁻¹ : R) * algebraMap k R (X.toBlocks₁₁ i j) ∧
        Y.toBlocks₁₂ i j = (t i : R) * (t j : R) * algebraMap k R (X.toBlocks₁₂ i j) ∧
        Y.toBlocks₂₁ i j = (↑(t i)⁻¹ : R) * (↑(t j)⁻¹ : R) * algebraMap k R (X.toBlocks₂₁ i j)

/-- The involution on the named coordinate lattice induced by interchanging
one hyperbolic pair. -/
def invertCoordinate {I : Type u} [DecidableEq I] (i : I) (v : I → ℤ) : I → ℤ :=
  fun j => if j = i then -v j else v j

/-- A switch of the two vectors in one hyperbolic plane inverts its torus
coordinate. For the last plane this interchanges the two end roots of the
type-D diagram while preserving the other simple roots. -/
def VectorDiagramSwitch : Prop :=
  (∀ (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] (i : I),
    ∃ g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ, g * g = 1 ∧
      (∀ x, g.val *ᵥ x = x ∘ Equiv.swap (Sum.inl i) (Sum.inr i)) ∧
      g ∈ orthogonalMatrices I R ∧
      ∀ t : I → Rˣ, conjugate g (SymplecticMatrixStructure.hyperbolicDiagonal t) =
        SymplecticMatrixStructure.hyperbolicDiagonal (fun j => if j = i then (t j)⁻¹ else t j)) ∧
  ∀ (I : Type u) [DecidableEq I] (i j l : I),
    (i ≠ j → i ≠ l → invertCoordinate i (coordinateVector I j - coordinateVector I l) =
      coordinateVector I j - coordinateVector I l) ∧
    (j ≠ i →
      invertCoordinate i (coordinateVector I j - coordinateVector I i) =
        coordinateVector I j + coordinateVector I i ∧
      invertCoordinate i (coordinateVector I j + coordinateVector I i) =
        coordinateVector I j - coordinateVector I i)

open _root_.LinearAlgebraicGroups.Albert.SpinSpecification
  (IsSpinPointRepresentation IsVectorAction ScalarClifford muTwoUnderlying)
open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup IsSchemeKernel)

/-- The split vector morphism onto its closed image, retaining the scheme
kernel as the scalar copy of `μ₂` even in characteristic two. -/
structure SplitSpinVectorImage (k I : Type u) [Field k] [Fintype I] [DecidableEq I] where
  orthogonal : SplitOrthogonalPresentation k I
  spin : AffineAlgebraicGroup k
  spinPoints : ∀ R : TestAlgebra k, Points spin.val.X R →*
    (ScalarClifford (OddSpinModels.hyperbolicForm I k) R)ˣ
  spinRepresents : IsSpinPointRepresentation (OddSpinModels.hyperbolicForm I k) spin.val spinPoints
  image : AffineAlgebraicGroup k
  projection : spin.val ⟶ image.val
  inclusion : image.val ⟶ orthogonal.group.val
  closed : IsClosedImmersion inclusion.hom.hom.left
  finite : IsFinite projection.hom.hom.left
  flat : Flat projection.hom.hom.left
  surjective : Surjective projection.hom.hom.left
  kernel : ClosedSubgroup spin.val
  isKernel : IsSchemeKernel projection kernel
  kernelScheme : kernel.group.X = muTwoUnderlying k
  kernelPoints : ∀ R : TestAlgebra k, Points kernel.group.X R ≃* rootsOfUnity 2 R
  scalar : ∀ (R : TestAlgebra k) (a : Points kernel.group.X R),
    (spinPoints R (a ≫ kernel.inclusion.hom.hom)).val = algebraMap R _ (kernelPoints R a).val.val
  central : ∀ (R : TestAlgebra k) (a : Points kernel.group.X R) (b : Points spin.val.X R),
    Commute (a ≫ kernel.inclusion.hom.hom) b
  vector : ∀ (R : TestAlgebra k) (a : Points spin.val.X R),
    ∃ g : (R ⊗[k] (I ⊕ I → k)) ≃ₗ[R] (R ⊗[k] (I ⊕ I → k)),
      IsVectorAction (OddSpinModels.hyperbolicForm I k) R (spinPoints R a) g ∧
      let b := (Pi.basisFun k (I ⊕ I)).baseChange R
      let v := ((groupPointsFunctor k).map (projection ≫ inclusion)).app R a
      LinearMap.toMatrix b b g.toLinearMap = (orthogonal.points R v).val.val

def SplitSpinImage : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    Nonempty (SplitSpinVectorImage k I)

open _root_.LinearAlgebraicGroups.Albert.SplitSpinSpecification
  (PairIndex HasActionMatrix PreservesNorm integralForm)

/-- The actual Clifford fiber over a split isometry, over any test ring. -/
abbrev SpinVectorFiber (m : ℕ) (R : Type u) [CommRing R] [Algebra ℤ R]
    (M : Matrix (PairIndex m) (PairIndex m) R) :=
  {a : (ScalarClifford (integralForm m) R)ˣ //
    a ∈ _root_.LinearAlgebraicGroups.Albert.SpinSpecification.spinUnits (integralForm m) R ∧
    HasActionMatrix m a M}

/-- On the standard orthogonal chart, the lifted scalar has equation
`u² det(A) = 1`. The norm-one lift exists fppf locally in every characteristic. -/
def SpinChartFibers : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (R : Type u) [CommRing R] [Algebra ℤ R]
    (M : Matrix (PairIndex m) (PairIndex m) R), PreservesNorm M → IsUnit M.toBlocks₁₁.det →
    Nonempty ({u' : Rˣ // (u' : R) ^ 2 * M.toBlocks₁₁.det = 1} ≃ SpinVectorFiber m R M) ∧
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra ℤ A),
      IsScalarTower ℤ R A ∧ Module.Free R A ∧ Module.Finite R A ∧
      Module.FaithfullyFlat R A ∧ Algebra.FinitePresentation R A ∧
      Nonempty (SpinVectorFiber m A (M.map (algebraMap R A)))

/-- The integral hyperbolic chart and the field model describe the same Clifford
points, with vector matrices reindexed by the chosen hyperbolic basis. -/
def SplitSpinIntegralComparison : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
    (m : ℕ) (d : Fin m ≃ I) (R : Type u) [CommRing R] [Algebra k R],
    let q := OddSpinModels.hyperbolicForm I k
    let b := (Pi.basisFun k (I ⊕ I)).baseChange R
    ∃ e : ScalarClifford (integralForm m) R ≃ₐ[R] ScalarClifford q R,
      ∀ a : (ScalarClifford (integralForm m) R)ˣ,
        let z := Units.map e.toMonoidHom a
        (z ∈ _root_.LinearAlgebraicGroups.Albert.SpinSpecification.spinUnits q R ↔
          a ∈ _root_.LinearAlgebraicGroups.Albert.SpinSpecification.spinUnits (integralForm m) R) ∧
        ∀ M : Matrix (PairIndex m) (PairIndex m) R,
          HasActionMatrix m a M ↔
            ∃ g : (R ⊗[k] (I ⊕ I → k)) ≃ₗ[R] (R ⊗[k] (I ⊕ I → k)),
              IsVectorAction q R z g ∧
                LinearMap.toMatrix b b g.toLinearMap = Matrix.reindex (d.sumCongr d) (d.sumCongr d) M

/-- The standard open orthogonal chart lies in the scheme image of the vector
projection. The factorization is over the original test algebra. -/
def SplitSpinChartInImage : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ (P : SplitSpinVectorImage k I) (R : TestAlgebra k) (a : Points P.orthogonal.group.val.X R),
      IsUnit (P.orthogonal.points R a).val.val.toBlocks₁₁.det →
      ∃ c : Points P.image.val.X R, c ≫ P.inclusion.hom.hom = a

/-- The image of the split vector projection is an open and closed subgroup
of the full quadratic isometry group, including in characteristic two. -/
def SplitSpinOpenImage : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ P : SplitSpinVectorImage k I, IsOpenImmersion P.inclusion.hom.hom.left

/-- The split spin vector image is geometrically connected and identifies,
as an open and closed subscheme, with the neutral component of the full
quadratic isometry group. -/
def SplitSpinIdentityComponent : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ P : SplitSpinVectorImage k I,
      GeometricallyConnected P.image.val.X.hom ∧ Set.range P.inclusion.hom.hom.left =
        connectedComponent (η[P.orthogonal.group.val.X].left
          (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))))

/-- In characteristic different from two, the neutral component is the
determinant-one quadratic isometry subgroup on every test algebra. -/
def SplitSpinDeterminant : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I → (2 : k) ≠ 0 →
    ∀ (P : SplitSpinVectorImage k I) (R : TestAlgebra k) (a : Points P.orthogonal.group.val.X R),
      (P.orthogonal.points R a).val.val.det = 1 ↔
        ∃ b : Points P.image.val.X R, b ≫ P.inclusion.hom.hom = a

end SplitOrthogonalModel

/-- The multiplier-corrected action on the even Clifford algebra.
The equation on pairs determines the action on products of any even length. -/
def EvenCliffordSimilitude : Prop :=
  ∀ {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (q : QuadraticForm R M) (g : M ≃ₗ[R] M) (c : Rˣ),
    (∀ x, q (g x) = (c : R) * q x) →
    ∃ e : CliffordAlgebra.even q ≃ₐ[R] CliffordAlgebra.even q,
      (∀ x y, e ((CliffordAlgebra.even.ι q).bilin x y) =
        (↑c⁻¹ : R) • (CliffordAlgebra.even.ι q).bilin (g x) (g y)) ∧
      (∀ x : CliffordAlgebra.even q, ∀ h :
        CliffordAlgebra.reverse (x : CliffordAlgebra q) ∈ CliffordAlgebra.even q,
        (e ⟨CliffordAlgebra.reverse x.val, h⟩ : CliffordAlgebra q) =
          CliffordAlgebra.reverse (e x : CliffordAlgebra q))

/-- The multiplier-corrected even Clifford action intertwines the vector action
of an even implementer, as an identity over every commutative test ring. -/
def EvenCliffordVectorAction : Prop :=
  ∀ {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (q : QuadraticForm R M) (g : M ≃ₗ[R] M) (c : Rˣ), (∀ x, q (g x) = (c : R) * q x) →
    ∀ e : CliffordAlgebra.even q →ₐ[R] CliffordAlgebra.even q,
      (∀ x y, e ((CliffordAlgebra.even.ι q).bilin x y) =
        (↑c⁻¹ : R) • (CliffordAlgebra.even.ι q).bilin (g x) (g y)) →
      ∀ (a : CliffordAlgebra.even q) (x y : M),
        (a : CliffordAlgebra q) * CliffordAlgebra.ι q x =
          CliffordAlgebra.ι q y * (a : CliffordAlgebra q) →
        (e a : CliffordAlgebra q) * CliffordAlgebra.ι q (g x) =
          CliffordAlgebra.ι q (g y) * (e a : CliffordAlgebra q)

section CliffordAction

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Quadratic similitudes with their specified invertible multipliers. -/
def quadraticSimilitudes (q : QuadraticForm R M) : Subgroup ((M ≃ₗ[R] M) × Rˣ) where
  carrier := {g | ∀ x, q (g.1 x) = (g.2 : R) * q x}
  one_mem' := by intro x; exact (one_mul (q x)).symm
  mul_mem' {g h} hg hh := by
    intro x
    change q (g.1 (h.1 x)) = ((g.2 * h.2 : Rˣ) : R) * q x
    rw [hg (h.1 x), hh x, Units.val_mul, mul_assoc]
  inv_mem' {g} hg := by
    intro x
    change q (g.1.symm x) = (↑g.2⁻¹ : R) * q x
    rw [← g.1.apply_symm_apply x, hg (g.1.symm x), ← mul_assoc, Units.inv_mul, one_mul]
    simp

/-- The graph of the vector action of an even Clifford unit in the full algebra. -/
def ImplementsIsometry (q : QuadraticForm R M) (a : (CliffordAlgebra.even q)ˣ)
    (g : M ≃ₗ[R] M) : Prop :=
  ∀ x, (a.val : CliffordAlgebra q) * CliffordAlgebra.ι q x =
    CliffordAlgebra.ι q (g x) * (a.val : CliffordAlgebra q)

/-- Functoriality and scalar independence of the similitude action. The inner
action and the graph of the spin vector map are compatible with the same action. -/
def CliffordSimilitudeAction : Prop :=
  ∀ {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (q : QuadraticForm R M),
    ∃ C : quadraticSimilitudes q →* (CliffordAlgebra.even q ≃ₐ[R] CliffordAlgebra.even q),
      (∀ g x y, C g ((CliffordAlgebra.even.ι q).bilin x y) =
        (↑g.val.2⁻¹ : R) • (CliffordAlgebra.even.ι q).bilin (g.val.1 x) (g.val.1 y)) ∧
      (∀ (g h : quadraticSimilitudes q) (s : Rˣ),
        (∀ x, g.val.1 x = (s : R) • h.val.1 x) → g.val.2 = s ^ 2 * h.val.2 → C g = C h) ∧
      (∀ (g : quadraticSimilitudes q) (a : (CliffordAlgebra.even q)ˣ),
        g.val.2 = 1 → ImplementsIsometry q a g.val.1 →
        ∀ z, C g z = a.val * z * a.inv) ∧
      ∀ (g : quadraticSimilitudes q) (a : (CliffordAlgebra.even q)ˣ) (h : M ≃ₗ[R] M),
        CliffordAlgebra.reverse (a.val : CliffordAlgebra q) * (a.val : CliffordAlgebra q) = 1 →
        ImplementsIsometry q a h →
        let b := Units.map (C g).toMonoidHom a
        CliffordAlgebra.reverse (b.val : CliffordAlgebra q) * (b.val : CliffordAlgebra q) = 1 ∧
          ImplementsIsometry q b (g.val.1 * h * g.val.1⁻¹)

/-- The formula for even Clifford similitudes commutes with scalar extension
on the canonical maps induced by the vector inclusion. -/
def CliffordSimilitudeBaseChange : Prop :=
  ∀ {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] {I : Type u} [LinearOrder I]
    (q : QuadraticForm R M) (b : Module.Basis I R M) (S : Type u) [CommRing S] [Algebra R S],
    let Q := _root_.LinearAlgebraicGroups.Albert.CliffordSpecification.coefficientForm S q b
    ∃ J : CliffordAlgebra.even q →ₐ[R] CliffordAlgebra.even Q,
      (∀ x y, J ((CliffordAlgebra.even.ι q).bilin x y) =
        (CliffordAlgebra.even.ι Q).bilin (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) ∧
      ∀ g : quadraticSimilitudes q,
        let h := LinearEquiv.baseChange R S M M g.val.1
        let c := Units.map (algebraMap R S).toMonoidHom g.val.2
        (∀ x, Q (h x) = (c : S) * Q x) ∧
        ∀ (f : CliffordAlgebra.even q →ₐ[R] CliffordAlgebra.even q)
          (F : CliffordAlgebra.even Q →ₐ[S] CliffordAlgebra.even Q),
          (∀ x y, f ((CliffordAlgebra.even.ι q).bilin x y) =
            (↑g.val.2⁻¹ : R) • (CliffordAlgebra.even.ι q).bilin (g.val.1 x) (g.val.1 y)) →
          (∀ x y, F ((CliffordAlgebra.even.ι Q).bilin x y) =
            (↑c⁻¹ : S) • (CliffordAlgebra.even.ι Q).bilin (h x) (h y)) →
          ∀ z, J (f z) = F (J z)

/-- Scalar extension of the multiplier-corrected action preserves the
intrinsic spin points and intertwines the actual vector action. The action
on the scalar-extended even algebra commutes with every test-algebra map. -/
def SpinSimilitudeScalarExtension : Prop :=
  ∀ {k M I : Type u} [Field k] [AddCommGroup M] [Module k M] [LinearOrder I]
    (q : QuadraticForm k M) (_b : Module.Basis I k M),
    ∃ C : quadraticSimilitudes q →* (CliffordAlgebra.even q ≃ₐ[k] CliffordAlgebra.even q),
      (∀ g x y, C g ((CliffordAlgebra.even.ι q).bilin x y) =
        (↑g.val.2⁻¹ : k) • (CliffordAlgebra.even.ι q).bilin (g.val.1 x) (g.val.1 y)) ∧
      (∀ (S : Type u) [CommRing S] [Algebra k S],
        let j : (S ⊗[k] CliffordAlgebra.even q) →ₐ[S] S ⊗[k] CliffordAlgebra q :=
          Algebra.TensorProduct.map (AlgHom.id S S) (CliffordAlgebra.even q).val
        Function.Injective j ∧
        (∀ a : (S ⊗[k] CliffordAlgebra q)ˣ,
          a ∈ _root_.LinearAlgebraicGroups.Albert.SpinSpecification.spinUnits q S →
          ∃ z : (S ⊗[k] CliffordAlgebra.even q)ˣ, Units.map j.toMonoidHom z = a) ∧
        ∀ (g : quadraticSimilitudes q) (a : (S ⊗[k] CliffordAlgebra.even q)ˣ)
          (h : (S ⊗[k] M) ≃ₗ[S] (S ⊗[k] M)),
          let gS := LinearEquiv.baseChange k S M M g.val.1
          let aS := Units.map j.toMonoidHom a
          let f := Algebra.TensorProduct.map (AlgHom.id S S) (C g).toAlgHom
          let aS' := Units.map j.toMonoidHom (Units.map f.toMonoidHom a)
          aS ∈ _root_.LinearAlgebraicGroups.Albert.SpinSpecification.spinUnits q S →
          _root_.LinearAlgebraicGroups.Albert.SpinSpecification.IsVectorAction q S aS h →
          aS' ∈ _root_.LinearAlgebraicGroups.Albert.SpinSpecification.spinUnits q S ∧
            _root_.LinearAlgebraicGroups.Albert.SpinSpecification.IsVectorAction q S aS' (gS * h * gS⁻¹)) ∧
      ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
        (f : S →ₐ[k] T) (g : quadraticSimilitudes q) (z : S ⊗[k] CliffordAlgebra.even q),
        let f₀ := Algebra.TensorProduct.map f (AlgHom.id k (CliffordAlgebra.even q))
        f₀ (Algebra.TensorProduct.map (AlgHom.id S S) (C g).toAlgHom z) =
          Algebra.TensorProduct.map (AlgHom.id T T) (C g).toAlgHom (f₀ z)


end CliffordAction

section ProjectiveCliffordAction

variable {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]

/-- Matrix conjugation as an algebra automorphism. -/
def matrixInner (g : (Matrix I I R)ˣ) : Matrix I I R ≃ₐ[R] Matrix I I R where
  toFun := conjugate g
  invFun := conjugate g⁻¹
  left_inv X := by simp [conjugate, mul_assoc]
  right_inv X := by simp [conjugate, mul_assoc]
  map_mul' X Y := by simp [conjugate, mul_assoc]
  map_add' X Y := by simp [conjugate, add_mul, mul_add]
  commutes' r := by
    change g.val * algebraMap R (Matrix I I R) r * g.inv = _
    rw [← Algebra.commutes, mul_assoc, g.val_inv, mul_one]

/-- The linear automorphism represented by an invertible matrix on columns. -/
def matrixColumnEquiv : (Matrix I I R)ˣ ≃* ((I → R) ≃ₗ[R] (I → R)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R (I → R))

/-- Projective action of a quadratic similitude on the split matrix algebra. -/
def projectiveMatrixAction (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] :
    quadraticSimilitudes (OddSpinModels.hyperbolicForm I R) →*
      (Matrix (I ⊕ I) (I ⊕ I) R ≃ₐ[R] Matrix (I ⊕ I) (I ⊕ I) R) where
  toFun d := matrixInner (matrixColumnEquiv.symm d.val.1)
  map_one' := by
    apply AlgEquiv.ext
    intro X
    change matrixInner (matrixColumnEquiv.symm 1) X = X
    rw [map_one]
    simp [matrixInner, conjugate]
  map_mul' d e := by
    apply AlgEquiv.ext
    intro X
    change matrixInner (matrixColumnEquiv.symm (d.val.1 * e.val.1)) X =
      matrixInner (matrixColumnEquiv.symm d.val.1) (matrixInner (matrixColumnEquiv.symm e.val.1) X)
    rw [map_mul]
    simp [matrixInner, conjugate, mul_assoc]

/-- The action on the even Clifford algebra factors through the automorphisms
of the split pair over the splitting field. It respects reversion and has
the multiplier formula on pairs of vectors. -/
def ProjectiveCliffordAction : Prop :=
  ∀ (I K : Type u) [Fintype I] [DecidableEq I] [Nonempty I] [Field K],
    let q := OddSpinModels.hyperbolicForm I K
    let P := projectiveMatrixAction I K
    (∀ f, f ∈ P.range ↔ PreservesQuadraticPair (hyperbolicGram I K) (hyperbolicProjection I K) f) ∧
    ∃ C : P.range →* (CliffordAlgebra.even q ≃ₐ[K] CliffordAlgebra.even q),
      (∀ g x y, C (P.rangeRestrict g) ((CliffordAlgebra.even.ι q).bilin x y) =
        (↑g.val.2⁻¹ : K) • (CliffordAlgebra.even.ι q).bilin (g.val.1 x) (g.val.1 y)) ∧
      ∀ (a : P.range) (z : CliffordAlgebra.even q) (h :
          CliffordAlgebra.reverse z.val ∈ CliffordAlgebra.even q),
        (C a ⟨CliffordAlgebra.reverse z.val, h⟩ : CliffordAlgebra q) =
          CliffordAlgebra.reverse (C a z : CliffordAlgebra q)

open CategoryTheory
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification (IsVectorAction)

/-- Projective quadratic similitudes act on the actual split spin scheme.
The action is given by scalar extension of the even Clifford automorphism,
conjugates the vector action, and fixes the scalar scheme kernel. -/
def SplitProjectiveSpinAction : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [Nonempty I]
    (P : SplitSpinVectorImage k I),
    let form := OddSpinModels.hyperbolicForm I k
    ∃ C : quadraticSimilitudes form →* (CliffordAlgebra.even form ≃ₐ[k] CliffordAlgebra.even form),
      ∃ A : quadraticSimilitudes form → (P.spin.val ≅ P.spin.val),
        (∀ g h, projectiveMatrixAction I k g = projectiveMatrixAction I k h → A g = A h) ∧
        (∀ g h, (A (g * h)).hom = (A h).hom ≫ (A g).hom) ∧
        (∀ g x y, C g ((CliffordAlgebra.even.ι form).bilin x y) =
          (↑g.val.2⁻¹ : k) • (CliffordAlgebra.even.ι form).bilin (g.val.1 x) (g.val.1 y)) ∧
        (∀ (R : TestAlgebra k) (g : quadraticSimilitudes form) (a : Points P.spin.val.X R)
          (z : (R ⊗[k] CliffordAlgebra.even form)ˣ),
          let j := Algebra.TensorProduct.map (AlgHom.id R R) (CliffordAlgebra.even form).val
          let f := Algebra.TensorProduct.map (AlgHom.id R R) (C g).toAlgHom
          Units.map j.toMonoidHom z = P.spinPoints R a →
          P.spinPoints R (a ≫ (A g).hom.hom.hom) = Units.map j.toMonoidHom (Units.map f.toMonoidHom z)) ∧
        (∀ (R : TestAlgebra k) (g : quadraticSimilitudes form) (a : Points P.spin.val.X R)
          (h : (R ⊗[k] (I ⊕ I → k)) ≃ₗ[R] (R ⊗[k] (I ⊕ I → k))),
          let gR := LinearEquiv.baseChange k R (I ⊕ I → k) (I ⊕ I → k) g.val.1
          IsVectorAction form R (P.spinPoints R a) h →
          IsVectorAction form R (P.spinPoints R (a ≫ (A g).hom.hom.hom)) (gR * h * gR⁻¹)) ∧
        ∀ (R : TestAlgebra k) (g : quadraticSimilitudes form) (a : Points P.kernel.group.X R),
          (a ≫ P.kernel.inclusion.hom.hom) ≫ (A g).hom.hom.hom = a ≫ P.kernel.inclusion.hom.hom

end ProjectiveCliffordAction

section OrthogonalModel

open SymplecticDivisionForms (extendAnti dagger hermitianValue intoTensor tensorMap)

/-- Adjoint to an invertible Gram matrix. -/
def gramAdjoint {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (H : (Matrix I I R)ˣ) (X : Matrix I I R) : Matrix I I R :=
  H.inv * X.transpose * H.val

/-- Orthogonal type in characteristic different from two, tested over an
algebraic closure by the adjoint of a nonsingular symmetric matrix. -/
def IsOrthogonal {F A : Type u} [Field F] [Ring A] [Algebra F A]
    (s : Involution F A) : Prop :=
  ∃ (d : ℕ) (e : (AlgebraicClosure F ⊗[F] A) ≃ₐ[AlgebraicClosure F]
      Matrix (Fin d) (Fin d) (AlgebraicClosure F))
      (G : (Matrix (Fin d) (Fin d) (AlgebraicClosure F))ˣ),
    G.val.transpose = G.val ∧
    ∀ x, e (antiValue (extendAnti s.anti (AlgebraicClosure F)) x) = gramAdjoint G (e x)

/-- A split orthogonal involution is the adjoint of the polar form of a
regular quadratic form over the ground field. -/
def FieldOrthogonalModel : Prop :=
  ∀ {F A : Type u} [Field F] [Ring A] [Algebra F A] (r : ℕ), (2 : F) ≠ 0 →
    _root_.Specs.RM03.CSA.isCentralSimple F A →
    ∀ (s : Involution F A), IsOrthogonal s →
    ∀ (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F),
      ∃ (H : (Matrix (Fin r) (Fin r) F)ˣ)
        (q : QuadraticForm F (Fin r → F)),
        H.val.transpose = H.val ∧
        q.polarBilin = Matrix.toLinearMap₂' F H.val ∧ q.polarBilin.Nondegenerate ∧
        ∀ x, e (antiValue s.anti x) = gramAdjoint H (e x)

open _root_.LinearAlgebraicGroups.QuaternionHermitianCocharacters
  (isometryPoints multiplicativePoints pairing)

/-- The quaternionic model for an orthogonal involution, with its isometry
equations after scalar extension and a hyperbolic pair from split isotropy. -/
def QuaternionSkewModel : Prop :=
  ∀ {F A B : Type u} [Field F] [Ring A] [Algebra F A] [DivisionRing B] [Algebra F B]
    (r : ℕ), (2 : F) ≠ 0 → _root_.Specs.RM03.CSA.isCentralSimple F A →
    ∀ (s : Involution F A), IsOrthogonal s →
    ∀ (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
      _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B),
      ∃ (b : Involution F B) (H : (Matrix (Fin r) (Fin r) B)ˣ),
        (∀ x, antiValue b.anti x = SymplecticInvolutionModels.quaternionConjugate hB x) ∧
        dagger b.anti H.val = -H.val ∧
        (∀ x, e (antiValue s.anti x) = H.inv * dagger b.anti (e x) * H.val) ∧
        (∃ h : SkewHermitianPairing b, h.value = hermitianValue b.anti H.val) ∧
        (∃ E : ∀ (R : Type u) [CommRing R] [Algebra F R],
            (R ⊗[F] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[F] B),
          (∀ (R : Type u) [CommRing R] [Algebra F R] (x : A),
            E R (1 ⊗ₜ[F] x) = (e x).map (intoTensor R B)) ∧
          (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
            (f : R →ₐ[F] S) (x : R ⊗[F] A), E S (tensorMap A f x) = (E R x).map (tensorMap B f)) ∧
          ∀ (R : Type u) [CommRing R] [Algebra F R] (g : (R ⊗[F] A)ˣ),
            antiValue (extendAnti s.anti R) g.val * g.val = 1 ↔
              let h := hermitianValue (extendAnti b.anti R) (H.val.map (intoTensor R B))
              ∀ x y, h (E R g.val *ᵥ x) (E R g.val *ᵥ y) = h x y) ∧
        ∀ (cochar : multiplicativePoints.{u,u} F ⟶ isometryPoints b.anti.toAlgHom H.val),
          (¬ ∀ R t, cochar.app R t = 1) →
          ∃ x y : Fin r → B, x ≠ 0 ∧
            hermitianValue b.anti H.val x x = 0 ∧
            hermitianValue b.anti H.val x y = 1 ∧
            hermitianValue b.anti H.val y x = -1 ∧
            hermitianValue b.anti H.val y y = 0

end OrthogonalModel

section QuadraticPairDescent

open RM03.Brauer.SemilinearDescent (AlgebraAction)

variable {k K I : Type u} [Field k] [Field K] [Algebra k K]
  [Fintype I] [DecidableEq I]

/-- The self-adjoint submodule for a first-kind involution. -/
def symmetricPart {A : Type u} [Ring A] [Algebra k A] (s : _root_.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent.Involution k A) :
    Submodule k A :=
  LinearMap.ker (s.toLinearMap - LinearMap.id)

variable (ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K))

/-- Descent of the involution and semitrace from the split matrix algebra.
The formulas on fixed elements determine the maps under scalar extension. -/
structure DescendedQuadraticPair where
  centralSimple : _root_.Specs.RM03.CSA.isCentralSimple k ρ.fixedSubalgebra
  degree : _root_.Specs.RM03.CSA.degree k ρ.fixedSubalgebra = 2 * Fintype.card I
  involution : _root_.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent.Involution k ρ.fixedSubalgebra
  semitrace : symmetricPart involution →ₗ[k] k
  involutionFormula : ∀ x : ρ.fixedSubalgebra,
    (involution.toLinearMap x).val = adjoint (hyperbolicGram I K) x.val
  semitraceFormula : ∀ x : symmetricPart involution,
    algebraMap k K (semitrace x) = (hyperbolicProjection I K * x.val.val).trace
  semitraceIdentity : ∀ x : ρ.fixedSubalgebra, ∃ h : x + involution.toLinearMap x ∈ symmetricPart involution,
    semitrace ⟨_, h⟩ = -(_root_.Specs.RM03.CSA.reducedCharpoly centralSimple x).coeff
      (_root_.Specs.RM03.CSA.degree k ρ.fixedSubalgebra - 1)
  splitting : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K] Matrix (I ⊕ I) (I ⊕ I) K
  splittingFormula : ∀ (a : K) (x : ρ.fixedSubalgebra), splitting (a ⊗ₜ[k] x) = a • x.val
  splittingInvolution : ∀ x,
    splitting ((involution.baseChange K).toLinearMap x) =
      adjoint (hyperbolicGram I K) (splitting x)

/-- A semilinear descent action induced by quadratic similitudes descends
the split hyperbolic pair to a central simple algebra with quadratic pair. -/
def QuadraticPairDescent : Prop :=
  ∀ (k K I : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I],
    ∀ (ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)),
      (∀ a : Gal(K/k), ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
        (∀ X, ρ.act a X = conjugate g (X.map a)) ∧
        ∀ x, OddSpinModels.hyperbolicForm I K (g.val *ᵥ x) =
          (c : K) * OddSpinModels.hyperbolicForm I K x) →
      Nonempty (DescendedQuadraticPair ρ)

/-- The descended involution in characteristic different from two is orthogonal. -/
def OrthogonalInvolutionDescent : Prop :=
  ∀ (k K I : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I], (2 : k) ≠ 0 →
    ∀ (ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)),
      (∀ a : Gal(K/k), ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
        (∀ X, ρ.act a X = conjugate g (X.map a)) ∧
        ∀ x, OddSpinModels.hyperbolicForm I K (g.val *ᵥ x) =
          (c : K) * OddSpinModels.hyperbolicForm I K x) →
      ∃ D : DescendedQuadraticPair ρ,
        IsOrthogonal (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution D.involution)

/-- The matrix comparison after splitting recovers both the involution and the
semitrace on every commutative algebra over the splitting field. -/
def QuadraticPairScalarExtension : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)} (D : DescendedQuadraticPair ρ)
    (S : Type u) [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S],
    ∃ E : (S ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S,
      (∀ (r : S) (x : ρ.fixedSubalgebra), E (r ⊗ₜ[k] x) = r • x.val.map (algebraMap K S)) ∧
      (∀ x, E ((D.involution.baseChange S).toLinearMap x) = adjoint (hyperbolicGram I S) (E x)) ∧
      ∃ Eσ : (S ⊗[k] symmetricPart D.involution) ≃ₗ[S] selfAdjoint (hyperbolicGram I S),
        (∀ t, (Eσ t).val = E ((symmetricPart D.involution).subtype.baseChange S t)) ∧
        ∀ t, semitrace (hyperbolicGram I S) (hyperbolicProjection I S) (Eσ t) =
          TensorProduct.AlgebraTensorModule.rid k S S (D.semitrace.baseChange S t)

end QuadraticPairDescent

section TypeDModels

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open Pinning (AttachedDatum PinnedGroup SplitBorelPair)
open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open RelativeFormComparison (fieldTest transportedAut)
open CharacterDescent (Cocharacter)

/-- A vector vertex is fixed by the diagram action induced by a splitting
isomorphism. For `D₄` one may mark any fixed outer vertex. -/
def HasFixedVectorVertex {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (n : ℕ) : Prop :=
  ∃ (L : RootGroups.AdditiveLine k) (P : PinnedGroup L)
    (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P)
    (Q : AdjointQuotient P.pair.G) (E : SplitSequence P D l Q)
    (e : (groupBaseChange k (SeparableClosure k)).obj P.pair.G.val ≅
      (groupBaseChange k (SeparableClosure k)).obj G.val)
    (r : relativePoints P.pair.G.val (fieldTest k (SeparableClosure k)) ≅
      relativePoints G.val (fieldTest k (SeparableClosure k)))
    (simple : Fin n ≃ ↥D.toBased.base.support) (i : Fin n),
    RelativeFormComparison.IsInduced k (SeparableClosure k) e r ∧
    (∀ a b, D.toBased.datum.pairing (simple b).val (simple a).val = CartanMatrix.D n a b) ∧
    (if n = 4 then i.val ≠ 1 else i.val = 0) ∧
    ∀ σ : Gal(SeparableClosure k/k),
      ((QuasiSplitInnerForms.outerHom (S := SeparableClosure k) E)
        (transportedAut k (SeparableClosure k) r σ)).asIso.hom.val.indexEquiv
        (simple i).val = (simple i).val

/-- The simple coroots in the standard hyperbolic coordinates of type `Dₙ`. -/
def simpleDCoroot (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : ULift.{u} (Fin n) → ℤ :=
  if h : i.val + 1 < n then
    coordinateVector _ (ULift.up i) - coordinateVector _ (ULift.up ⟨i.val + 1, h⟩)
  else
    coordinateVector _ (ULift.up (⟨n - 2, by omega⟩ : Fin n)) +
      coordinateVector _ (ULift.up (⟨n - 1, by omega⟩ : Fin n))

/-- The full inverse image of the diagonal vector torus is a geometrically
maximal split torus. Its cocharacters have the even-sum exponents on the
hyperbolic planes. -/
def SplitSpinDiagonalTorus : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [Nonempty I]
    (P : SplitSpinVectorImage k I),
    ∃ (T : ClosedSubgroup P.spin.val) (comm : IsCommMonObj T.group.X),
      GeometricRadicals.IsSplitTorus T.group ∧
      RankOneFlag.IsGeometricallyMaximal T ∧
      (∀ (R : TestAlgebra k) (a : Points P.spin.val.X R),
        (∃ b : Points T.group.X R, b ≫ T.inclusion.hom.hom = a) ↔
          ∃ t : I → Rˣ,
            (P.orthogonal.points R (a ≫ (P.projection ≫ P.inclusion).hom.hom)).val.val =
              SymplecticMatrixStructure.hyperbolicDiagonal t) ∧
      letI := comm
      ∃ v : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSum I,
        ∀ (R : TestAlgebra k) (s : Rˣ) (c : Cocharacter T.group),
          let a := _root_.LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint c R s
          (P.orthogonal.points R (a ≫ (T.inclusion ≫ P.projection ≫ P.inclusion).hom.hom)).val.val =
            SymplecticMatrixStructure.hyperbolicDiagonal (fun i => s ^ (v (Additive.ofMul c)).val i)

/-- Centrality of the scalar kernel on all test algebras gives scheme centrality. -/
def SplitSpinCentralIsogeny : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    (P : SplitSpinVectorImage k I), CentralIsogenies.IsCentralIsogeny P.projection

/-- The integral Clifford charts give smoothness of the split spin group over
every field. Its scalar kernel is in the connected torus, so the cover is
geometrically connected. The vector image is smooth by faithful flatness. -/
def SplitSpinGeometry : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ P : SplitSpinVectorImage k I,
      Smooth P.spin.val.X.hom ∧ GeometricallyConnected P.spin.val.X.hom ∧ Smooth P.image.val.X.hom

/-- The standard type-D simple coroots pair by the stated Cartan matrix
and span the even-sum lattice. -/
def SimpleDCoordinates : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n),
    (∀ i j, simpleDCoroot.{u} n hn j ⬝ᵥ simpleDCoroot n hn i = CartanMatrix.D n i j) ∧
    Submodule.span ℤ (Set.range (simpleDCoroot.{u} n hn)) = evenSum (ULift.{u} (Fin n))

/-- Relabel the chosen vector vertex by the standard vertex. Its diagram
stabilizer then consists of the identity and the switch of the two spin vertices. -/
def VectorVertexStabilizer : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (i : Fin n), (if n = 4 then i.val ≠ 1 else i.val = 0) →
    ∃ a : Equiv.Perm (Fin n),
      AbsoluteDynkinTypes.PreservesCartan (CartanMatrix.D n) (CartanMatrix.D n) a ∧
      a ⟨0, by omega⟩ = i ∧
      ∀ σ : Equiv.Perm (Fin n),
        AbsoluteDynkinTypes.PreservesCartan (CartanMatrix.D n) (CartanMatrix.D n) σ →
        σ i = i →
        (a.trans σ).trans a.symm = Equiv.refl _ ∨
          (a.trans σ).trans a.symm = Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩

/-- The height for the standard type-D chamber in hyperbolic coordinates. -/
def typeDRootHeight (n : ℕ) (r : ULift.{u} (Fin n) → ℤ) : ℤ :=
  (fun i : ULift.{u} (Fin n) => (n : ℤ) - 1 - i.down.val) ⬝ᵥ r

/-- The standard simple coroots are exactly the indecomposable positive vectors
in the type-D root set for the indicated chamber. -/
def TypeDPositiveRoots : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n),
    (∀ r ∈ coroots (ULift.{u} (Fin n)), typeDRootHeight n r ≠ 0) ∧
    ∀ r : ULift.{u} (Fin n) → ℤ,
      r ∈ Set.range (simpleDCoroot n hn) ↔
        r ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n r ∧
          ¬ ∃ a b, (a ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n a) ∧
            (b ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n b) ∧ a + b = r

/-- The matrix centralizer of the split vector image on all test algebras
consists of scalar matrices. -/
def SplitVectorCentralizer : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ (P : SplitSpinVectorImage k I) (R : TestAlgebra k) (X : Matrix (I ⊕ I) (I ⊕ I) R),
      (∀ (S : TestAlgebra k) (f : R ⟶ S) (p : Points P.image.val.X S),
        Commute (X.map f.hom) (P.orthogonal.points S (p ≫ P.inclusion.hom.hom)).val.val) →
      ∃ a : R, X = Matrix.diagonal (fun _ => a)

/-- The spin group and its vector image are semisimple. The spin group has an
attached datum on a Borel pair containing its diagonal torus. -/
def SplitSpinBorel : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ P : SplitSpinVectorImage k I,
      ∃ (B : SplitBorelPair k) (D : AttachedDatum B) (e : B.G.val ≅ P.spin.val),
        GeometricRadicals.IsSemisimple B.G ∧ GeometricRadicals.IsSemisimple P.image ∧
        letI := D.comm
        ∃ v : Additive (Cocharacter B.T.group) ≃ₗ[ℤ] evenSum I,
          ∀ (R : TestAlgebra k) (s : Rˣ) (c : Cocharacter B.T.group),
            let a := _root_.LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint c R s
            (P.orthogonal.points R (a ≫ (B.T.inclusion ≫ e.hom ≫ P.projection ≫ P.inclusion).hom.hom)).val.val =
              SymplecticMatrixStructure.hyperbolicDiagonal (fun i => s ^ (v (Additive.ofMul c)).val i)

/-- The two diagonal tori in the split Clifford covering form the
faithfully flat torus restriction of the vector projection. -/
def SplitSpinTorusRestriction : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ P : SplitSpinVectorImage k I,
      ∃ (T : ClosedSubgroup P.spin.val) (S : ClosedSubgroup P.image.val) (p : T.group ⟶ S.group),
        GeometricRadicals.IsSplitTorus T.group ∧ RankOneFlag.IsGeometricallyMaximal T ∧
        GeometricRadicals.IsSplitTorus S.group ∧ RankOneFlag.IsGeometricallyMaximal S ∧
        CentralIsogenies.IsTorusRestriction P.projection p ∧
        ∀ (R : TestAlgebra k) (a : Points P.image.val.X R),
          (∃ b : Points S.group.X R, b ≫ S.inclusion.hom.hom = a) ↔
          ∃ t : I → Rˣ,
            (P.orthogonal.points R (a ≫ P.inclusion.hom.hom)).val.val =
              SymplecticMatrixStructure.hyperbolicDiagonal t

/-- In every characteristic, a tangent vector of the vector group is
represented uniquely by an infinitesimal hyperbolic isometry. -/
def SplitVectorTangent : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ P : SplitSpinVectorImage k I,
      let R : TestAlgebra k := CommAlgCat.of k (DualNumber k)
      let q := OddSpinModels.hyperbolicForm I (DualNumber k)
      ∃ e : Lie k P.image.val ≃
          {X : Matrix (I ⊕ I) (I ⊕ I) k //
            ∀ x, q (infinitesimalOrthogonalMatrix X *ᵥ x) = q x},
        ∀ v : Lie k P.image.val,
          (P.orthogonal.points R (v.toMul.val ≫ P.inclusion.hom.hom)).val.val =
            infinitesimalOrthogonalMatrix (e v).val

/-- The actual split Clifford cover has simply connected type `Dₙ`. The
cocharacter comparison is given by its vector action on the hyperbolic torus. -/
def SplitSpinTypeD : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (hn : 4 ≤ n)
    (P : SplitSpinVectorImage k (ULift.{u} (Fin n))),
    ∃ (B : SplitBorelPair k) (D : AttachedDatum B) (e : B.G.val ≅ P.spin.val),
      GeometricRadicals.IsSemisimple B.G ∧
      SimplyConnectedLattice.GeometricallySimplyConnected B.G ∧
      SimplyConnectedLattice.corootLattice D = ⊤ ∧
      letI := D.comm
      ∃ (simple : Fin n ≃ ↥D.base.support)
        (v : Additive (Cocharacter B.T.group) ≃ₗ[ℤ] evenSum (ULift.{u} (Fin n)))
        (t : (groupPointsFunctor k).obj (specGroup (DiagonalizableGroups.groupAlgebra k
          DiagonalizableGroups.IntegerCharacters)) ≅ StandardGroups.multiplicativePoints k),
        (∀ i j, D.datum.rootDatum.pairing (simple j).val (simple i).val = CartanMatrix.D n i j) ∧
        (∀ i, (v (D.datum.rootDatum.coroot (simple i).val)).val = simpleDCoroot n hn i) ∧
        Set.range (fun a => (v (D.datum.rootDatum.coroot a)).val) = coroots (ULift.{u} (Fin n)) ∧
        (∀ a c, D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root a) c =
          ∑ i, (v (D.datum.rootDatum.coroot a)).val i * (v c).val i) ∧
        ∀ (R : TestAlgebra k) (s : Rˣ) (c : Cocharacter B.T.group),
          let a := t.inv.app R s
          let f := c ≫ B.T.inclusion ≫ e.hom ≫ P.projection ≫ P.inclusion
          ((P.orthogonal.points R (a ≫ f.hom.hom)).val : Matrix _ _ R) =
            SymplecticMatrixStructure.hyperbolicDiagonal
              (fun i => s ^ ((v (Additive.ofMul c)).val i))

open _root_.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent (tensorMap)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification (muTwoUnderlying)

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}

/-- The isometry equations of the descended quadratic pair on a test algebra.
The semitrace is extended on the scalar extension of the self-adjoint part. -/
def IsPairIsometry (D : DescendedQuadraticPair ρ) (R : TestAlgebra k)
    (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ) : Prop :=
  let j := (symmetricPart D.involution).subtype.baseChange R
  let f := fun x => TensorProduct.AlgebraTensorModule.rid k R R (D.semitrace.baseChange R x)
  (D.involution.baseChange R).toLinearMap g.val * g.val = 1 ∧
  ∀ x, ∃ y, j y = g.val * j x * g.inv ∧ f y = f x

/-- The full pair isometry equations recover the hyperbolic quadratic
isometries after splitting, over arbitrary commutative test algebras. -/
def PairIsometryScalarExtension : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    [Nonempty I] {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    (D : DescendedQuadraticPair ρ) (R : TestAlgebra k) [Algebra K R] [IsScalarTower k K R],
    ∃ E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[R] Matrix (I ⊕ I) (I ⊕ I) R,
      (∀ (r : R) (x : ρ.fixedSubalgebra), E (r ⊗ₜ[k] x) = r • x.val.map (algebraMap K R)) ∧
      ∀ a : (R ⊗[k] ρ.fixedSubalgebra)ˣ,
        IsPairIsometry D R a ↔ Units.map E.toMonoidHom a ∈ orthogonalMatrices I R

/-- Over every test algebra of the splitting field the reduced norm of
the descended algebra is the determinant in the canonical matrix coordinates. -/
def PairReducedNormScalarExtension : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)} (D : DescendedQuadraticPair ρ)
    (S : Type u) [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    (E : (S ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S),
    (∀ (r : S) (x : ρ.fixedSubalgebra), E (r ⊗ₜ[k] x) = r • x.val.map (algebraMap K S)) →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) k ρ.fixedSubalgebra) (x : S ⊗[k] ρ.fixedSubalgebra),
      MvPolynomial.eval₂ (algebraMap k S) (fun i => (b.baseChange S).repr x i)
        (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b) = (E x).det

/-- The full isometries of the descended pair are represented and split in the indicated
matrix coordinates over every test algebra of the splitting field. -/
def PairIsometryModel : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I] [Nonempty I]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    (D : DescendedQuadraticPair ρ) (O : SplitOrthogonalPresentation K I),
    ∃ (H : AffineAlgebraicGroup k)
      (m : ∀ R : TestAlgebra k, Points H.val.X R →* (R ⊗[k] ρ.fixedSubalgebra)ˣ)
      (e : (groupBaseChange k K).obj H.val ≅ O.group.val),
      (∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : Points H.val.X R),
        m S (mapPoints f a) = Units.map (tensorMap f).toMonoidHom (m R a)) ∧
      (∀ R, Function.Injective (m R)) ∧
      (∀ (R : TestAlgebra k) (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ),
        g ∈ Set.range (m R) ↔ IsPairIsometry D R g) ∧
      ∀ (S : TestAlgebra K),
        let R := (restrictTestAlgebra k K).obj S
        ∃ E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S,
          (∀ (s : S) (x : ρ.fixedSubalgebra), E (s ⊗ₜ[k] x) = s • x.val.map (algebraMap K S)) ∧
          ∀ a : Points ((groupBaseChange k K).obj H.val).X S,
            E (m R (baseChangePoint k K H.val.X S a)).val =
              (O.points S (a ≫ e.hom.hom.hom)).val.val

/-- A simply connected form with a fixed vector vertex is isomorphic to the
actual split Clifford group over a finite Galois subextension of the separable closure. -/
def FiniteSpinReference : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (n : ℕ), 4 ≤ n →
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    SimplyConnectedLattice.GeometricallySimplyConnected G →
    HasFixedVectorVertex G n →
    ∀ (P : SplitSpinVectorImage k (ULift.{u} (Fin n))),
      ∃ K : FiniteGaloisIntermediateField k (SeparableClosure k),
        Nonempty ((groupBaseChange k K).obj P.spin.val ≅ (groupBaseChange k K).obj G.val)

/-- The last hyperbolic switch lifts to the actual split spin scheme, preserves the
standard Borel pair, and interchanges the spin coroots. -/
def SplitSpinDiagramAction : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (hn : 4 ≤ n)
    (P : SplitSpinVectorImage k (ULift.{u} (Fin n))),
    let I := ULift.{u} (Fin n)
    ∃ (B : SplitBorelPair k) (D : AttachedDatum B) (e : B.G.val ≅ P.spin.val)
      (A : B.G.val ≅ B.G.val) (T : B.T.group ≅ B.T.group) (F : B.B.group ≅ B.B.group)
      (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ),
      letI := D.comm
      ∃ simple : Fin n ≃ ↥D.base.support,
      Specs.SimplyConnectedLattice.corootLattice D = ⊤ ∧
      (∀ i j, D.datum.rootDatum.pairing (simple j).val (simple i).val = CartanMatrix.D n i j) ∧
      (∀ x, OddSpinModels.hyperbolicForm I k (g.val *ᵥ x) = OddSpinModels.hyperbolicForm I k x) ∧
      A.hom ≫ A.hom = 𝟙 _ ∧
      T.hom ≫ B.T.inclusion = B.T.inclusion ≫ A.hom ∧
      F.hom ≫ B.B.inclusion = B.B.inclusion ≫ A.hom ∧
      (∀ (R : TestAlgebra k) (a : Points B.G.val.X R),
        let f := e.hom ≫ P.projection ≫ P.inclusion
        let v := (P.orthogonal.points R (a ≫ f.hom.hom)).val.val
        (P.orthogonal.points R (a ≫ (A.hom ≫ f).hom.hom)).val.val =
          conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) g) v) ∧
      P.kernel.inclusion ≫ e.inv ≫ A.hom ≫ e.hom = P.kernel.inclusion ∧
      ∀ i, let j := (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) i
        (D.datum.rootDatum.coroot (simple i).val).toMul ≫ T.hom =
          (D.datum.rootDatum.coroot (simple j).val).toMul

/-- Once the vector morphism descends, its faithfully flat image is the ground-field
neutral subgroup and retains the specified split projection and inclusion. -/
def DescendedVectorImage : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I],
    4 ≤ Fintype.card I →
    ∀ (G H : AffineAlgebraicGroup k) (_hG : GeometricallyConnected G.val.X.hom)
    (v : G.val ⟶ H.val)
    (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G.val ≅ P.spin.val)
    (b : (groupBaseChange k K).obj H.val ≅ P.orthogonal.group.val)
    (_hv : (groupBaseChange k K).map v ≫ b.hom = e.hom ≫ P.projection ≫ P.inclusion),
    ∃ (N : AffineAlgebraicGroup k) (p : G.val ⟶ N.val) (j : N.val ⟶ H.val)
      (a : (groupBaseChange k K).obj N.val ≅ P.image.val),
      IsImageFactorization v p j ∧ IsOpenImmersion j.hom.hom.left ∧
      GeometricallyConnected N.val.X.hom ∧
      Set.range j.hom.hom.left = connectedComponent
        (η[H.val.X].left (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ∧
      (groupBaseChange k K).map p ≫ a.hom = e.hom ≫ P.projection ∧
      (groupBaseChange k K).map j ≫ b.hom = a.hom ≫ P.inclusion

/-- Semilinear equivariance of the split vector matrices descends the displayed
vector morphism to the scheme of full isometries. -/
def VectorMorphismDescent : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    [FiniteDimensional k K] [IsGalois k K] {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    (_D : DescendedQuadraticPair ρ)
    (G H : AffineAlgebraicGroup k) (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G.val ≅ P.spin.val)
    (b : (groupBaseChange k K).obj H.val ≅ P.orthogonal.group.val)
    (m : ∀ R : TestAlgebra k, Points H.val.X R →* (R ⊗[k] ρ.fixedSubalgebra)ˣ)
    (_hNat : ∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : Points H.val.X R),
      m S (mapPoints f a) = Units.map (tensorMap f).toMonoidHom (m R a))
    (_hInj : ∀ R, Function.Injective (m R))
    (_hM : ∀ (S : TestAlgebra K),
      let R := (restrictTestAlgebra k K).obj S
      ∃ E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S,
        (∀ (s : S) (x : ρ.fixedSubalgebra), E (s ⊗ₜ[k] x) = s • x.val.map (algebraMap K S)) ∧
        ∀ x : Points ((groupBaseChange k K).obj H.val).X S,
          E (m R (baseChangePoint k K H.val.X S x)).val =
            (P.orthogonal.points S (x ≫ b.hom.hom.hom)).val.val)
    (g : Gal(K/k) → (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (_hg : ∀ σ X, ρ.act σ X = conjugate (g σ) (X.map σ))
    (_hEq : ∀ (S : TestAlgebra K) (σ : Gal(K/k)),
      let R := (restrictTestAlgebra k K).obj S
      ∀ (f : R ⟶ R), (∀ b, f.hom (algebraMap K S b) = algebraMap K S (σ b)) →
      ∀ (x y : Points ((groupBaseChange k K).obj G.val).X S),
        baseChangePoint k K G.val.X S y = mapPoints f (baseChangePoint k K G.val.X S x) →
        let v (z : Points ((groupBaseChange k K).obj G.val).X S) :=
          (P.orthogonal.points S (z ≫ (e.hom ≫ P.projection ≫ P.inclusion).hom.hom)).val.val
        v y = conjugate (Matrix.GeneralLinearGroup.map (algebraMap K S) (g σ)) ((v x).map f.hom)),
    ∃ v : G.val ⟶ H.val,
      (groupBaseChange k K).map v ≫ b.hom = e.hom ≫ P.projection ≫ P.inclusion

/-- The neutral isometry equations in characteristic different from two are
the unitary equation and reduced norm one, on every ground-field test algebra. -/
def NeutralPointsReducedNorm : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    [Nonempty I] [FiniteDimensional k K] [IsGalois k K]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    (D : DescendedQuadraticPair ρ), 4 ≤ Fintype.card I → (2 : k) ≠ 0 →
    ∀ (H N : AffineAlgebraicGroup k) (j : N.val ⟶ H.val) (_hj : IsClosedImmersion j.hom.hom.left)
    (m : ∀ R : TestAlgebra k, Points H.val.X R →* (R ⊗[k] ρ.fixedSubalgebra)ˣ)
    (_hNat : ∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : Points H.val.X R),
      m S (mapPoints f a) = Units.map (tensorMap f).toMonoidHom (m R a))
    (_hRange : ∀ (R : TestAlgebra k) (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ),
      g ∈ Set.range (m R) ↔ IsPairIsometry D R g)
    (P : SplitSpinVectorImage K I)
    (b : (groupBaseChange k K).obj H.val ≅ P.orthogonal.group.val)
    (a : (groupBaseChange k K).obj N.val ≅ P.image.val)
    (_hIncl : (groupBaseChange k K).map j ≫ b.hom = a.hom ≫ P.inclusion)
    (_hM : ∀ (S : TestAlgebra K),
      let R := (restrictTestAlgebra k K).obj S
      ∃ E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S,
        (∀ (s : S) (x : ρ.fixedSubalgebra), E (s ⊗ₜ[k] x) = s • x.val.map (algebraMap K S)) ∧
        ∀ x : Points ((groupBaseChange k K).obj H.val).X S,
          E (m R (baseChangePoint k K H.val.X S x)).val =
            (P.orthogonal.points S (x ≫ b.hom.hom.hom)).val.val),
    ∃ (d : ℕ) (s : Module.Basis (Fin d) k ρ.fixedSubalgebra),
      ∀ (R : TestAlgebra k) (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ),
        (∃ x : Points N.val.X R, m R (x ≫ j.hom.hom) = g) ↔
          (D.involution.baseChange R).toLinearMap g.val * g.val = 1 ∧
          MvPolynomial.eval₂ (algebraMap k R) (fun i => (s.baseChange R).repr g.val i)
            (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple s) = 1

open Opposite
open AutomorphismSequence (RelativeAut groupSections scalarAut)

/-- A marked split vector realization of the given pinning. Over any field
extension, an automorphism fixing the marked vertex is inner or the composite
of an inner automorphism and the last-plane switch. -/
def FixedVertexOuterFactorization : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    (L : RootGroups.AdditiveLine k) (P : PinnedGroup L)
    (D : AttachedDatum P.pair) {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (n : ℕ) (hn : 4 ≤ n)
    (_hD : letI := D.comm; SimplyConnectedLattice.corootLattice D = ⊤)
    (s : Fin n ≃ ↥D.toBased.base.support)
    (_hs : ∀ i j, D.toBased.datum.pairing (s j).val (s i).val = CartanMatrix.D n i j)
    (i : Fin n) (_hi : if n = 4 then i.val ≠ 1 else i.val = 0)
    (C : SplitSpinVectorImage k (ULift.{u} (Fin n))),
    let I := ULift.{u} (Fin n)
    ∃ (e : C.spin.val ≅ P.pair.G.val) (A : P.pair.G.val ≅ P.pair.G.val)
      (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ),
      (∀ x, OddSpinModels.hyperbolicForm I k (g.val *ᵥ x) =
        OddSpinModels.hyperbolicForm I k x) ∧
      (∀ (R : TestAlgebra k) (x : Points P.pair.G.val.X R),
        let p := e.inv ≫ C.projection ≫ C.inclusion
        (C.orthogonal.points R (x ≫ (A.hom ≫ p).hom.hom)).val.val =
          conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) g)
            (C.orthogonal.points R (x ≫ p.hom.hom)).val.val) ∧
      C.kernel.inclusion ≫ e.hom ≫ A.hom = C.kernel.inclusion ≫ e.hom ∧
      ∀ f : RelativeAut P.pair.G.val (fieldTest k S),
        ((QuasiSplitInnerForms.outerHom (S := S) E) f).asIso.hom.val.indexEquiv (s i).val = (s i).val →
        ∃ q : (groupSections Q.quotient.val).obj (op (fieldTest k S)),
          f = E.inner.app (op (fieldTest k S)) q ∨
          f = (show RelativeAut P.pair.G.val (fieldTest k S) from E.inner.app (op (fieldTest k S)) q) *
            scalarAut (Aut.of A) (fieldTest k S)

/-- Restrict the splitting cocycle and its fixed vertex to a finite Galois
subextension of the separable closure, retaining the given relative comparison. -/
def FixedVertexFiniteLevel : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : RootGroups.AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (G : AffineAlgebraicGroup k) (v : D.toBased.I)
    (e : (groupBaseChange k S).obj P.pair.G.val ≅ (groupBaseChange k S).obj G.val)
    (r : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (_hr : RelativeFormComparison.IsInduced k S e r)
    (_h : ∀ σ : Gal(S/k), ((QuasiSplitInnerForms.outerHom (S := S) E) (transportedAut k S r σ)).asIso.hom.val.indexEquiv v = v),
    ∃ (L : FiniteGaloisIntermediateField k S)
      (j : (groupBaseChange k L).obj P.pair.G.val ≅ (groupBaseChange k L).obj G.val)
      (t : relativePoints P.pair.G.val (fieldTest k L) ≅ relativePoints G.val (fieldTest k L)),
      RelativeFormComparison.IsInduced k L j t ∧
      r = AutomorphismSequence.restrictIso
        ((testSpec k).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L S)).op) t ∧
      ∀ δ : Gal(L/k), ((QuasiSplitInnerForms.outerHom (S := L) E) (transportedAut k L t δ)).asIso.hom.val.indexEquiv v = v

/-- A finite split spin comparison with its descended projective matrix action
and scalar inclusion, both identified on the indicated test algebras. -/
structure EquivariantSpinTrivialization {k K I : Type u} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] (G : AffineAlgebraicGroup k) where
  reference : SplitSpinVectorImage k I
  split : SplitSpinVectorImage K I
  comparison : (groupBaseChange k K).obj G.val ≅ split.spin.val
  g : Gal(K/k) → (Matrix (I ⊕ I) (I ⊕ I) K)ˣ
  multiplier : Gal(K/k) → Kˣ
  action : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)
  actionFormula : ∀ σ X, action.act σ X = conjugate (g σ) (X.map σ)
  similarity : ∀ σ x, OddSpinModels.hyperbolicForm I K ((g σ).val *ᵥ x) = (multiplier σ : K) * OddSpinModels.hyperbolicForm I K x
  equivariance : ∀ (S : TestAlgebra K) (σ : Gal(K/k)),
    let R := (restrictTestAlgebra k K).obj S
    ∀ (f : R ⟶ R), (∀ b, f.hom (algebraMap K S b) = algebraMap K S (σ b)) →
    ∀ (x y : Points ((groupBaseChange k K).obj G.val).X S),
      baseChangePoint k K G.val.X S y = mapPoints f (baseChangePoint k K G.val.X S x) →
      let v (z : Points ((groupBaseChange k K).obj G.val).X S) :=
        (split.orthogonal.points S (z ≫ (comparison.hom ≫ split.projection ≫ split.inclusion).hom.hom)).val.val
      v y = conjugate (Matrix.GeneralLinearGroup.map (algebraMap K S) (g σ)) ((v x).map f.hom)
  scalar : reference.kernel.group ⟶ G.val
  splitScalar : (groupBaseChange k K).obj reference.kernel.group ≅ split.kernel.group
  scalarInclusion : (groupBaseChange k K).map scalar ≫ comparison.hom =
    splitScalar.hom ≫ split.kernel.inclusion
  scalarValue : ∀ (S : TestAlgebra K) (x : Points ((groupBaseChange k K).obj reference.kernel.group).X S),
    (reference.kernelPoints ((restrictTestAlgebra k K).obj S)
      (baseChangePoint k K reference.kernel.group.X S x)).val.val =
      (split.kernelPoints S (x ≫ splitScalar.hom.hom.hom)).val.val

/-- The given fixed vector vertex produces an equivariant finite Galois
comparison with the split Clifford group. -/
def FiniteEquivariantSpinReference : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (n : ℕ), 4 ≤ n →
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    SimplyConnectedLattice.GeometricallySimplyConnected G →
    HasFixedVectorVertex G n →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K) (_ : IsGalois k K),
      Nonempty (EquivariantSpinTrivialization (K := K) (I := ULift.{u} (Fin n)) G)

/-- The orthogonal or quadratic-pair model, with its vector morphism and its
scalar scheme kernel compared to the Clifford cover after splitting. -/
structure SpinModel (G : AffineAlgebraicGroup k) (D : DescendedQuadraticPair ρ) where
  full : AffineAlgebraicGroup k
  neutral : AffineAlgebraicGroup k
  inclusion : neutral.val ⟶ full.val
  projection : G.val ⟶ neutral.val
  fullPoints : ∀ R : TestAlgebra k, Points full.val.X R →* (R ⊗[k] ρ.fixedSubalgebra)ˣ
  fullNatural : ∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : Points full.val.X R),
    fullPoints S (mapPoints f a) = Units.map (tensorMap f).toMonoidHom (fullPoints R a)
  fullFaithful : ∀ R, Function.Injective (fullPoints R)
  fullRange : ∀ (R : TestAlgebra k) (a : (R ⊗[k] ρ.fixedSubalgebra)ˣ),
    a ∈ Set.range (fullPoints R) ↔ IsPairIsometry D R a
  openImmersion : IsOpenImmersion inclusion.hom.hom.left
  closedImmersion : IsClosedImmersion inclusion.hom.hom.left
  connected : GeometricallyConnected neutral.val.X.hom
  identityComponent : Set.range inclusion.hom.hom.left =
    connectedComponent (η[full.val.X].left
      (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))))
  centralIsogeny : CentralIsogenies.IsCentralIsogeny projection
  kernel : ClosedSubgroup G.val
  isKernel : IsSchemeKernel projection kernel
  kernelScheme : kernel.group.X ≅ muTwoUnderlying k
  kernelPoints : ∀ R : TestAlgebra k, Points kernel.group.X R ≃* rootsOfUnity 2 R
  kernelNatural : ∀ (R S : TestAlgebra k) (f : R ⟶ S) (x : Points kernel.group.X R),
    (kernelPoints S (mapPoints f x)).val.val = f.hom (kernelPoints R x).val.val
  splitCover : SplitSpinVectorImage K I
  splitSource : (groupBaseChange k K).obj G.val ≅ splitCover.spin.val
  splitNeutral : (groupBaseChange k K).obj neutral.val ≅ splitCover.image.val
  splitFull : (groupBaseChange k K).obj full.val ≅ splitCover.orthogonal.group.val
  splitKernel : (groupBaseChange k K).obj kernel.group ≅ splitCover.kernel.group
  projectionComparison : (groupBaseChange k K).map projection ≫ splitNeutral.hom =
    splitSource.hom ≫ splitCover.projection
  inclusionComparison : (groupBaseChange k K).map inclusion ≫ splitFull.hom =
    splitNeutral.hom ≫ splitCover.inclusion
  kernelComparison : (groupBaseChange k K).map kernel.inclusion ≫ splitSource.hom =
    splitKernel.hom ≫ splitCover.kernel.inclusion
  scalarComparison : ∀ (S : TestAlgebra K)
    (a : Points ((groupBaseChange k K).obj kernel.group).X S),
    (kernelPoints ((restrictTestAlgebra k K).obj S) (baseChangePoint k K kernel.group.X S a)).val.val =
      (splitCover.kernelPoints S (a ≫ splitKernel.hom.hom.hom)).val.val
  matrixComparison : ∀ (S : TestAlgebra K),
    let R := (restrictTestAlgebra k K).obj S
    ∃ E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S,
      (∀ (s : S) (x : ρ.fixedSubalgebra), E (s ⊗ₜ[k] x) = s • x.val.map (algebraMap K S)) ∧
      ∀ a : Points ((groupBaseChange k K).obj full.val).X S,
        E (fullPoints R (baseChangePoint k K full.val.X S a)).val =
          (splitCover.orthogonal.points S (a ≫ splitFull.hom.hom.hom)).val.val
  reducedNormOne : (2 : k) ≠ 0 →
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k ρ.fixedSubalgebra),
      ∀ (R : TestAlgebra k) (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ),
        (∃ a : Points neutral.val.X R, fullPoints R (a ≫ inclusion.hom.hom) = g) ↔
          (D.involution.baseChange R).toLinearMap g.val * g.val = 1 ∧
          MvPolynomial.eval₂ (algebraMap k R) (fun i => (b.baseChange R).repr g.val i)
            (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b) = 1

/-- A simply connected nontrialitarian group of type `Dₙ` descends as the
scalar double cover of the neutral isometries of the stated algebra and pair. -/
def NontrialitarianSpinModel : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (n : ℕ), 4 ≤ n →
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    SimplyConnectedLattice.GeometricallySimplyConnected G →
    HasFixedVectorVertex G n →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K) (_ : IsGalois k K),
      let I := ULift.{u} (Fin n)
      ∃ (ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)) (D : DescendedQuadraticPair ρ),
        (∀ σ : Gal(K/k), ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
          (∀ X, ρ.act σ X = conjugate g (X.map σ)) ∧
          ∀ x, OddSpinModels.hyperbolicForm I K (g.val *ᵥ x) =
            (c : K) * OddSpinModels.hyperbolicForm I K x) ∧
        ((2 : k) ≠ 0 → IsOrthogonal
          (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution D.involution)) ∧
        Nonempty (SpinModel G D)

/-- A nontrivial split cocharacter of the spin group over the local field
produces a hyperbolic pair in its quaternionic skew-Hermitian model. -/
def QuaternionSpinIsotropy : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    (G : AffineAlgebraicGroup k) (D : DescendedQuadraticPair ρ), SpinModel G D →
    ∀ (F : Type u) [Field F] [Algebra k F], (2 : F) ≠ 0 →
    ∀ (B : Type u) [DivisionRing B] [Algebra F B]
      (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
      _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (r : ℕ) (e : (F ⊗[k] ρ.fixedSubalgebra) ≃ₐ[F] Matrix (Fin r) (Fin r) B),
      (∃ c : Cocharacter ((groupBaseChange k F).obj G.val), c ≠ 0) →
      ∃ (b : Involution F B) (H : (Matrix (Fin r) (Fin r) B)ˣ)
        (h : SkewHermitianPairing b) (x y : Fin r → B),
        (∀ z, antiValue b.anti z = SymplecticInvolutionModels.quaternionConjugate hB z) ∧
        SymplecticDivisionForms.dagger b.anti H.val = -H.val ∧
        (∀ z, e ((D.involution.baseChange F).toLinearMap z) =
          H.inv * SymplecticDivisionForms.dagger b.anti (e z) * H.val) ∧
        h.value = SymplecticDivisionForms.hermitianValue b.anti H.val ∧
        x ≠ 0 ∧ h.value x x = 0 ∧ h.value x y = 1 ∧ h.value y x = -1 ∧ h.value y y = 0

end TypeDModels

end LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
