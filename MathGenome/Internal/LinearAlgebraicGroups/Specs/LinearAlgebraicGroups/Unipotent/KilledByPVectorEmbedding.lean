import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.FieldTheory.AlgebraicClosure

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.Unipotent

variable {k : Type u} [Field k]

/-- Applying a linear functional to each entry of a matrix of coordinate functions. -/
def coordinateEvaluation {ι A : Type u} [AddCommGroup A] [Module k A]
    (D : Matrix ι ι A) : Module.Dual k A →ₗ[k] Matrix ι ι k where
  toFun f := D.map f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The space cut out by the linear relations on the entries of a coordinate matrix.
Equivalently, it is the image of the dual of the linear map giving those entries. -/
def coordinateSpan {ι A : Type u} [AddCommGroup A] [Module k A]
    (D : Matrix ι ι A) : Submodule k (Matrix ι ι k) :=
  LinearMap.range (coordinateEvaluation D)

/-- The scalar extension of a matrix subspace in the matrix algebra over a test ring. -/
def extendMatrixSpan {ι : Type u} (R : Type u) [CommRing R] [Algebra k R]
    (M : Submodule k (Matrix ι ι k)) : Submodule R (Matrix ι ι R) :=
  Submodule.span R ((fun v : Matrix ι ι k ↦ v.map (algebraMap k R)) '' (M : Set _))

/-- Membership in the coordinate span is equivalent to satisfying the defining linear
equations. The values of a linear form on the matrix units are its coefficients. -/
def CoordinateSpanLinearEquations : Prop :=
  ∀ {k A ι : Type u} [Field k] [AddCommGroup A] [Module k A]
    [Fintype ι] [DecidableEq ι] (D : Matrix ι ι A) (v : Matrix ι ι k),
    v ∈ coordinateSpan (k := k) D ↔
      ∀ l : Module.Dual k (Matrix ι ι k),
        (∑ i, ∑ j, l (Matrix.single i j 1) • D i j) = 0 → l v = 0

/-- Formation of the span of a finite coordinate matrix commutes with field extension. -/
def CoordinateSpanBaseChange : Prop :=
  ∀ {k K A ι : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Finite ι] (D : Matrix ι ι A),
    extendMatrixSpan K (coordinateSpan (k := k) D) =
      coordinateSpan (k := K)
        (D.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A))

/-- Every specialization of the coordinate matrix belongs to the extended span. -/
def CoordinateEvaluationMem : Prop :=
  ∀ {k A R ι : Type u} [Field k] [CommRing A] [Algebra k A]
    [CommRing R] [Algebra k R] [Finite ι] (D : Matrix ι ι A) (f : A →ₐ[k] R),
    D.map f ∈ extendMatrixSpan R (coordinateSpan (k := k) D)

/-- Over an algebraically closed field, the geometric evaluations span the coordinate
matrix space of a reduced affine scheme of finite type. -/
def CoordinateSpanGeometricPoints : Prop :=
  ∀ {K A ι : Type u} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [_root_.IsReduced A] [Finite ι] (D : Matrix ι ι A),
    coordinateSpan (k := K) D =
      Submodule.span K (Set.range fun f : A →ₐ[K] K ↦ D.map f)

/-- The strictly upper triangular commutative nil algebra used in the construction. -/
structure IsMatrixNilAlgebra {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (p : ℕ) (M : Submodule k (Matrix ι ι k)) : Prop where
  strictUpper {v} : v ∈ M → ∀ i j, j ≤ i → v i j = 0
  mul_mem {v w} : v ∈ M → w ∈ M → v * w ∈ M
  commute {v w} : v ∈ M → w ∈ M → Commute v w
  pow_eq_zero {v} : v ∈ M → v ^ p = 0

/-- The matrix of differences at the universal point of a Hopf algebra. -/
def universalDifference {A : HopfAlgebraCategory k} {n : ℕ}
    (ρ : convolutionPoints A ⟶ unitriangularPoints k n) :
    Matrix (Index.{u} n) (Index.{u} n) A :=
  (ρ.app (CommAlgCat.of k A) (toConv (AlgHom.id k A))).val.val - 1

/-- The coordinates of a commutative group killed by p in a unitriangular representation
span a commutative algebra consisting of matrices whose p-th powers vanish. -/
def CoordinateSpanNilAlgebra : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A]
    [_root_.IsReduced (AlgebraicClosure k ⊗[k] A)] (n : ℕ)
    (ρ : convolutionPoints A ⟶ unitriangularPoints k n),
    (∀ (R : TestAlgebra k) (x y : (convolutionPoints A).obj R), Commute x y) →
    (∀ (R : TestAlgebra k) (x : (convolutionPoints A).obj R), x ^ p = 1) →
    IsMatrixNilAlgebra p (coordinateSpan (k := k) (universalDifference ρ))

/-- A vector group identifies with the group 1 + M on all test algebras.
The displayed entries and their inverse are polynomial by representability. -/
def TruncatedExponentialIsomorphism : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)),
    IsMatrixNilAlgebra p M →
    ∃ (d : ℕ) (e : StandardGroups.additivePowerPoints k (Index.{u} d) ⟶ unitriangularPoints k n),
      d = Module.finrank k M ∧ ∀ R : TestAlgebra k, Function.Injective (e.app R) ∧
        Set.range (e.app R) = {g | g.val.val - 1 ∈ extendMatrixSpan R M}

/-- The arbitrary-field closed embedding for smooth connected commutative unipotent
groups killed by multiplication by p. Commutativity and the power identity are
asserted on every affine test algebra. -/
def KilledByPVectorEmbedding : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : AffineAlgebraicGroup k) [Smooth H.val.X.hom] [ConnectedSpace H.val.X.left],
    IsUnipotent H →
    (∀ (R : TestAlgebra k) (x y : ((groupPointsFunctor k).obj H.val).obj R), Commute x y) →
    (∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj H.val).obj R), x ^ p = 1) →
    ∃ (d : ℕ) (V : AffineAlgebraicGroup k),
      Nonempty ((groupPointsFunctor k).obj V.val ≅ StandardGroups.additivePowerPoints k (Index.{u} d)) ∧
        ∃ f : H.val ⟶ V.val, IsClosedImmersion f.hom.hom.left

end LinearAlgebraicGroups.Specs.Unipotent
