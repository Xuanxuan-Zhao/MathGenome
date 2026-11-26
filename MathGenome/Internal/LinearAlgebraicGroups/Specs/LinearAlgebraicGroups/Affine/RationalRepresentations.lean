import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ComoduleFiniteness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

open AlgebraicGeometry CategoryTheory WithConv Opposite
open scoped TensorProduct

universe u
noncomputable section

namespace LinearAlgebraicGroups
namespace Specs.RationalRepresentations

def RepresentationType :=
  ∀ {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    (_ : AffineGroupCategory k) (L : GroupScheme k),
    ((groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι) → Type u

/-- Rational representations are group scheme maps into a scheme representing the
general linear point functor in a finite basis. -/
abbrev representation {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    (G : AffineGroupCategory k) (L : GroupScheme k)
    (_ : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι) : Type u :=
  G.val ⟶ L

end Specs.RationalRepresentations

namespace RationalRepresentations

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {ι : Type u}

/-- Applying the given coordinate functional to the vector factor of a tensor. -/
def tensorCoordinate {C : Type u} [AddCommGroup C] [Module k C]
    (b : Module.Basis ι k V) (i : ι) : V ⊗[k] C →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap.comp ((b.coord i).rTensor C)

/-- The matrix of a coaction in the given basis. The column indexes the input vector. -/
def coefficients (A : HopfAlgebraCategory k) (b : Module.Basis ι k V)
    (ρ : RightComodule k A V) : Matrix ι ι A :=
  fun i j ↦ tensorCoordinate b i (ρ.coaction (b j))

/-- The matrix identities for the comultiplication and counit of a right coaction. -/
structure IsCoactionMatrix (A : HopfAlgebraCategory k) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) : Prop where
  comul (i j : ι) :
    Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j
  counit (i j : ι) :
    Coalgebra.counit (R := k) (M i j) = (1 : Matrix ι ι k) i j

/-- A group scheme homomorphism evaluated on the universal point of its coordinate Hopf algebra. -/
def universalMatrix (A : HopfAlgebraCategory k) [Fintype ι] [DecidableEq ι]
    (G : AffineGroupCategory k) (L : Specs.GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (f : Specs.RationalRepresentations.representation G L l) : Matrix ι ι A :=
  (l.hom.app (CommAlgCat.of k A)
    (((groupPointsFunctor k).map f).app (CommAlgCat.of k A)
      (e.hom.app (CommAlgCat.of k A) (toConv (AlgHom.id k A)))) :
        Matrix.GeneralLinearGroup ι A).val

/-- The canonical trivial coaction used in the definition of invariants. -/
def trivialLinearMap (A : HopfAlgebraCategory k) : V →ₗ[k] V ⊗[k] A :=
  (TensorProduct.comm k A V).toLinearMap.comp (TensorProduct.mk k A V 1)

/-- The action on vectors of the form `x ⊗ 1` at an algebra-valued point. Such vectors
span the extended module over the test algebra. -/
def evaluate (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    {R : Type u} [CommRing R] [Algebra k R] (g : A →ₐ[k] R) :
    V →ₗ[k] V ⊗[k] R :=
  (g.toLinearMap.lTensor V).comp ρ.coaction

/-- The difference between the coaction and the trivial map. -/
def invariantDifference (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) :
    V →ₗ[k] V ⊗[k] A :=
  ρ.coaction - trivialLinearMap A

/-- The invariant subspace of a coaction. -/
def invariants (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) : Submodule k V :=
  LinearMap.ker (invariantDifference A ρ)

/-- The standard Hopf algebra after scalar extension, with its usual tensor product structure. -/
abbrev scalarExtension (A : HopfAlgebraCategory k) (K : Type u) [Field K] [Algebra k K] :
    HopfAlgebraCategory K :=
  CommHopfAlgCat.of K (K ⊗[k] A)

/-- Restrict a point of the extended coordinate algebra along the inclusion of the
original coefficient algebra. -/
def restrictCoordinatePoint (A : HopfAlgebraCategory k) (K : Type u) [Field K] [Algebra k K]
    (R : TestAlgebra K) (g : scalarExtension A K →ₐ[K] R) :
    A →ₐ[k] (restrictTestAlgebra k K).obj R :=
  letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' rfl
  (g.restrictScalars k).comp Algebra.TensorProduct.includeRight

end RationalRepresentations

namespace Specs
namespace RationalRepresentations

open LinearAlgebraicGroups.RationalRepresentations

/-- Every right coaction has the indicated matrix identities, and the matrix
determines it uniquely. Every matrix with these identities comes from a coaction. -/
def CoactionMatrixComparison : Prop :=
  ∀ {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V),
    (∀ ρ : RightComodule k A V, IsCoactionMatrix A (coefficients A b ρ)) ∧
    Function.Injective (coefficients A b) ∧
    (∀ M : Matrix ι ι A, IsCoactionMatrix A M → ∃ ρ, coefficients A b ρ = M)

/-- Representations of affine group schemes and coactions are equivalent, with
the coaction coefficients given by the universal point. -/
def RepresentationCoactionComparison : Prop :=
  ∀ {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V)
    (G : AffineGroupCategory k) (L : GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι),
    ∃ E : representation G L l ≃ RightComodule k A V,
      ∀ f, coefficients A b (E f) = universalMatrix A G L e l f

/-- In the given basis, evaluation gives the matrix of the representation at every point. -/
def EvaluationComparison : Prop :=
  ∀ {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V)
    (G : AffineGroupCategory k) (L : GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
    (f : representation G L l) (ρ : RightComodule k A V)
    (_ : coefficients A b ρ = universalMatrix A G L e l f)
    (R : TestAlgebra k) (g : A →ₐ[k] R) (j : ι),
    evaluate A ρ g (b j) = ∑ i, b i ⊗ₜ[k]
      (l.hom.app R (((groupPointsFunctor k).map f).app R (e.hom.app R (toConv g))) :
        Matrix.GeneralLinearGroup ι R).val i j

def EquivariantMaps : Prop :=
  ∀ {k V W : Type u} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (f : V →ₗ[k] W),
    (∀ (R : TestAlgebra k) (g : A →ₐ[k] R),
      (f.rTensor R).comp (evaluate A ρ g) = (evaluate A σ g).comp f) ↔
    (f.rTensor A).comp ρ.coaction = σ.coaction.comp f

def StableSubspaces : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (W : Submodule k V),
    (∀ (R : TestAlgebra k) (g : A →ₐ[k] R) (x : W),
      evaluate A ρ g x ∈ LinearMap.range (W.subtype.rTensor R)) ↔ ρ.IsSubcomodule W

def InvariantKernel : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (x : V),
    (∀ (R : TestAlgebra k) (g : A →ₐ[k] R), evaluate A ρ g x = x ⊗ₜ[k] (1 : R)) ↔
      x ∈ invariants A ρ

/-- Tensor product uses the tensor product basis and the products of the coefficients.
In these bases the matrices are the Kronecker products at every test point. -/
def TensorProductComparison : Prop :=
  ∀ {k V W ι J : Type u} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V) (c : Module.Basis J k W)
    (ρ : RightComodule k A V) (σ : RightComodule k A W),
    ∃ τ : RightComodule k A (V ⊗[k] W),
      ∀ i j, coefficients A (b.tensorProduct c) τ i j =
        coefficients A b ρ i.1 j.1 * coefficients A c σ i.2 j.2

/-- The dual basis has coefficients given by the transpose of the antipode matrix. -/
def DualComparison : Prop :=
  ∀ {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V) (ρ : RightComodule k A V),
    ∃ σ : RightComodule k A (Module.Dual k V),
      ∀ i j, coefficients A b.dualBasis σ i j =
        HopfAlgebra.antipode k (coefficients A b ρ j i)

/-- Field extension maps the coefficient functions into the scalar-extended Hopf algebra. -/
def FieldExtensionComparison : Prop :=
  ∀ {k K V ι : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V) (ρ : RightComodule k A V),
    ∃ σ : RightComodule K (scalarExtension A K) (K ⊗[k] V),
      (∀ i j, coefficients (scalarExtension A K) (b.baseChange K) σ i j =
        (1 : K) ⊗ₜ[k] coefficients A b ρ i j) ∧
      invariants (scalarExtension A K) σ = (invariants A ρ).baseChange K ∧
      ∀ (R : TestAlgebra K) (g : scalarExtension A K →ₐ[K] R) (i j : ι),
        g (coefficients (scalarExtension A K) (b.baseChange K) σ i j) =
          restrictCoordinatePoint A K R g (coefficients A b ρ i j)

/-- For each affine group scheme and finite-dimensional space, the matrix general linear
group represents automorphisms in a basis and its scheme homomorphisms give coactions
over the coordinate algebra of the given group scheme. -/
def AffineRepresentationComparison : Prop :=
  ∀ {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    [(affineHopfSpec k).IsEquivalence] (G : AffineGroupCategory k) (b : Module.Basis ι k V),
    let A := ((affineHopfSpec k).inv.obj G).unop
    ∃ (L : AffineAlgebraicGroup k)
      (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
      (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
      (E : representation G L.val l ≃ RightComodule k A V),
      (∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)),
        (e.hom.app R g : Points G.val.X R).left =
          Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫
            ((affineHopfSpec k).asEquivalence.counitIso.hom.app G).hom.hom.hom.left) ∧
      ∀ f, coefficients A b (E f) = universalMatrix A G L.val e l f

/-- For a smooth affine algebraic group, stability may be checked on all
algebraic-closure points of the coordinate model. -/
def GeometricStability : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (G : AffineAlgebraicGroup k) (A : HopfAlgebraCategory k)
    (_ : ((affineHopfSpec k).obj (op A)).val ≅ G.val) (_ : Smooth G.val.X.hom)
    (ρ : RightComodule k A V) (W : Submodule k V),
    (∀ (g : A →ₐ[k] AlgebraicClosure k) (x : W),
      evaluate A ρ g x ∈ LinearMap.range (W.subtype.rTensor (AlgebraicClosure k))) ↔
        ρ.IsSubcomodule W

/-- The extended Hopf algebra describes points of the scheme-theoretic base change.
The identification on the original scheme is along the inclusion of coordinates. -/
def FieldExtensionPoints : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (G : AffineGroupCategory k)
    (s : ((affineHopfSpec k).obj (op A)).val ≅ G.val),
    ∃ e : convolutionPoints (scalarExtension A K) ≅
        (groupPointsFunctor K).obj ((groupBaseChange k K).obj G.val),
      (∀ (R : TestAlgebra K) (g : WithConv (scalarExtension A K →ₐ[K] R)),
        (baseChangePoint k K G.val.X R (e.hom.app R g)).left =
          Spec.map (CommRingCat.ofHom (restrictCoordinatePoint A K R g.ofConv).toRingHom) ≫
            s.hom.hom.hom.left) ∧
      ∀ (L : GroupScheme k) (f : G.val ⟶ L) (R : TestAlgebra K)
        (g : WithConv (scalarExtension A K →ₐ[K] R)),
        (baseChangePoint k K L.X R
          (((groupPointsFunctor K).map ((groupBaseChange k K).map f)).app R
            (e.hom.app R g))).left =
          Spec.map (CommRingCat.ofHom (restrictCoordinatePoint A K R g.ofConv).toRingHom) ≫
            s.hom.hom.hom.left ≫ f.hom.hom.left

/-- The coordinate coalgebra satisfies the comodule directed-union result even
when the affine group scheme is not of finite type. -/
def CoordinateComoduleUnion : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V),
    Directed (· ≤ ·) (fun W : ρ.FiniteSubcomodule ↦ W.val) ∧
      (⋃ W : ρ.FiniteSubcomodule, (W.val : Set V)) = Set.univ

end RationalRepresentations
end Specs
end LinearAlgebraicGroups
