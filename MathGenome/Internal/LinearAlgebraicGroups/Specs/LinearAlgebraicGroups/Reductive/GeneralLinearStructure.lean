import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.LieKolchin
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.GeneralLinearStructure

noncomputable section

open StandardGroups
open Unipotent (Index)
open GeometricRadicals
open SchemeDerivedGroup (IsSubgroupOf IsSolvable)

variable {k : Type u} [Field k] {n : ℕ}

abbrev MatrixPoints (G : AffineAlgebraicGroup k) (n : ℕ) :=
  (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k (Index.{u} n)

abbrev SpecialMatrixPoints (S : AffineAlgebraicGroup k) (n : ℕ) :=
  (groupPointsFunctor k).obj S.val ≅ specialLinearPoints k (Index.{u} n)

def IsDiagonal {R : Type u} [CommRing R] (g : Matrix.GeneralLinearGroup (Index.{u} n) R) : Prop :=
  ∀ i j, i ≠ j → g.val i j = 0

/-- The diagonal subgroup centralizer is tested after every extension of the test algebra. -/
def DiagonalCentralizerMatrices : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (R : TestAlgebra k)
    (g : Matrix.GeneralLinearGroup (Index.{u} n) R),
    IsDiagonal g ↔
      ∀ (A : TestAlgebra k) (f : R ⟶ A)
        (d : Matrix.GeneralLinearGroup (Index.{u} n) A), IsDiagonal d →
        Matrix.GeneralLinearGroup.map f.hom.toRingHom g * d =
          d * Matrix.GeneralLinearGroup.map f.hom.toRingHom g

/-- The center of the matrix group over every test algebra, including nonreduced algebras. -/
def ScalarCenterMatrices : Prop :=
  ∀ (n : ℕ) (_ : 0 < n) (R : Type u) [CommRing R]
    (g : Matrix.GeneralLinearGroup (Index.{u} n) R),
    (∀ h : Matrix.GeneralLinearGroup (Index.{u} n) R, g * h = h * g) ↔
      ∃ a : Rˣ, g.val = Matrix.scalar (Index.{u} n) (a : R)

/-- The determinant-open affine scheme is smooth and geometrically connected. -/
def GeneralLinearGeometry : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    let X := (testSpec k).obj (Opposite.op (CommAlgCat.of k (GLCoordinates k (Index.{u} n))))
    Smooth X.hom ∧ GeometricallyConnected X.hom

/-- Any affine group representing invertible matrices has the determinant-open geometry. -/
def GeneralLinearGroupGeometry : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    ∀ (G : AffineAlgebraicGroup k), MatrixPoints G n →
      Smooth G.val.X.hom ∧ GeometricallyConnected G.val.X.hom

/-- The determinant-one scheme is smooth in every characteristic. -/
def SpecialLinearGeometry : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (S : AffineAlgebraicGroup k), SpecialMatrixPoints S n → Smooth S.val.X.hom

/-- A geometric Borel is a maximal smooth connected solvable closed subgroup. -/
def IsBorel {G : GroupScheme k} (B : ClosedSubgroup G) : Prop :=
  Smooth B.group.X.hom ∧ ConnectedSpace B.group.X.left ∧ IsSolvable B.group ∧
    ∀ H : ClosedSubgroup G, Smooth H.group.X.hom → ConnectedSpace H.group.X.left →
      IsSolvable H.group → IsSubgroupOf B H → IsSubgroupOf H B

def GeneralLinearReductive : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G : AffineAlgebraicGroup k), MatrixPoints G n → IsReductive G

/-- The scheme centre is the multiplicative group with its scalar embedding. -/
def GeneralLinearCenter : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G : AffineAlgebraicGroup k) (e : MatrixPoints G n) (M : AffineAlgebraicGroup k)
      (m : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k),
      ∃ C : ClosedSubgroup G.val,
        RepresentsSubgroup C (fun _ g ↦ Centralizes (𝟙 G.val) g) ∧
        ∃ i : M.val ≅ C.group, ∀ (R : TestAlgebra k) (x : Points M.val.X R),
          let a : Rˣ := m.hom.app R x
          (e.hom.app R (((groupPointsFunctor k).map (i.hom ≫ C.inclusion)).app R x)).val =
            Matrix.scalar (Index.{u} n) a.val

/-- The specified diagonal and upper triangular subgroups, with their inclusions into GL. -/
def GeneralLinearBorelPair : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G : AffineAlgebraicGroup k) (e : MatrixPoints G n),
      ∃ (T B : ClosedSubgroup G.val),
        (∀ (R : TestAlgebra k) (g : Points G.val.X R),
          g ∈ SubgroupSections T ((testSpec k).obj (Opposite.op R)) ↔
            IsDiagonal (e.hom.app R g)) ∧
        (∀ (R : TestAlgebra k) (g : Points G.val.X R),
          g ∈ SubgroupSections B ((testSpec k).obj (Opposite.op R)) ↔
            (e.hom.app R g).val.IsUpperTriangular) ∧
        IsSplitTorus T.group ∧ IsSubgroupOf T B ∧
        RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g) ∧
        Smooth B.group.X.hom ∧ GeometricallyConnected B.group.X.hom ∧
          IsSolvable B.group ∧
        ∃ (hT : IsClosedImmersion
            ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left)
          (hB : IsClosedImmersion
            ((groupBaseChange k (AlgebraicClosure k)).map B.inclusion).hom.hom.left),
          IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T hT) ∧
            IsBorel (baseChangedSubgroup (AlgebraicClosure k) B hB)

/-- Over an algebraically closed field the abstract derived subgroup of GL is determinant one. -/
def GeneralLinearGeometricCommutator : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (_ : 0 < n),
    commutator (Matrix.GeneralLinearGroup (Index.{u} n) k) =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Index.{u} n) k →* kˣ).ker

/-- The canonical determinant-one matrices form the scheme-derived subgroup. -/
def GeneralLinearDerived : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G S : AffineAlgebraicGroup k) (e : MatrixPoints G n) (s : SpecialMatrixPoints S n),
      ∃ f : S.val ⟶ G.val,
        ∃ hf : IsClosedImmersion f.hom.hom.left,
          (∀ (R : TestAlgebra k) (x : Points S.val.X R),
            e.hom.app R (((groupPointsFunctor k).map f).app R x) =
              Matrix.SpecialLinearGroup.toGL (s.hom.app R x)) ∧
          Smooth S.val.X.hom ∧
          SchemeDerivedGroup.IsDerivedSubgroup (⟨S.val, f, hf⟩ : ClosedSubgroup G.val)

/-- In rank one, the general linear group, the diagonal torus and the upper triangular
group are copies of the multiplicative group, and the determinant-one group is trivial. -/
def GeneralLinearRankOne : Prop :=
  ∀ (k : Type u) [Field k] (G S M : AffineAlgebraicGroup k)
    (e : MatrixPoints G 1) (_s : SpecialMatrixPoints S 1)
    (_ : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k),
    Nonempty (G.val ≅ M.val) ∧ Nonempty (S.val ≅ Grp.trivial (SchemeOver k)) ∧
      ∀ D : ClosedSubgroup G.val,
        ((∀ (R : TestAlgebra k) (g : Points G.val.X R),
            g ∈ SubgroupSections D ((testSpec k).obj (Opposite.op R)) ↔
              IsDiagonal (e.hom.app R g)) ∨
         (∀ (R : TestAlgebra k) (g : Points G.val.X R),
            g ∈ SubgroupSections D ((testSpec k).obj (Opposite.op R)) ↔
              (e.hom.app R g).val.IsUpperTriangular)) →
        IsIso D.inclusion

end

end LinearAlgebraicGroups.Specs.GeneralLinearStructure
