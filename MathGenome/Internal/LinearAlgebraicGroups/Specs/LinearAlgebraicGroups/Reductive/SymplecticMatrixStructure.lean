import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.IdentityTangent
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

open AlgebraicGeometry CategoryTheory Matrix
open scoped Matrix

universe u

namespace LinearAlgebraicGroups.Specs.SymplecticMatrixStructure

noncomputable section

abbrev Indices (ι : Type u) := ι ⊕ ι

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {k : Type u} [Field k]

/-- The equation for preservation of the alternating form on column vectors. -/
def matrixEquation {R : Type u} [CommRing R] (g : Matrix (Indices ι) (Indices ι) R) :
    Matrix (Indices ι) (Indices ι) R :=
  gᵀ * Matrix.J ι R * g - Matrix.J ι R

def alternatingForm (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R] :
    LinearMap.BilinForm R (Indices ι → R) :=
  Matrix.toLinearMap₂' R (Matrix.J ι R)

abbrev PointGroup (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R] :=
  ↥(Matrix.symplecticGroup ι R)

def mapSymplecticPoint {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PointGroup ι R →* PointGroup ι S where
  toFun g := ⟨g.val.map f, SymplecticGroup.map_mem g.property f⟩
  map_one' := Subtype.ext (Matrix.map_one f (map_zero f) (map_one f))
  map_mul' g h := Subtype.ext (Matrix.map_mul (f := f) (L := g.val) (M := h.val))

def symplecticPoints (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (PointGroup ι R)
  map f := GrpCat.ofHom (mapSymplecticPoint f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro g; exact Subtype.ext rfl
  map_comp _ _ := by apply GrpCat.ext; intro g; exact Subtype.ext rfl

open StandardGroups

/-- The defining ideal in the fixed general linear coordinate algebra. -/
def symplecticIdeal (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    Ideal (GLCoordinates k (Indices ι)) :=
  Ideal.span (Set.range fun ij : Indices ι × Indices ι =>
    matrixEquation (universalMatrix k (Indices ι)) ij.1 ij.2)

abbrev Coordinates (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :=
  GLCoordinates k (Indices ι) ⧸ symplecticIdeal k ι

def universalSymplecticMatrix (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    Matrix (Indices ι) (Indices ι) (Coordinates k ι) :=
  (Ideal.Quotient.mkₐ k (symplecticIdeal k ι)).mapMatrix
    (universalMatrix k (Indices ι))

def PointEquation : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R]
    (g : Matrix (Indices ι) (Indices ι) R),
    (g ∈ Matrix.symplecticGroup ι R ↔ gᵀ * Matrix.J ι R * g = Matrix.J ι R) ∧
    (g ∈ Matrix.symplecticGroup ι R ↔
      ∀ x y, alternatingForm ι R (g *ᵥ x) (g *ᵥ y) = alternatingForm ι R x y)

def PerfectAlternatingForm : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R],
    (alternatingForm ι R).IsAlt ∧ (alternatingForm ι R).Nondegenerate ∧
      IsUnit (Matrix.J ι R).det

def MatrixPresentation : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι],
    ∃ (hGL : HopfOperations k (GLCoordinates k (Indices ι)))
        (hSp : HopfOperations k (Coordinates k ι)),
      letI := hGL.hopf
      letI := hSp.hopf
      let q := Ideal.Quotient.mkₐ k (symplecticIdeal k ι)
      Represents (GLCoordinates k (Indices ι)) (generalLinearPoints k (Indices ι))
        (fun (R : TestAlgebra k) f M => (show Matrix.GeneralLinearGroup (Indices ι) R from M).val =
          f.mapMatrix (universalMatrix k (Indices ι))) ∧
      Represents (Coordinates k ι) (symplecticPoints k ι)
        (fun (R : TestAlgebra k) f M => (show PointGroup ι R from M).val =
          f.mapMatrix (universalSymplecticMatrix k ι)) ∧
      (Algebra.TensorProduct.map q q).comp hGL.delta = hSp.delta.comp q ∧
      hGL.epsilon = hSp.epsilon.comp q ∧
      q.comp hGL.inverse = hSp.inverse.comp q ∧
      ∃ j : (spectrum k (Coordinates k ι)).val ⟶ (spectrum k (GLCoordinates k (Indices ι))).val,
        j.hom.hom.left = Spec.map (CommRingCat.ofHom q.toRingHom) ∧
        IsClosedImmersion j.hom.hom.left

/-- The matrices satisfying the linear equation obtained at the identity. -/
def symplecticLieSubspace (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    Submodule k (Matrix (Indices ι) (Indices ι) k) where
  carrier := {X | (Matrix.J ι k * X).IsSymm}
  zero_mem' := by simp [Matrix.IsSymm]
  add_mem' {X Y} hX hY := by
    change (Matrix.J ι k * (X + Y)).IsSymm
    rw [Matrix.mul_add]
    exact Matrix.IsSymm.add hX hY
  smul_mem' s X h := by
    change (Matrix.J ι k * (s • X)).IsSymm
    rw [Matrix.mul_smul]
    exact Matrix.IsSymm.smul h s

/-- A comparison natural in test algebras identifies the identity tangent kernel
with the matrices whose product on the left by J is symmetric. -/
def LieComparison : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] (G : GroupScheme k)
    (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k ι),
    ∃ e : Lie k G ≃+ symplecticLieSubspace k ι,
      (∀ p i j, (e p).val i j =
        ((show PointGroup ι (DualNumber k) from
          c.hom.app (CommAlgCat.of k (DualNumber k)) p.toMul.val).val i j).snd) ∧
      ∀ (s : k) (p : Lie k G), e (scalePointKernel G s p) = s • e p

abbrev symplecticScheme (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :=
  (testSpec k).obj (Opposite.op (CommAlgCat.of k (Coordinates k ι)))

def Smoothness : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι],
    Smooth (symplecticScheme k ι).hom

def GeometricConnectedness : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι],
    GeometricallyConnected (symplecticScheme k ι).hom

def Dimension : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι],
    ringKrullDim (Coordinates k ι) =
      (Fintype.card ι * (2 * Fintype.card ι + 1) : ℕ)

def Reductivity : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G : AffineAlgebraicGroup k),
    Nonempty ((groupPointsFunctor k).obj G.val ≅ symplecticPoints k ι) →
    GeometricRadicals.IsReductive G

/-- The diagonal matrices whose entries on the paired hyperbolic basis vectors are reciprocal. -/
def hyperbolicDiagonal {R : Type u} [CommRing R] (t : ι → Rˣ) :
    Matrix (Indices ι) (Indices ι) R :=
  Matrix.diagonal (Sum.elim (fun i => (t i : R)) (fun i => (↑((t i)⁻¹) : R)))

/-- Commutation is required after every scalar extension of the test ring. -/
def CentralizesDiagonal {R : Type u} [CommRing R]
    (g : Matrix (Indices ι) (Indices ι) R) : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S) (t : ι → Sˣ),
    Commute (g.map f) (hyperbolicDiagonal t)

def DiagonalCentralizer : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R] (g : PointGroup ι R),
    CentralizesDiagonal g.val ↔ ∃ t : ι → Rˣ, g.val = hyperbolicDiagonal t

def DiagonalTorusEmbedding : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k ι),
    ∃ (T : ClosedSubgroup G.val)
      (d : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k ι),
      Nonempty (T.group ≅
        (multiplicativePowerGroup k (ULift.{u} (Fin (Fintype.card ι)))).val) ∧
      ∀ (R : TestAlgebra k) (t : ι → Rˣ),
        (show PointGroup ι R from
          c.hom.app R (((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t))).val =
          hyperbolicDiagonal t

/-- The centralizer functor of a closed subgroup. Commutation is tested on all
algebras over each test algebra, which includes infinitesimal points. -/
def IsOwnSchemeCentralizer {G : GroupScheme k} (T : ClosedSubgroup G) : Prop :=
  let P := (groupPointsFunctor k).obj G
  let Q := (groupPointsFunctor k).obj T.group
  let j := (groupPointsFunctor k).map T.inclusion
  ∀ (R : TestAlgebra k) (p : P.obj R),
    (∀ (S : TestAlgebra k) (f : R ⟶ S) (q : Q.obj S),
      Commute (P.map f p) (j.app S q)) ↔
    ∃ q : Q.obj R, j.app R q = p

def DiagonalTorus : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k ι),
    ∃ (T : ClosedSubgroup G.val)
      (d : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k ι),
      Nonempty (T.group ≅
        (multiplicativePowerGroup k (ULift.{u} (Fin (Fintype.card ι)))).val) ∧
      (∀ (R : TestAlgebra k) (t : ι → Rˣ),
        (show PointGroup ι R from
          c.hom.app R (((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t))).val =
          hyperbolicDiagonal t) ∧
      IsOwnSchemeCentralizer T ∧ ∃ h : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        GeometricRadicals.IsMaximalTorus (GeometricRadicals.baseChangedSubgroup
          (AlgebraicClosure k) T h)

def TransitiveNaturalAction : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    {x y : Indices ι → k}, x ≠ 0 → y ≠ 0 → ∃ g : PointGroup ι k, g.val *ᵥ x = y

end
end LinearAlgebraicGroups.Specs.SymplecticMatrixStructure
