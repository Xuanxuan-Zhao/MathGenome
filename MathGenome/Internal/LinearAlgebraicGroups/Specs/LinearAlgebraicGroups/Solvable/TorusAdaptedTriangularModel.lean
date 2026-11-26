import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SplitSolvableRadical

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.TorusAdaptedTriangularModel

open SmoothDiagonalKernel SplitSolvableRadical StandardGroups Unipotent

variable {k : Type u} [Field k]

/-- Evaluate an integral character of a split torus in its unit coordinates. -/
def characterValue {r : ℕ} {R : TestAlgebra k} (m : Index.{u} r → ℤ)
    (a : Index.{u} r → Rˣ) : Rˣ :=
  ∏ s, a s ^ m s

/-- In the given basis, the restricted representation is diagonal with
characters given by the rows of `m` on all test algebras. -/
def DiagonalWeights {n r : ℕ} {H : AffineAlgebraicGroup k} {T : GroupScheme k}
    (j : T ⟶ H.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Index.{u} r))
    (m : Index.{u} n → Index.{u} r → ℤ) : Prop :=
  ∀ (R : TestAlgebra k) (a : Points T.X R) (i l : Index.{u} n),
    (matrixPoint j e R a).val i l =
      if i = l then (characterValue (m i) (t.hom.app R a) : R) else 0

/-- A split solvable group has a faithful matrix realization respecting a full
flag and diagonalizing the given closed split torus in that basis. The upper
triangular condition is preservation of every coordinate prefix on every test
algebra. -/
def HasTorusAdaptedTriangularModel : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val),
    SchemeDerivedGroup.IsSplitSolvable G.val →
    IsSplitTorus (closedSubgroupAlgebraicGroup T) →
    ∃ (n r : ℕ) (H : AffineAlgebraicGroup k) (j : G.val ⟶ H.val)
      (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
      (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} r))
      (m : Index.{u} n → Index.{u} r → ℤ),
      IsClosedImmersion j.hom.hom.left ∧ IsUpperTriangular j e ∧
        DiagonalWeights (T.inclusion ≫ j) e t m

end LinearAlgebraicGroups.Specs.TorusAdaptedTriangularModel
