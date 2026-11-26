import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.F4RealCompletionBorelPair

open AdjointRepresentation (GroupPoints)
open GeometricRadicals (IsReductive)
open Pinning (SplitBorelPair)

variable {F : Type u} [Field F] {K : Type} [Field K]

/-- A natural multiplicative comparison on the specified test algebras. -/
structure PointComparison (L : TestAlgebra K ⥤ TestAlgebra F)
    (X : GroupScheme F) (Y : GroupScheme K) where
  equiv : ∀ R : TestAlgebra K, GroupPoints Y R ≃* GroupPoints X (L.obj R)
  natural : ∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : GroupPoints Y R),
    equiv S (mapPoints a x) = mapPoints (L.map a) (equiv R x)

/-- A comparison of subgroup points intertwines the two marked inclusions. -/
def Compatible {L : TestAlgebra K ⥤ TestAlgebra F} {A X : GroupScheme F}
    {B Y : GroupScheme K} (p : PointComparison L X Y) (q : PointComparison L A B)
    (i : A ⟶ X) (j : B ⟶ Y) : Prop :=
  ∀ (R : TestAlgebra K) (x : GroupPoints B R),
    p.equiv R (x ≫ j.hom.hom) = q.equiv R x ≫ i.hom.hom

/-- Transport the specified split maximal torus and Borel to the actual target group. -/
def TransportSplitBorelPair : Prop :=
  ∀ (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (e : F ≃+* K) (L : TestAlgebra K ⥤ TestAlgebra F)
    (r : ∀ R : TestAlgebra K, L.obj R ≃+* R),
    (∀ (R : TestAlgebra K) (x : F), r R (algebraMap F (L.obj R) x) = algebraMap K R (e x)) →
    (∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : L.obj R), r S ((L.map a).hom x) = a.hom (r R x)) →
    ∀ (P : SplitBorelPair F) (H : AffineAlgebraicGroup K), IsReductive H →
    PointComparison L P.G.val H.val →
    ∃ Q : SplitBorelPair K, Q.G = H ∧
      ∃ (p : PointComparison L P.G.val Q.G.val)
        (t : PointComparison L P.T.group Q.T.group) (b : PointComparison L P.B.group Q.B.group),
        Compatible p t P.T.inclusion Q.T.inclusion ∧
          Compatible p b P.B.inclusion Q.B.inclusion

end LinearAlgebraicGroups.Specs.Arithmetic.F4RealCompletionBorelPair
