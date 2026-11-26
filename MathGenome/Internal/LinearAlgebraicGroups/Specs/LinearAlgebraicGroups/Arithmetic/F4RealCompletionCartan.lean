import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

open CategoryTheory AlgebraicGeometry

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.F4RealCompletionCartan

open AdjointRepresentation (GroupPoints)
open Pinning (SplitBorelPair AttachedDatum)
open AbsoluteDynkinTypes (HasDynkinType)

variable {F : Type u} [Field F] {K : Type} [Field K]

/-- The test algebra comparison respects scalars and changes of coefficients. -/
def AlgebraCompatible (e : F ≃+* K) (L : TestAlgebra K ⥤ TestAlgebra F)
    (r : ∀ R, L.obj R ≃+* R) : Prop :=
  (∀ R x, r R (algebraMap F (L.obj R) x) = algebraMap K R (e x)) ∧
  (∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : L.obj R),
    r S ((L.map a).hom x) = a.hom (r R x))

/-- The corresponding test points of two group schemes. -/
abbrev PointComparison (L : TestAlgebra K ⥤ TestAlgebra F)
    (X : GroupScheme F) (Y : GroupScheme K) :=
  ∀ R : TestAlgebra K, GroupPoints Y R ≃* GroupPoints X (L.obj R)

def IsNatural {L : TestAlgebra K ⥤ TestAlgebra F} {X : GroupScheme F} {Y : GroupScheme K}
    (p : PointComparison L X Y) : Prop :=
  ∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : GroupPoints Y R),
    p S (mapPoints a x) = mapPoints (L.map a) (p R x)

def InclusionCompatible {L : TestAlgebra K ⥤ TestAlgebra F}
    {A X : GroupScheme F} {B Y : GroupScheme K} (i : A ⟶ X) (j : B ⟶ Y)
    (p : PointComparison L X Y) (q : PointComparison L A B) : Prop :=
  ∀ (R : TestAlgebra K) (x : GroupPoints B R),
    p R (x ≫ j.hom.hom) = q R x ≫ i.hom.hom

/-- The Cartan type of the specified based datum is invariant under the
compatible comparisons of the ambient group, torus, and Borel. -/
def Statement : Prop :=
  ∀ {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (L : TestAlgebra K ⥤ TestAlgebra F) (r : ∀ R, L.obj R ≃+* R),
    AlgebraCompatible e L r →
    ∀ (P : SplitBorelPair F) (Q : SplitBorelPair K)
      (g : PointComparison L P.G.val Q.G.val)
      (t : PointComparison L P.T.group Q.T.group)
      (b : PointComparison L P.B.group Q.B.group),
      IsNatural g → IsNatural t → IsNatural b →
      InclusionCompatible P.T.inclusion Q.T.inclusion g t →
      InclusionCompatible P.B.inclusion Q.B.inclusion g b →
      ∀ (D : AttachedDatum P) (E : AttachedDatum Q),
        (letI := D.comm; HasDynkinType (RootData.integralCartan D.datum.rootDatum D.base) .F4) →
        (letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) .F4)

end LinearAlgebraicGroups.Specs.Arithmetic.F4RealCompletionCartan
