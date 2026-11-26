import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

/-- The map from rational points to points over an extension field. -/
def extendRationalPoint {K : Type u} [Field K] [Algebra k K] {X : SchemeOver k} :
    Points X (CommAlgCat.of k k) → Points X (CommAlgCat.of k K) :=
  mapPoints (CommAlgCat.ofHom (Algebra.ofId k K))

/-- The action of the q-power Frobenius on points of an arbitrary scheme over the
finite field k, where q is the cardinality of k. -/
def frobeniusOnPoints [Fintype k] {X : SchemeOver k} (R : TestAlgebra k) :
    Points X R → Points X R :=
  mapPoints (CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k R))

/-- The Lang map on geometric points with the convention F(g) * g⁻¹. -/
def langOnGeometricPoints [Fintype k] (G : Specs.GroupScheme k)
    (g : Points G.X (CommAlgCat.of k (AlgebraicClosure k))) :
    Points G.X (CommAlgCat.of k (AlgebraicClosure k)) :=
  frobeniusOnPoints _ g * g⁻¹

namespace Specs

def SmoothGroupGeometricConnectedness : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : GroupScheme k)
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left],
    ConnectedSpace ((groupBaseChange k (AlgebraicClosure k)).obj G).X.left

def FrobeniusFixedPoints : Prop :=
  ∀ (k K : Type u) [Field k] [Fintype k] [Field K] [Algebra k K]
    (X : SchemeOver k) (x : Points X (CommAlgCat.of k K)),
    frobeniusOnPoints _ x = x ↔
      ∃ a : Points X (CommAlgCat.of k k), extendRationalPoint a = x

def SmoothLangSurjectivity : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : GroupScheme k)
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left],
    Function.Surjective (langOnGeometricPoints G)

def SmoothLangFibres : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : GroupScheme k)
    (g h : Points G.X (CommAlgCat.of k (AlgebraicClosure k))),
    langOnGeometricPoints G h = langOnGeometricPoints G g ↔
      ∃ a : Points G.X (CommAlgCat.of k k), g * extendRationalPoint (K := AlgebraicClosure k) a = h

end Specs

end

end LinearAlgebraicGroups
