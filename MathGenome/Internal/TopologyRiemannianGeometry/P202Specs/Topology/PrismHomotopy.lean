import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularDegreeZero
import Mathlib.Topology.Homotopy.TopCat.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Algebra.Homology.Homotopy

/-! Homotopy invariance, paper.tex, Theorem `thm:p202-prism` (1104–1145).
All coefficients are arbitrary modules, all chains have finite support, and
integer indexing includes the augmented degree -1. Mathlib's `Homotopy g f`
means `g = dP + Pd + f`, so this order gives the paper's positive prism sign. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202Specs.PrismHomotopy
open P202Specs.SingularChains P202Specs.RelativeSingularChains
universe u v w

/-- A homotopy of pairs need only preserve the specified subspaces. -/
structure PairHomotopy {P Q : Pair.{w}} (f g : P ⟶ Q) where
  homotopy : TopCat.Homotopy f.map g.map
  preserves : ∀ (t : unitInterval) (x : P.subspace), homotopy (t, x.val) ∈ Q.subspace

namespace Expected

def nonnegative : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : TopCat.{w}} {f g : X ⟶ Y}, TopCat.Homotopy f g →
    Nonempty (_root_.Homotopy (chainMap R M g) (chainMap R M f))

def ordinary : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : TopCat.{w}} {f g : X ⟶ Y}, TopCat.Homotopy f g →
    Nonempty (_root_.Homotopy ((ordinaryFunctor R M).map g) ((ordinaryFunctor R M).map f))

def reduced : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : TopCat.{w}} {f g : X ⟶ Y}, TopCat.Homotopy f g →
    ∃ h : _root_.Homotopy ((reducedFunctor R M).map g) ((reducedFunctor R M).map f),
      h.hom (-1) 0 = 0

/-- The quotient prism is induced by an absolute prism, in every degree. -/
def relative : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {P Q : Pair.{w}} {f g : P ⟶ Q}, PairHomotopy f g →
    ∃ (a : _root_.Homotopy ((ordinaryFunctor R M).map g.map)
        ((ordinaryFunctor R M).map f.map))
      (b : _root_.Homotopy ((reducedFunctor R M).map g.map)
        ((reducedFunctor R M).map f.map))
      (ar : _root_.Homotopy (relativeMap (ordinaryFunctor R M) g)
        (relativeMap (ordinaryFunctor R M) f))
      (br : _root_.Homotopy (relativeMap (reducedFunctor R M) g)
        (relativeMap (reducedFunctor R M) f)),
      b.hom (-1) 0 = 0 ∧
      (∀ i j, (projection (ordinaryFunctor R M) P).f i ≫ ar.hom i j =
        a.hom i j ≫ (projection (ordinaryFunctor R M) Q).f j) ∧
      (∀ i j, (projection (reducedFunctor R M) P).f i ≫ br.hom i j =
        b.hom i j ≫ (projection (reducedFunctor R M) Q).f j)

def homology : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : TopCat.{w}} {f g : X ⟶ Y}, TopCat.Homotopy f g → ∀ n : ℤ,
    (homologyFunctor R M n).map f = (homologyFunctor R M n).map g ∧
    (reducedHomologyFunctor R M n).map f = (reducedHomologyFunctor R M n).map g

def relativeHomology : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {P Q : Pair.{w}} {f g : P ⟶ Q}, PairHomotopy f g → ∀ n : ℤ,
    (relativeHomologyFunctor R M n).map f = (relativeHomologyFunctor R M n).map g ∧
    (reducedRelativeHomologyFunctor R M n).map f =
      (reducedRelativeHomologyFunctor R M n).map g

def equivalence : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X),
    TopCat.Homotopy (f ≫ g) (𝟙 X) → TopCat.Homotopy (g ≫ f) (𝟙 Y) → ∀ n : ℤ,
    IsIso ((homologyFunctor R M n).map f) ∧
    IsIso ((reducedHomologyFunctor R M n).map f)

def contractible : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (X : TopCat.{w}) [Nonempty X] [ContractibleSpace X] (n : ℤ),
    IsZero (reducedHomology R M X n)

end Expected
end P202Specs.PrismHomotopy
