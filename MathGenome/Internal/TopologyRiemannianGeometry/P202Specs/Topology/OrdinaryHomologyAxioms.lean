import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Excision
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.PrismHomotopy
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! Ordinary additivity and the previously constructed axioms, paper.tex 1416–1426.
A colimiting cofan is the universal-property formulation of a direct sum.
Its legs below are the actual maps induced by the summand inclusions. In
particular the assertions include an empty index type and arbitrary topologies.
The coefficient module is arbitrary, including ring and abelian coefficients.
The excision statements retain the upstream ring-coefficient interface. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
namespace P202Specs.OrdinaryHomologyAxioms
open SingularChains RelativeSingularChains ChainLES

variable (R : Type u) [CommRing R] {I : Type v} (X : I → TopCat.{v})
  (M : Type w) [AddCommGroup M] [Module R M]

def chainCofan : Cofan (fun i => complex R M (X i)) :=
  Cofan.mk (complex R M (TopCat.of (Σ i, X i)))
    (fun i => chainMap R M (TopCat.sigmaι X i))

def ordinaryChainCofan : Cofan (fun i => ordinaryComplex R M (X i)) :=
  Cofan.mk (ordinaryComplex R M (TopCat.of (Σ i, X i)))
    (fun i => (ordinaryFunctor R M).map (TopCat.sigmaι X i))

def homologyCofan (n : ℤ) : Cofan (fun i => homology R M (X i) n) :=
  Cofan.mk (homology R M (TopCat.of (Σ i, X i)) n)
    (fun i => (homologyFunctor R M n).map (TopCat.sigmaι X i))

/-- The nonnegative singular complex is the direct sum via its canonical inclusions. -/
def chainAdditivity_type : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (X : I → TopCat.{v})
    (M : Type w) [AddCommGroup M] [Module R M],
    Nonempty (IsColimit (chainCofan R X M))

/-- The same assertion for the ordinary complex extended by zero in negative degrees. -/
def ordinaryChainAdditivity_type : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (X : I → TopCat.{v})
    (M : Type w) [AddCommGroup M] [Module R M],
    Nonempty (IsColimit (ordinaryChainCofan R X M))

/-- Additivity of ordinary homology in every integer degree, including empty unions. -/
def homologyAdditivity_type : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (X : I → TopCat.{v})
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℤ),
    Nonempty (IsColimit (homologyCofan R X M n))

/-- These are the same canonical functors, pair sequence and point calculation
as in the preceding constructions, together with excision and its naturality. -/
def ordinaryAxioms_type : Prop :=
  (∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
    (n : ℤ),
    (∀ X : TopCat.{v}, (homologyFunctor R M n).map (𝟙 X) = 𝟙 _) ∧
    (∀ {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (homologyFunctor R M n).map (f ≫ g) =
        (homologyFunctor R M n).map f ≫ (homologyFunctor R M n).map g)) ∧
  PrismHomotopy.Expected.homology.{u,w,v} ∧
  PrismHomotopy.Expected.relativeHomology.{u,w,v} ∧
  (∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M],
    ordinaryLESType.{u,w,v} R M) ∧
  Excision.isomorphism_type.{u,v} ∧ Excision.naturality_type.{u,v} ∧
  SingularDegreeZero.Expected.pointOrdinaryZero.{u,w,v} ∧
  SingularDegreeZero.Expected.pointOrdinaryOther.{u,w,v}

end P202Specs.OrdinaryHomologyAxioms
