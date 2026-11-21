import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainHomology
import Mathlib.Algebra.Homology.Homotopy

/-! The complete small-chain comparison, paper.tex 1264–1316.
The equivalences below have the actual inclusions as their forward maps;
`HomotopyEquiv` supplies an inverse chain map and both chain homotopies.
All complexes use the original nonnegative grading and arbitrary commutative
coefficient rings, and the relative complex uses the restricted cover. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped Simplicial
universe u v w
namespace P202Specs.SmallChainEquivalence
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.SmallChainHomology

/-- Absolute chain homotopy equivalence, together with every homology comparison. -/
def absoluteEquivalence_type : Prop :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{v}) (ι : Type w)
    (U : OpenCover X ι),
    (∃ e : HomotopyEquiv (smallComplex R U) (complex R R X),
      e.hom = smallInclusion R U) ∧
    ∀ n : ℕ, IsIso (homologyMap (smallInclusion R U) n)

/-- Relative chain homotopy equivalence for every subspace, including the empty one. -/
def relativeEquivalence_type : Prop :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{v}) (ι : Type w)
    (U : OpenCover X ι) (A : Set X),
    (∃ e : HomotopyEquiv (smallRelativeComplex R U A) (nonnegative R R ⟨X, A⟩),
      e.hom = smallRelativeInclusion R U A) ∧
    ∀ n : ℕ, IsIso (homologyMap (smallRelativeInclusion R U A) n)

/-- A map compatible with the two covers; no choice of target member is fixed. -/
def CoverCompatible {X Y : TopCat.{v}} {ι κ : Type w}
    (U : OpenCover X ι) (V : OpenCover Y κ) (f : X ⟶ Y) : Prop :=
  ∀ i, ∃ j, Set.MapsTo f (U.sets i) (V.sets j)

variable (R : Type u) [CommRing R]

/-- Postcomposition on the actual small subcomplexes. -/
def mapSmall {X Y : TopCat.{v}} {ι κ : Type w}
    (U : OpenCover X ι) (V : OpenCover Y κ) (f : X ⟶ Y)
    (hf : CoverCompatible U V f) : smallComplex R U ⟶ smallComplex R V := by
  classical
  exact ChainComplex.ofHom
    (fun n => ModuleCat.ofHom ((((chainMap R R f).f n).hom.comp
      (smallModule R U n).subtype).codRestrict (smallModule R V n)
        (by
          intro c q hq
          change q ∈ (Finsupp.mapDomain _ c.val).support at hq
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hq)
          obtain ⟨i, hi⟩ := (mem_smallModule R U n c.val).mp c.property s hs
          obtain ⟨j, hj⟩ := hf i
          refine ⟨j, ?_⟩
          rintro y ⟨x, rfl⟩
          exact hj (hi ⟨x, rfl⟩))))
    (by
      intro n
      simp only [smallComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact congrArg (fun k => k c.val) ((chainMap R R f).comm (n+1) n))

lemma mapSmall_square {X Y : TopCat.{v}} {ι κ : Type w}
    (U : OpenCover X ι) (V : OpenCover Y κ) (f : X ⟶ Y)
    (hf : CoverCompatible U V f) :
    mapSmall R U V f hf ≫ smallInclusion R V =
      smallInclusion R U ≫ chainMap R R f := by
  ext n c
  rfl

/-- Compatibility passes to restricted covers, even when some members disappear. -/
lemma restrictedCompatible {P Q : Pair.{v}} {ι κ : Type w}
    (U : OpenCover P.space ι) (V : OpenCover Q.space κ) (f : P ⟶ Q)
    (hf : CoverCompatible U V f.map) :
    CoverCompatible (restrictedCover U P.subspace) (restrictedCover V Q.subspace)
      f.restrict := by
  intro i
  obtain ⟨j, hj⟩ := hf i.val
  obtain ⟨x, hx⟩ := i.property
  refine ⟨⟨j, f.restrict x, hj hx⟩, ?_⟩
  intro y hy
  exact hj hy

lemma mapSmall_subspace_square {P Q : Pair.{v}} {ι κ : Type w}
    (U : OpenCover P.space ι) (V : OpenCover Q.space κ) (f : P ⟶ Q)
    (hf : CoverCompatible U V f.map) :
    smallSubspaceInclusion R U P.subspace ≫ mapSmall R U V f.map hf =
      mapSmall R (restrictedCover U P.subspace) (restrictedCover V Q.subspace)
        f.restrict (restrictedCompatible U V f hf) ≫ smallSubspaceInclusion R V Q.subspace := by
  ext n c
  apply Subtype.ext
  exact congrArg (fun k : complex R R P.sub ⟶ complex R R Q.space => k.f n c.val)
    (inclusion_square (chainFunctor R R) f)

/-- The induced map of small relative quotients. -/
def mapSmallRelative {P Q : Pair.{v}} {ι κ : Type w}
    (U : OpenCover P.space ι) (V : OpenCover Q.space κ) (f : P ⟶ Q)
    (hf : CoverCompatible U V f.map) :
    smallRelativeComplex R U P.subspace ⟶ smallRelativeComplex R V Q.subspace :=
  cokernel.map _ _
    (mapSmall R (restrictedCover U P.subspace) (restrictedCover V Q.subspace)
      f.restrict (restrictedCompatible U V f hf))
    (mapSmall R U V f.map hf) (mapSmall_subspace_square R U V f hf)

/-- Naturality of the inclusion on homology. With `absoluteEquivalence_type`
these are natural isomorphisms; no naturality of the chosen homotopy inverse
is required. -/
def absoluteNaturality_type : Prop :=
  ∀ (R : Type u) [CommRing R] (X Y : TopCat.{v}) (ι κ : Type w)
    (U : OpenCover X ι) (V : OpenCover Y κ) (f : X ⟶ Y)
    (hf : CoverCompatible U V f) (n : ℕ),
    homologyMap (mapSmall R U V f hf) n ≫ homologyMap (smallInclusion R V) n =
      homologyMap (smallInclusion R U) n ≫ homologyMap (chainMap R R f) n

/-- The relative naturality square for arbitrary maps of pairs compatible
with the covers, using the ordinary relative chain map. -/
def relativeNaturality_type : Prop :=
  ∀ (R : Type u) [CommRing R] (P Q : Pair.{v}) (ι κ : Type w)
    (U : OpenCover P.space ι) (V : OpenCover Q.space κ) (f : P ⟶ Q)
    (hf : CoverCompatible U V f.map) (n : ℕ),
    homologyMap (mapSmallRelative R U V f hf) n ≫
        homologyMap (smallRelativeInclusion R V Q.subspace) n =
      homologyMap (smallRelativeInclusion R U P.subspace) n ≫
        homologyMap (relativeMap (chainFunctor R R) f) n

end P202Specs.SmallChainEquivalence
