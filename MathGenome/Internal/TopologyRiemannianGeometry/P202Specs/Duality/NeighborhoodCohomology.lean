import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.EuclideanNeighborhoodRetraction
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Category.Preorder

/-! Neighborhood comparison in the proof of Alexander duality, paper.tex
2505–2522. The index order is reverse inclusion; every open neighborhood is
included. Cohomology is the algebraic singular cohomology of the upstream
interface. The theorem types below do not assume any continuity property. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace P202.Duality.NeighborhoodCohomology
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
universe u v w

abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanAmbient (n+1)) 1

/-- Arrows run from larger neighborhoods to smaller neighborhoods. -/
structure OpenNeighborhood {X : Type w} [TopologicalSpace X] (K : Set X) where
  val : Opens X
  property : K ⊆ val

instance {X : Type w} [TopologicalSpace X] (K : Set X) : Preorder (OpenNeighborhood K) where
  le U V := V.val ≤ U.val
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := hbc.trans hab

variable {X : Type w} [TopologicalSpace X] (K : Set X)

/-- Inclusion of a smaller open neighborhood in a larger one. -/
def neighborhoodInclusion {U V : OpenNeighborhood K} (f : U ⟶ V) :
    TopCat.of V.1 ⟶ TopCat.of U.1 :=
  TopCat.ofHom (ContinuousMap.inclusion (leOfHom f))

/-- The contravariant diagram of neighborhood spaces. -/
def neighborhoodSpaces : OpenNeighborhood K ⥤ TopCat.{w}ᵒᵖ where
  obj U := op (TopCat.of U.1)
  map f := (neighborhoodInclusion K f).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The pair with the fixed ambient space and the specified subspace. -/
def ambientPair (L : Set X) : Pair.{w} := ⟨TopCat.of X, L⟩

/-- Inclusion of pairs keeps the ambient map equal to the identity. -/
def ambientPairInclusion {L M : Set X} (h : L ⊆ M) :
    ambientPair L ⟶ ambientPair M := ⟨𝟙 _, h⟩

/-- The contravariant diagram of pairs `(X,U)`. -/
def neighborhoodPairs : OpenNeighborhood K ⥤ Pair.{w}ᵒᵖ where
  obj U := op (ambientPair (U.1 : Set X))
  map f := (ambientPairInclusion (leOfHom f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion used in the ordinary restriction map. -/
def compactInclusion (U : OpenNeighborhood K) : TopCat.of K ⟶ TopCat.of U.1 :=
  TopCat.ofHom (ContinuousMap.inclusion U.2)

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

abbrev ordinaryDiagram (q : ℤ) :=
  neighborhoodSpaces K ⋙ ordinaryCohomologyFunctor R A q

abbrev relativeDiagram (q : ℤ) :=
  neighborhoodPairs K ⋙ relativeCohomologyFunctor R A q

/-- The canonical cocone consists of actual restriction maps. -/
def ordinaryRestrictionCocone (q : ℤ) : Cocone (ordinaryDiagram K R A q) where
  pt := ordinaryCohomology R A (TopCat.of K) q
  ι :=
    { app := fun U => (ordinaryCohomologyFunctor R A q).map (compactInclusion K U).op
      naturality := fun U V f => by
        change (ordinaryCohomologyFunctor R A q).map (neighborhoodInclusion K f).op ≫
          (ordinaryCohomologyFunctor R A q).map (compactInclusion K V).op = _
        simp only [Functor.const_obj_map, ← Functor.map_comp]
        rfl }

/-- Relative restriction is induced by `(X,K) → (X,U)`. -/
def relativeRestrictionCocone (q : ℤ) : Cocone (relativeDiagram K R A q) where
  pt := relativeCohomology R A (ambientPair K) q
  ι :=
    { app := fun U => (relativeCohomologyFunctor R A q).map
        (ambientPairInclusion U.2).op
      naturality := fun U V f => by
        change (relativeCohomologyFunctor R A q).map
          (ambientPairInclusion (leOfHom f)).op ≫
          (relativeCohomologyFunctor R A q).map (ambientPairInclusion V.2).op = _
        simp only [Functor.const_obj_map, ← Functor.map_comp]
        rfl }

abbrev ordinaryComparison (q : ℤ) :=
  colimit.desc (ordinaryDiagram K R A q) (ordinaryRestrictionCocone K R A q)

abbrev relativeComparison (q : ℤ) :=
  colimit.desc (relativeDiagram K R A q) (relativeRestrictionCocone K R A q)

/-- The topological factorization needed for injectivity in the limit.
There is one retraction, and for each prescribed neighborhood its restriction
is homotopic inside that neighborhood to inclusion after a further shrink. -/
def HasShrinkingRetraction : Prop :=
  ∃ (U₀ : OpenNeighborhood K) (r : C(U₀.1, K)),
    (∀ x : K, r ⟨x.1, U₀.2 x.2⟩ = x) ∧
    ∀ U : OpenNeighborhood K, ∃ (V : OpenNeighborhood K)
      (hVU : (V.1 : Set X) ⊆ U.1) (hV₀ : (V.1 : Set X) ⊆ U₀.1),
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.inclusion hVU)
        ((ContinuousMap.inclusion U.2).comp (r.comp (ContinuousMap.inclusion hV₀))))

end P202.Duality.NeighborhoodCohomology

namespace P202Specs.Duality.NeighborhoodCohomology
open P202.Duality.NeighborhoodCohomology
universe u v

/-- Local contractibility has its classical nullhomotopic-inclusion meaning. -/
def sphereShrinkingRetraction : Prop :=
  ∀ (n : ℕ) (K : Set (Sphere n)), 1 ≤ n → K.Nonempty → K ≠ Set.univ →
    IsCompact K → LocallyContractibleSpace K → HasShrinkingRetraction K

/-- Stronger coefficient and degree generality includes integers and every
fixed field with itself as coefficient module, in all nonnegative degrees. -/
def ordinaryComparison : Prop :=
  ∀ (n : ℕ) (K : Set (Sphere n)), 1 ≤ n → K.Nonempty → K ≠ Set.univ →
    IsCompact K → LocallyContractibleSpace K →
    ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A] (q : ℤ),
      IsIso (P202.Duality.NeighborhoodCohomology.ordinaryComparison K R A q)

def relativeComparison : Prop :=
  ∀ (n : ℕ) (K : Set (Sphere n)), 1 ≤ n → K.Nonempty → K ≠ Set.univ →
    IsCompact K → LocallyContractibleSpace K →
    ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A] (q : ℤ),
      IsIso (P202.Duality.NeighborhoodCohomology.relativeComparison K R A q)

end P202Specs.Duality.NeighborhoodCohomology
