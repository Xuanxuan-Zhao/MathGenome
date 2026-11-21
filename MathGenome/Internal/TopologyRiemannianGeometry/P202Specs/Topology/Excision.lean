import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains

/-! Excision, paper.tex 1318–1338, with the conventions of 1027–1050.
The ordinary complexes are nonnegatively graded. The sets being excised
need not be closed and the second terms of the pairs need not be open.
The naturality square uses the actual maps of relative singular complexes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
namespace P202Specs.Excision
open P202Specs.SingularChains P202Specs.RelativeSingularChains

structure Data where
  pair : Pair.{v}
  removed : Set pair.space
  subset : removed ⊆ pair.subspace
  closure_subset : closure removed ⊆ interior pair.subspace

/-- The subspace pair (X ∖ Z, A ∖ Z), with its actual subspace topologies. -/
def Data.excised (D : Data.{v}) : Pair.{v} :=
  ⟨TopCat.of {x : D.pair.space // x ∉ D.removed}, Subtype.val ⁻¹' D.pair.subspace⟩

def Data.inclusion (D : Data.{v}) : D.excised ⟶ D.pair :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ h => h⟩

/-- Maps of excision data preserve both second terms and the complements
of the removed sets. This is exactly what is needed to map both pairs. -/
structure Map (D E : Data.{v}) where
  pairMap : D.pair ⟶ E.pair
  outside : Set.MapsTo pairMap.map D.removedᶜ E.removedᶜ

def Map.excised {D E : Data.{v}} (f : Map D E) : D.excised ⟶ E.excised where
  map := TopCat.ofHom ⟨fun x => ⟨f.pairMap.map x.val, f.outside x.property⟩,
    (f.pairMap.map.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  mapsTo := fun _ h => f.pairMap.mapsTo h

lemma Map.square {D E : Data.{v}} (f : Map D E) :
    D.inclusion ≫ f.pairMap = f.excised ≫ E.inclusion := by
  apply PairMap.ext
  rfl

/-- Excision for arbitrary commutative coefficient rings and every ordinary degree. -/
def isomorphism_type : Prop :=
  ∀ (R : Type u) [CommRing R] (D : Data.{v}) (n : ℕ),
    IsIso (homologyMap (relativeMap (chainFunctor R R) D.inclusion) n)

/-- The excision isomorphisms commute with maps of excision data. -/
def naturality_type : Prop :=
  ∀ (R : Type u) [CommRing R] (D E : Data.{v}) (f : Map D E) (n : ℕ),
    homologyMap (relativeMap (chainFunctor R R) D.inclusion) n ≫
      homologyMap (relativeMap (chainFunctor R R) f.pairMap) n =
    homologyMap (relativeMap (chainFunctor R R) f.excised) n ≫
      homologyMap (relativeMap (chainFunctor R R) E.inclusion) n

end P202Specs.Excision
