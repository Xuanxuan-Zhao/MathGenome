import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellTopology

/-! Cellular-to-singular comparison for the specified skeletal complex.
`skeletalSpace X m` means X^(m-1), so stabilization in degree n starts at m=n+2.
All maps below are inclusions of the actual subspaces. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w

namespace P202Specs.CellularComparison
open P202.Cellular P202Specs.CellularChains P202Specs.SingularChains
open P202Specs.RelativeSingularChains

def skeletonInclusion (X : Type w) [TopologicalSpace X] [CellStructure X]
    {m k : ℕ} (h : m ≤ k) : skeletalSpace X m ⟶ skeletalSpace X k :=
  TopCat.ofHom ⟨fun x => ⟨x.val, skeletonLT_subset X h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def skeletonToSpace (X : Type w) [TopologicalSpace X] [CellStructure X]
    (m : ℕ) : skeletalSpace X m ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

namespace Expected

def skeletalVanishing : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (m n : ℕ), m ≤ n → IsZero (homology R M (skeletalSpace X m) (n : ℤ))

/-- Every finite singular chain lies in an actual skeleton, including chains
of degree zero and the zero chain in an empty space. -/
def finiteChainSupport : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (c : Chains M (TopCat.of X) n),
    ∃ m, ∃ b : Chains M (skeletalSpace X m) n,
      (chainMap R M (skeletonToSpace X m)).f n b = c

def skeletalStabilization : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n m : ℕ), n + 2 ≤ m →
    IsIso ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X m))

/-- A simultaneous choice of the canonical isomorphisms. The last identity
specifies the comparison on absolute skeletal classes; naturality uses every
chain map with the prescribed, already constructed, maps on skeletal groups.
Thus neither an unrelated cellular complex nor unrelated abstract isomorphisms
can satisfy the statement. -/
def comparison : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ∃ e : ∀ (X : Type w) [TopologicalSpace X] [CWStructure X] (n : ℕ),
      (cellularComplex X R M).homology n ≅ homology R M (TopCat.of X) (n : ℤ),
      (∀ (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y]
        [CWStructure X] [CWStructure Y] (f : CellularMap X Y)
        (F : cellularComplex X R M ⟶ cellularComplex Y R M)
        (_ : ∀ n, F.f n = cellularDegreeMap R M f n) (n : ℕ),
        homologyMap F n ≫ (e Y n).hom =
          (e X n).hom ≫ (homologyFunctor R M (n : ℤ)).map (TopCat.ofHom f.map)) ∧
      (∀ (X : Type w) [TopologicalSpace X] [CWStructure X] (n : ℕ)
        (z : (cellularComplex X R M).cycles n)
        (a : homology R M (skeletalSpace X (n+1)) (n : ℤ)),
        (cellularComplex X R M).iCycles n z =
          homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ) a →
        (e X n).hom ((cellularComplex X R M).homologyπ n z) =
          (homologyFunctor R M (n : ℤ)).map (skeletonToSpace X (n+1)) a)

end Expected
end P202Specs.CellularComparison
