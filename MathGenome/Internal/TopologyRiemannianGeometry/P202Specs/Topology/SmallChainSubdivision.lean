import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularSubdivision

noncomputable section
namespace P202Specs.SmallChainSubdivision
open P202Specs.SingularChains P202Specs.SingularSubdivision
universe u v w

/-- A sufficiently iterated concrete barycentric subdivision of each singular
simplex is small for the given indexed open cover. The level is simplex dependent. -/
def eventualSmall : Prop :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{v}) (ι : Type w)
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
    ∀ (n : ℕ) (s : Simplex X n), ∃ m : ℕ,
      IsSmall U (((subdivision R X n) ^ m) (Finsupp.single s 1))

end P202Specs.SmallChainSubdivision
