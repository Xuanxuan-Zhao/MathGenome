import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.TraceContraction

namespace Specs.GaloisFormalization.GH.AdditiveGaloisCohomology

open GaloisFormalization.GH.Model

universe u v w

/-- Positive-degree ordinary cohomology of a finite Galois group with semilinear
vector space coefficients vanishes. -/
def FiniteSemilinearVanishing : Prop :=
  GaloisFormalization.GH.Specification.SemilinearVanishing.{u,v,w}

/-- Positive-degree continuous cohomology of the Krull Galois group with
coefficients in the additive group of the discrete extension field vanishes. -/
def ContinuousAdditiveVanishing : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    [TopologicalSpace L] [DiscreteTopology L] (q : ℕ), 0 < q →
      letI : ContinuousSMul Gal(L/k) L :=
        continuousSMul_iff_stabilizer_isOpen.mpr stabilizer_isOpen_of_isIntegral
      Subsingleton (ContinuousH (KrullLayers.GaloisGroup k L) L q)

end Specs.GaloisFormalization.GH.AdditiveGaloisCohomology
