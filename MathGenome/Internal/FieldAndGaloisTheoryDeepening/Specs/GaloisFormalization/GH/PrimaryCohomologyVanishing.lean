import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers

namespace Specs.GaloisFormalization.GH.PrimaryCohomologyVanishing

open KrullLayers (AbsoluteGaloisGroup)
open _root_.GaloisFormalization.GH.Model (ContinuousH)

universe u v w

/-- Continuous cohomology in degree at least two vanishes for discrete p-primary
abelian coefficients over a field of characteristic p. -/
def vanishing_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [CharP k p] [IsSepClosure k S] (_hp : 0 < p)
    (M : Type w) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup k S) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (AbsoluteGaloisGroup k S) M],
    (∀ m : M, ∃ r : ℕ, p ^ r • m = 0) →
    ∀ q : ℕ, 2 ≤ q → Subsingleton (ContinuousH (AbsoluteGaloisGroup k S) M q)

end Specs.GaloisFormalization.GH.PrimaryCohomologyVanishing
