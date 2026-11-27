import Mathlib.FieldTheory.Galois.Basic
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains

namespace GaloisFormalization.GH.Specification

universe u v w

open Model

/-- Positive-degree vanishing for the discrete finite-stage cohomology model. -/
def DiscreteSemilinearVanishing : Prop :=
  ∀ (k : Type u) (E : Type v) (V : Type w) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] [AddCommGroup V] [Module E V]
    [DistribMulAction Gal(E/k) V] [TopologicalSpace Gal(E/k)] [DiscreteTopology Gal(E/k)]
    [TopologicalSpace V] [DiscreteTopology V],
    (∀ (g : Gal(E/k)) (a : E) (b : V), g • (a • b) = g a • (g • b)) →
    ∀ q : ℕ, 0 < q → Subsingleton (ContinuousH Gal(E/k) V q)

/-- The finite semilinear assertion of GH08, in ordinary integral group cohomology. -/
def SemilinearVanishing : Prop :=
  ∀ (k : Type u) (E : Type v) (V : Type w) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] [AddCommGroup V] [Module E V]
    [DistribMulAction Gal(E/k) V],
    (∀ (g : Gal(E/k)) (a : E) (b : V), g • (a • b) = g a • (g • b)) →
    ∀ q : ℕ, 0 < q →
      Subsingleton (groupCohomology (integralRepresentation.{v,w,max v w} Gal(E/k) V) q)

end GaloisFormalization.GH.Specification
