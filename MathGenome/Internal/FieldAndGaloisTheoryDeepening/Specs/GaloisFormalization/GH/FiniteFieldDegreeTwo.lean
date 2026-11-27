import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers

namespace GaloisFormalization.GH.FiniteFieldDegreeTwo.Specification

open GaloisFormalization.GH.Model
open Specs.GaloisFormalization.GH.KrullLayers (AbsoluteGaloisGroup)
open scoped Algebra

universe u v

/-- The second continuous cohomology of a finite field with multiplicative coefficients
in its chosen separable closure is trivial. The units carry the discrete topology. -/
def Vanishing : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Finite k] [Field S] [Algebra k S]
    [IsSepClosure k S],
    letI : TopologicalSpace Sˣ := ⊥
    letI : DiscreteTopology Sˣ := discreteTopology_bot _
    haveI : ContinuousSMul (AbsoluteGaloisGroup k S) Sˣ :=
      continuousSMul_iff_stabilizer_isOpen.mpr (by
        intro a
        convert (stabilizer_isOpen_of_isIntegral (K := k) (a : S)) using 1
        ext σ
        change σ • a = a ↔ σ • (a : S) = (a : S)
        exact ⟨congrArg Units.val, fun h => Units.ext h⟩)
    Subsingleton (ContinuousMulH (AbsoluteGaloisGroup k S) Sˣ 2)

end GaloisFormalization.GH.FiniteFieldDegreeTwo.Specification
