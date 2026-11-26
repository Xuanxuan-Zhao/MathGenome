import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteValuationDegreeBound
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PurelyInseparableValuationExtension

namespace Specs.CommutativeAlgebraNotes.ValuationExtensionDegreesAndInseparability

universe u v

/-- In a purely inseparable field extension the unique valuation subring extending `V`
is the integral closure of `V`. -/
def PurelyInseparableClassification : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (V : ValuationSubring K),
    ∃ W : ValuationSubring L,
      W.comap (algebraMap K L) = V ∧
      W.toSubring = (integralClosure V L).toSubring ∧
      ∀ W' : ValuationSubring L, W'.comap (algebraMap K L) = V → W' = W

/-- The finite degree bound and the purely inseparable classification of Theorem 5.22. -/
def ExtensionDegreesAndInseparability : Prop :=
  FiniteValuationDegreeBound.DegreeBound.{u, v} ∧ PurelyInseparableClassification.{u, v}

end Specs.CommutativeAlgebraNotes.ValuationExtensionDegreesAndInseparability
