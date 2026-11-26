import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Specs.CommutativeAlgebraNotes.PurelyInseparableValuationExtension

universe u v

/-- A valuation subring has a unique extension along any purely inseparable field extension. -/
def ExistsUniqueExtension : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (V : ValuationSubring K),
    ∃! W : ValuationSubring L, W.comap (algebraMap K L) = V

/-- The extended valuation subring is the integral closure in the extension field. -/
def ExtensionEqIntegralClosure : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (V : ValuationSubring K) (W : ValuationSubring L),
    W.comap (algebraMap K L) = V →
    W.toSubring = (integralClosure V L).toSubring

/-- Membership in the extended valuation subring can be tested using any
`p ^ n`-th power that lies in the base field, where `p` is the exponential characteristic. -/
def MemIffPowMem : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L),
    W.comap (algebraMap K L) = V →
    ∀ (p : ℕ) [ExpChar K p] (n : ℕ) (x : L) (y : K),
      algebraMap K L y = x ^ (p ^ n) → (x ∈ W ↔ y ∈ V)

end Specs.CommutativeAlgebraNotes.PurelyInseparableValuationExtension
