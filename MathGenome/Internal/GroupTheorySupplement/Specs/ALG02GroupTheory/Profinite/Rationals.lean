import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Completion
import Mathlib.Algebra.Field.Rat

/-! The additive rationals and their profinite completion (GR02-C05.09). -/

namespace Specs.ALG02GroupTheory.Profinite

universe u

/-- `Multiplicative ℚ` uses rational addition as its group operation. -/
def RationalFiniteHomTrivial : Prop :=
  ∀ {H : Type u} [Group H] [Finite H] (f : Multiplicative ℚ →* H) (x : ℚ),
    f (Multiplicative.ofAdd x) = 1

def RationalFiniteQuotientSubsingleton : Prop :=
  ∀ N : FiniteIndexNormalSubgroup (Multiplicative ℚ),
    Subsingleton (Multiplicative ℚ ⧸ N.toSubgroup)

def RationalCompletionSubsingleton : Prop :=
  Subsingleton (completionValue (Multiplicative ℚ))

def RationalEtaDenseRange : Prop :=
  DenseRange (etaValue (Multiplicative ℚ) :
    Multiplicative ℚ → completionValue (Multiplicative ℚ))

end Specs.ALG02GroupTheory.Profinite
