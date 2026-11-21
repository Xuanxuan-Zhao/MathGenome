import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionInterface
import Mathlib.RingTheory.Noetherian.Basic

/-! Noetherianness in Theorem 7.5 (paper.tex:1229–1240).
The ideal is arbitrary, and neither a properness nor a nonzero hypothesis
is imposed on the ring or its completion. -/
universe u

namespace P103.Specs.Ch07.CompletedNoetherian

def completed_noetherianType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (P103.Adic.Completion I R)

end P103.Specs.Ch07.CompletedNoetherian
