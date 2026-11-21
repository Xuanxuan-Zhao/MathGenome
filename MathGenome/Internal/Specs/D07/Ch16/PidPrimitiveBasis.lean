import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
Independent specification of `lem:pid-primitive-basis`, paper.tex:2994–3016.
The scalar ring is an arbitrary commutative nontrivial PID, and `R^n` is
the ordinary left module of coordinate functions. The hypothesis says
exactly that the coordinates generate the unit ideal. The conclusion
places the given vector in a basis with `n` vectors. There is no positivity
assumption on `n`: in rank zero the hypothesis is impossible.
-/

universe u

namespace Specs.D07.Ch16.PidPrimitiveBasis

open Module

/-- A vector whose coordinates generate the whole PID belongs to a basis. -/
def PrimitiveExtendsToBasis : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (n : ℕ) (e : Fin n → R),
    Ideal.span (Set.range e) = ⊤ →
      ∃ b : Basis (Fin n) R (Fin n → R), e ∈ Set.range b

end Specs.D07.Ch16.PidPrimitiveBasis
