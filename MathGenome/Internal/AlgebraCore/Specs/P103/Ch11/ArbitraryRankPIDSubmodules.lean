import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
The arbitrary-cardinality assertion of paper.tex, Lemma 11.7
(`p103:pid-submodule-arbitrary`, lines 2895–2924).
A PID is a commutative domain all of whose ideals are principal.
Freeness has no finiteness hypothesis and allows the empty basis.
-/

universe u v

namespace Specs.P103.Ch11.ArbitraryRankPIDSubmodules

/-- Every submodule of every free module over a PID is free, at any rank.
This includes the zero ambient module and the zero submodule. -/
def freeSubmodule : Prop :=
  ∀ (R : Type u) (F : Type v) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup F] [Module R F] [Module.Free R F]
    (N : Submodule R F), Module.Free R N

end Specs.P103.Ch11.ArbitraryRankPIDSubmodules
