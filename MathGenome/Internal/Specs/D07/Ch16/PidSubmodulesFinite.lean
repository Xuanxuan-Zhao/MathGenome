import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
Independent specification of support.pid_submodules_finite,
paper.tex:3080–3089 (cor:pid-submodules-finite).

The scalar ring is a commutative nontrivial PID. The ambient module is
finitely generated, with no freeness or torsion-freeness assumption.
The submodule is arbitrary; in particular neither its finite generation
nor a nonzero condition is assumed. Zero modules are included.
`Module.Finite` means finite generation, not finite underlying cardinality.
-/

universe u v

namespace Specs.D07.Ch16.PidSubmodulesFinite

/-- Every submodule of a finitely generated module over a PID is finitely generated. -/
def SubmoduleFinite : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M), Module.Finite R N

end Specs.D07.Ch16.PidSubmodulesFinite
