import MathGenome.Internal.Specs.D07.Ch16.PidSubmodulesFinite
import Mathlib.RingTheory.Noetherian.Basic

/-!
The corollary cor:pid-submodules-finite (paper.tex:3080–3089).

Every ideal of a PID is principal and thus finitely generated, so the ring
is Noetherian. A finitely generated module over a Noetherian ring is
Noetherian; hence its arbitrary submodule is finitely generated.
-/

universe u v

namespace D07.Ch16.PidSubmodulesFinite

/-- Finite generation descends to every submodule of a finitely generated PID-module. -/
theorem submoduleFinite :
    Specs.D07.Ch16.PidSubmodulesFinite.SubmoduleFinite.{u, v} := by
  intro R _ _ _ M _ _ _ N
  exact Module.Finite.of_fg (IsNoetherian.noetherian N)

end D07.Ch16.PidSubmodulesFinite
