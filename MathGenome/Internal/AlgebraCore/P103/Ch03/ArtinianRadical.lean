import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.ArtinianRadical
import MathGenome.Internal.AlgebraCore.P103.Ch03.JacobsonRadical
import Mathlib.RingTheory.Artinian.Module

/-!
Theorem 3.3, radical and quotient assertions, including the zero ring.

Mathlib's Artinian-to-semiprimary instance proves nilpotence directly:
stabilize the descending chain of radical powers, choose a minimal nonzero
left ideal fixed by the radical, prove it is cyclic, and apply Nakayama.
It does not use a Noetherian hypothesis or the Hopkins–Levitzki conclusion.
For the quotient it uses vanishing of its Jacobson radical and the Artinian
criterion for semisimplicity (embedding into finitely many simple quotients).
-/

universe u

namespace P103.Ch03.ArtinianRadical

open P103.Specs.Ch03.ArtinianRadical

theorem nilpotent : nilpotentType.{u} := by
  intro R _ _
  exact IsSemiprimaryRing.isNilpotent (R := R)

theorem quotient_semisimple : quotient_semisimpleType.{u} := by
  intro R _ _
  exact IsSemiprimaryRing.isSemisimpleRing (R := R)

/-- The opposite-ring application uses the original Jacobson radical. -/
theorem op_mem_radical : op_mem_radicalType.{u} := by
  intro R _ x
  have h := Set.ext_iff.mp (P103.Ch03.JacobsonRadical.left_eq_right R) x
  change x ∈ Ring.jacobson R ↔
    MulOpposite.op x ∈ sInf {L : Ideal Rᵐᵒᵖ | L.IsMaximal} at h
  rw [← Ring.jacobson_eq_sInf_isMaximal] at h
  exact h.symm

theorem right_nilpotent : right_nilpotentType.{u} := by
  intro R _ _
  exact nilpotent Rᵐᵒᵖ

theorem right_quotient_semisimple : right_quotient_semisimpleType.{u} := by
  intro R _ _
  exact quotient_semisimple Rᵐᵒᵖ

end P103.Ch03.ArtinianRadical
