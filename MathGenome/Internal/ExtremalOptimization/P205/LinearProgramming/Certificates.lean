import MathGenome.Internal.ExtremalOptimization.Specs.P205.LinearProgramming.Certificates
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.LinearProgramDuality
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.FiniteConesFarkas

noncomputable section
open Matrix
universe u v
namespace P205.LinearProgramming.Certificates
open VariationalNotes.Ch05.LinearProgramModels

/-- The primal equality turns the objective gap into the sum of complementary products. -/
theorem gap_identity : Specs.gap_identity.{u,v} := by
  intro m n _ _ A b c x y hx
  exact VariationalNotes.Ch05.LinearProgramModels.gap_identity A b c x y hx

theorem gap_nonnegative : Specs.gap_nonnegative.{u,v} := by
  intro m n _ _ A b c x y hx hy
  exact VariationalNotes.Ch05.LinearProgramModels.gap_nonnegative A b c x y hx hy

theorem weak_duality : Specs.weak_duality.{u,v} := by
  intro m n _ _ A b c x y hx hy
  exact weakDuality A b c x y hx hy

theorem objective_eq_iff_complementarity :
    Specs.objective_eq_iff_complementarity.{u,v} := by
  intro m n _ _ A b c x y hx hy
  rw [← sub_eq_zero]
  exact gap_eq_zero_iff A b c x y hx hy

theorem optimality_certificate : Specs.optimality_certificate.{u,v} := by
  intro m n _ _ A b c x y hx hy h
  have heq : primalObjective c x = dualObjective b y := by
    rcases h with heq | hcomp
    · exact heq
    · exact (objective_eq_iff_complementarity A b c x y hx hy).mpr hcomp
  exact VariationalNotes.Ch05.LinearProgramDuality.zero_gap_certificate
    A b c x y hx hy (sub_eq_zero.mpr heq)

/-- Finite extended-real value gives an attained equal-value pair, without any
rank or compactness assumption on the feasible region. -/
theorem finite_infimum_attained : Specs.finite_infimum_attained.{u,v} := by
  intro m n _ _ A b c p hfeas hp
  obtain ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩, _, _⟩ :=
    VariationalNotes.Ch05.LinearProgramDuality.strong_duality A b c p hfeas hp
  exact ⟨x, y, hx, hy, hxp, hyp⟩

/-- Farkas uses a nonnegative transposed product and a strictly negative pairing
with b; no sign restriction is imposed on the certificate vector itself. -/
theorem infeasible_iff_certificate : Specs.infeasible_iff_certificate.{u,v} := by
  intro m n _ _ A b
  constructor
  · intro hnot
    rcases VariationalNotes.ConvexGeometry.farkas_alternative A b with
      ⟨⟨x, hx, hAx⟩, _⟩ | ⟨hcert, _⟩
    · exact (hnot ⟨x, hAx, hx⟩).elim
    · exact hcert
  · intro hcert ⟨x, hAx, hx⟩
    exact VariationalNotes.ConvexGeometry.farkas_exclusive A b ⟨x, hx, hAx⟩ hcert

end P205.LinearProgramming.Certificates
