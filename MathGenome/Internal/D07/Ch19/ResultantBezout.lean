import MathGenome.Internal.Specs.D07.Ch19.ResultantBezout
import MathGenome.Internal.D07.Ch19.ResultantDefinition

/-!
K07.19.resultant_bezout: bounded Bézout certificates for the notes' literal
descending Sylvester determinant. Mathlib's adjugate construction supplies
the bounded multipliers over an arbitrary commutative ring; the upstream
bridge identifies its determinant with the one in the paper.
-/

universe u v

namespace D07.Ch19.ResultantBezout

open Polynomial
open Specs.D07.Ch19.ResultantDefinition
open Specs.D07.Ch19.ResultantBezout

theorem bezoutCertificate : BezoutCertificate.{u} := by
  intro R _ f g n m hf hg hpos
  have hf' : f.natDegree ≤ n := natDegree_le_of_degree_le hf
  have hg' : g.natDegree ≤ m := natDegree_le_of_degree_le hg
  obtain ⟨U, V, hU, hV, h⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf' hg' (by omega)
  refine ⟨U, V, hU, hV, ?_⟩
  rw [D07.Ch19.ResultantDefinition.resultantBridge R f g n m hf' hg']
  simpa only [mul_comm] using h.symm

theorem emptyDeterminant : Specs.D07.Ch19.ResultantBezout.EmptyDeterminant.{u} := by
  exact D07.Ch19.ResultantDefinition.emptyDeterminant

/-- The determinant comparison retains the original degree parameters,
including when the coefficient map kills leading coefficients. -/
lemma fixedResultant_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (f g : R[X]) (n m : ℕ)
    (hf : f.degree ≤ (n : WithBot ℕ)) (hg : g.degree ≤ (m : WithBot ℕ)) :
    fixedResultant (f.map φ) (g.map φ) n m = φ (fixedResultant f g n m) := by
  have hf' : f.natDegree ≤ n := natDegree_le_of_degree_le hf
  have hg' : g.natDegree ≤ m := natDegree_le_of_degree_le hg
  rw [D07.Ch19.ResultantDefinition.resultantBridge S (f.map φ) (g.map φ) n m
    (natDegree_map_le.trans hf') (natDegree_map_le.trans hg'),
    D07.Ch19.ResultantDefinition.resultantBridge R f g n m hf' hg',
    Polynomial.resultant_map_map]

theorem certificateUnderHomomorphism : CertificateUnderHomomorphism.{u, v} := by
  intro R S _ _ φ f g n m U V hf hg hU hV h
  refine ⟨degree_map_le.trans_lt hU, degree_map_le.trans_lt hV, ?_⟩
  rw [fixedResultant_map φ f g n m hf hg]
  simpa only [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul] using
    congrArg (Polynomial.map φ) h

theorem necessaryElimination : NecessaryElimination.{u, v} := by
  intro R S _ _ φ f g n m x hf hg hpos hfx hgx
  obtain ⟨U, V, _, _, h⟩ := bezoutCertificate R f g n m hf hg hpos
  have heval := congrArg (fun p : R[X] => (p.map φ).eval x) h
  simpa only [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul,
    eval_C, eval_add, eval_mul, hfx, hgx, mul_zero, add_zero] using heval

end D07.Ch19.ResultantBezout
