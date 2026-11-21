import MathGenome.Internal.Specs.D07.Ch19.CommutativeRingAdjugate
import MathGenome.Internal.D07.Ch08.MatrixRing

/-!
The commutative-ring adjugate lemma, paper.tex:5369–5398.
The canonical adjugate has exactly the signed-minor entries in the paper.
The library's two product identities require only a commutative unital
ring, so they also cover characteristic two, zero divisors, and the zero ring.
-/

universe u

namespace D07.Ch19.CommutativeRingAdjugate

open Specs.D07.Ch19.CommutativeRingAdjugate

theorem cofactorEntries : CofactorEntries.{u} := by
  intro R _ n A i j
  exact Matrix.adjugate_fin_succ_eq_det_submatrix A i j

theorem adjugateIdentities : AdjugateIdentities.{u} := by
  intro R _ n _ A
  exact ⟨Matrix.adjugate_mul A, Matrix.mul_adjugate A⟩

end D07.Ch19.CommutativeRingAdjugate
