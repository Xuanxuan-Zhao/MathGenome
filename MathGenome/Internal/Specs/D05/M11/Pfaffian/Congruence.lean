import MathGenome.Internal.Specs.D05.M11.Pfaffian
import MathGenome.Internal.Specs.D05.M15.DeterminantLine
import MathGenome.Internal.Specs.D05.M07.DualMap
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Independent statements for paper.tex:1840–1847. Pullback is precomposition
on the actual algebraic dual, extended to the exterior algebra. All matrices P
are allowed; in particular there is no invertibility hypothesis. -/

noncomputable section
namespace Specs.D05.M11.Pfaffian.Congruence

open Specs.D05.M11.Pfaffian

/-- Pullback of the two-form has the congruence matrix in the fixed coordinates. -/
def pullback_omega : Prop :=
  ∀ (m : ℕ) (A P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    (∀ i j, A i j = -A j i) →
    ExteriorAlgebra.map (Matrix.toLin' P).dualMap (omega_value A) =
      omega_value (P.transpose * A * P)

/-- The fixed ordered dual volume transforms by the determinant, including
singular coordinate maps and the empty ordered basis. -/
def pullback_volume : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    ExteriorAlgebra.map (Matrix.toLin' P).dualMap (volume_value m) =
      D05.M05.determinant P • volume_value m

/-- Congruence covariance of the Pfaffian defined by the normalized m-fold wedge. -/
def congruence : Prop :=
  ∀ (m : ℕ) (A P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    (∀ i j, A i j = -A j i) →
    pfaffian_value (P.transpose * A * P) = D05.M05.determinant P * pfaffian_value A

/-- The dimension-zero congruence equation is explicitly 1 = 1. -/
def empty_congruence : Prop :=
  ∀ (A P : Matrix (Fin (2*0)) (Fin (2*0)) ℝ),
    pfaffian_value (P.transpose * A * P) = 1 ∧
      D05.M05.determinant P * pfaffian_value A = 1

end Specs.D05.M11.Pfaffian.Congruence
