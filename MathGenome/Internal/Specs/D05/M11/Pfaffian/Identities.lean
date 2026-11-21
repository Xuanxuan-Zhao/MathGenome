import MathGenome.Internal.Specs.D05.M11.Pfaffian
import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-! The two matrix Pfaffian identities of paper.tex:1840–1854.
The shared Pfaffian uses the ordered dual coordinate volume, with value one
in dimension zero. No invertibility assumption is imposed on either matrix. -/

namespace Specs.D05.M11.Pfaffian.Identities

/-- Congruence covariance and the determinant square identity for every real
even-sized skew-symmetric matrix, including the singular and empty cases. -/
def identities : Prop :=
  ∀ (m : ℕ) (A P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    (∀ i j, A i j = -A j i) →
    pfaffian_value (P.transpose * A * P) =
        D05.M05.determinant P * pfaffian_value A ∧
      pfaffian_value A ^ 2 = D05.M05.determinant A

end Specs.D05.M11.Pfaffian.Identities
