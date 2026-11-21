import MathGenome.Internal.Specs.D05.M11.Pfaffian
import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-! The square identity of paper.tex:1840–1854, with the paper's ordered dual
coordinate normalization. All real skew matrices are allowed, including the
singular matrix and the empty matrix. -/
namespace Specs.D05.M11.Pfaffian.Square

/-- The Pfaffian constructed from the normalized wedge squares to the
column-Leibniz determinant already used in the manuscript. -/
def square : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    (∀ i j, A i j = -A j i) →
    pfaffian_value A ^ 2 = D05.M05.determinant A

end Specs.D05.M11.Pfaffian.Square
