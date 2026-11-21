import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs
import Mathlib.Algebra.Central.Matrix

/-! Specifications for RM03-C04.02. -/

universe u v w x

namespace Specs.RM03.CSA.MatrixDivision

/-- The center of a matrix algebra consists of scalar matrices with central entries. -/
def CenterEqScalarMap : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D] (r : ℕ),
    Subalgebra.center k (Matrix (Fin r) (Fin r) D) =
      (Subalgebra.center k D).map (Matrix.scalarAlgHom (Fin r) k)

/-- A central simple algebra has a positive-size presentation over a central division algebra. -/
def ExistsPresentation : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A],
    isCentralSimple k A →
    ∃ (r : ℕ) (D : Type v) (_ : DivisionRing D) (_ : Algebra k D),
      isCentralDivision k D ∧ 0 < r ∧ Nonempty (A ≃ₐ[k] Matrix (Fin r) (Fin r) D)

/-- The matrix size and the division algebra up to equivalence over the original field are unique. -/
def PresentationUnique : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A],
    isCentralSimple k A →
    ∀ (D : Type w) [DivisionRing D] [Algebra k D]
      (E : Type x) [DivisionRing E] [Algebra k E] (r s : ℕ),
      0 < r → 0 < s →
      (A ≃ₐ[k] Matrix (Fin r) (Fin r) D) →
      (A ≃ₐ[k] Matrix (Fin s) (Fin s) E) →
      r = s ∧ Nonempty (D ≃ₐ[k] E)

end Specs.RM03.CSA.MatrixDivision
