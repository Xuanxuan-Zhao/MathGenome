import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra

/-! The separating-vector assertion for actual bounded operators.
No closure hypothesis on the unital star subalgebra is imposed. -/
namespace ExpandedFA.VonNeumann.SeparableAbelianSeparating.Spec
universe u

def SeparatingVector : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)),
    (∀ S ∈ A, ∀ T ∈ A, S * T = T * S) →
    ∃ e : H, ∀ T ∈ A, T e = 0 → T = 0

/-- Real separating-vector existence on the actual real Hilbert space.
As in the complex helper, no WOT-closedness is needed. -/
def RealSeparatingVector : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    (∀ S ∈ A, ∀ T ∈ A, S * T = T * S) →
    ∃ e : H, ∀ T ∈ A, T e = 0 → T = 0

end ExpandedFA.VonNeumann.SeparableAbelianSeparating.Spec
