import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Separable

namespace P103.Ch06.FrobeniusCover
universe u v

/-- Finite separability is measured for the actual field inclusion. -/
def CoefficientCover : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP K p]
    (L : IntermediateField K Ω), Module.Finite K L →
    ∃ (e : ℕ) (S : Finset K), ∀ (M : IntermediateField K Ω),
      (∀ a ∈ S, ∃ b : M, (b : Ω) ^ (p ^ e) = algebraMap K Ω a) →
      ∃ (N : IntermediateField K Ω), L ≤ N ∧
        ∃ h : M ≤ N, letI := (IntermediateField.inclusion h).toAlgebra;
          Module.Finite M N ∧ Algebra.IsSeparable M N

end P103.Ch06.FrobeniusCover
