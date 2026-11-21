import Mathlib.FieldTheory.SeparableClosure

/-!
Independent specification for the common-exponent assertion in
K07.20.separable_part, paper.tex:5833–5850.

`separableClosure K L` is the internal intermediate field whose carrier is
exactly the elements of L separable over K. Finite dimension supplies
algebraicity; no perfection or separability of the original extension is
assumed. The exponent is chosen before the universally quantified element.
-/

universe u v

namespace Specs.D07.Ch20.SeparablePartUniformInseparableExponent

/-- One Frobenius power sends the entire finite extension into its separable part. -/
def UniformInseparableExponent : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [CharP K p], p.Prime →
      ∃ r : ℕ, ∀ x : L, x ^ (p ^ r) ∈ separableClosure K L

end Specs.D07.Ch20.SeparablePartUniformInseparableExponent
