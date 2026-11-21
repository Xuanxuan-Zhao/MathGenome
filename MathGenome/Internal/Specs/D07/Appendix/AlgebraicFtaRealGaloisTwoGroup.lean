import Mathlib.Basic.Real.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index

/-!
Independent specification of the Sylow-2 step in `thm:algebraic-fta`,
paper.tex:7608. The extension is an arbitrary finite Galois extension
of the real field with its specified embedding, not an extension already
embedded in the complex field. No complex closedness or transcendence
hypothesis occurs. The bottom intermediate field is the image of ℝ.
The finite-cardinality definition of a 2-group includes order 2^0 = 1.
-/

universe u

namespace Specs.D07.Appendix.AlgebraicFtaRealGaloisTwoGroup

/-- An odd-index subgroup has exactly the real scalars as its fixed field. -/
def OddIndexFixedField : Prop :=
  ∀ (L : Type u) [Field L] [Algebra ℝ L] [FiniteDimensional ℝ L] [IsGalois ℝ L]
    (H : Subgroup (L ≃ₐ[ℝ] L)),
    Odd H.index → IntermediateField.fixedField H = ⊥

/-- The Galois correspondence then forces that subgroup to be the full group. -/
def OddIndexSubgroup : Prop :=
  ∀ (L : Type u) [Field L] [Algebra ℝ L] [FiniteDimensional ℝ L] [IsGalois ℝ L]
    (H : Subgroup (L ≃ₐ[ℝ] L)),
    Odd H.index → H = ⊤

/-- Every finite Galois extension of ℝ has a finite Galois group of 2-power order. -/
def FiniteGaloisTwoGroup : Prop :=
  ∀ (L : Type u) [Field L] [Algebra ℝ L] [FiniteDimensional ℝ L] [IsGalois ℝ L],
    Finite (L ≃ₐ[ℝ] L) ∧ ∃ a : ℕ, Nat.card (L ≃ₐ[ℝ] L) = 2 ^ a

end Specs.D07.Appendix.AlgebraicFtaRealGaloisTwoGroup
