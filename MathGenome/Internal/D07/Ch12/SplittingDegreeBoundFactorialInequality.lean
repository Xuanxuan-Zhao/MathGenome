import MathGenome.Internal.Specs.D07.Ch12.SplittingDegreeBoundFactorialInequality
import MathGenome.Internal.D07.Ch12.SplittingDefinition
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.LinearAlgebra.Dimension.Free

/-!
The splitting-field construction successively adjoins a root of an irreducible
factor and removes one linear factor. At a degree-(n+1) step the root adjunction
has degree at most n+1, and induction bounds the remaining extension by n!.
The tower law therefore bounds the constructed field by (n+1)!. Transport along
the base-preserving splitting-field equivalence handles any realization L/K.
The construction is over abstract fields and allows inseparability.
-/

universe u v

namespace D07.Ch12.SplittingDegreeBoundFactorialInequality

open Polynomial

/-- The factorial estimate for the recursive root-adjunction construction.
The base field varies in the induction, because each step changes the base. -/
theorem finrank_splittingFieldAux_le_factorial (n : ℕ) :
    ∀ (K : Type u) [Field K] (f : Polynomial K), f.natDegree = n →
      Module.finrank K (SplittingFieldAux n f) ≤ n.factorial := by
  induction n with
  | zero =>
      intro K _ f _
      change Module.finrank K K ≤ Nat.factorial 0
      simp
  | succ n ih =>
      intro K _ f hf
      let : Fact (Irreducible f.factor) := ⟨irreducible_factor f⟩
      have hfpos : f.natDegree ≠ 0 := by omega
      have hf0 : f ≠ 0 := fun h => hfpos (h ▸ natDegree_zero)
      have hfactor : f.factor.natDegree ≤ n + 1 := by
        rw [← hf]
        exact natDegree_le_of_dvd (factor_dvd_of_natDegree_ne_zero hfpos) hf0
      have hroot : Module.finrank K (AdjoinRoot f.factor) = f.factor.natDegree :=
        (AdjoinRoot.powerBasis (irreducible_factor f).ne_zero).finrank
      change Module.finrank K (SplittingFieldAux n f.removeFactor) ≤ (n + 1).factorial
      rw [← Module.finrank_mul_finrank K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor), hroot, Nat.factorial_succ]
      exact Nat.mul_le_mul hfactor
        (ih (AdjoinRoot f.factor) f.removeFactor (natDegree_removeFactor' hf))

/-- Finite cardinal degree and the factorial upper bound, for any splitting
field with its specified structure map. -/
theorem factorial_inequality :
    Specs.D07.Ch12.SplittingDegreeBoundFactorialInequality.FactorialInequality.{u, v} := by
  intro K L _ _ _ f hf
  let : Polynomial.IsSplittingField K L f :=
    (SplittingDefinition.library_characterization K L f hf.1).mp hf
  let : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L f
  let e : L ≃ₐ[K] SplittingFieldAux f.natDegree f :=
    (Polynomial.IsSplittingField.algEquiv L f).trans
      (Polynomial.SplittingField.algEquivSplittingFieldAux f)
  refine ⟨Module.finrank K L, (Module.finrank_eq_rank K L).symm, ?_⟩
  rw [e.toLinearEquiv.finrank_eq]
  exact finrank_splittingFieldAux_le_factorial f.natDegree K f rfl

end D07.Ch12.SplittingDegreeBoundFactorialInequality
