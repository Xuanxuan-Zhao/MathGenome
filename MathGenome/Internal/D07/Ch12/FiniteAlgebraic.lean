import MathGenome.Internal.Specs.D07.Ch12.FiniteAlgebraic
import MathGenome.Internal.D07.Ch12.AlgebraicDefinition
import MathGenome.Internal.D07.Ch12.DegreeDefinition
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite extensions are algebraic

K07.12.finite_algebraic, paper.tex:3575–3582.
The proof uses dependence of the first n+1 powers in an n-dimensional
vector space. The coefficients of a nontrivial relation give the polynomial;
its coefficient vector guarantees the degree bound and that it is nonzero.
-/

universe u v

namespace D07.Ch12.FiniteAlgebraic

open Polynomial

private theorem exists_annihilator_of_finrank (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (α : L) :
    ∃ f : Polynomial K, f ≠ 0 ∧
      f.degree ≤ (Module.finrank K L : WithBot ℕ) ∧ aeval α f = 0 := by
  classical
  let n := Module.finrank K L
  have hdep : ¬ LinearIndependent K (fun i : Fin (n + 1) => α ^ (i : ℕ)) := by
    intro hind
    have hcard := hind.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    exact Nat.not_succ_le_self n hcard
  obtain ⟨c, hsum, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨ofFn (n + 1) c, ?_, ?_, ?_⟩
  · intro hzero
    apply hi
    have hcoeff := congrArg (fun f : Polynomial K => f.coeff (i : ℕ)) hzero
    simpa only [ofFn_coeff_eq_val_of_lt c i.isLt, coeff_zero] using hcoeff
  · exact degree_le_of_natDegree_le
      (Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos n) c))
  · rw [ofFn_eq_sum_monomial, map_sum]
    simpa only [aeval_monomial, Algebra.smul_def] using hsum

/-- The paper's full assertion, with cardinal extension degree and a
nonzero annihilator of degree at most the specified natural number n. -/
theorem exists_annihilating_polynomial :
    Specs.D07.Ch12.FiniteAlgebraic.ExistsAnnihilatingPolynomial.{u, v} := by
  intro K L _ _ _ n hdegree α
  obtain ⟨hfinite, hfinrank⟩ :=
    (DegreeDefinition.degree_eq_nat_iff K L n).mp hdegree
  let := hfinite
  obtain ⟨f, hf, hbound, heval⟩ := exists_annihilator_of_finrank K L α
  exact ⟨f, hf, hfinrank ▸ hbound, heval⟩

/-- Dropping the degree bound yields elementwise algebraicity. -/
theorem finite_extension_is_algebraic :
    Specs.D07.Ch12.FiniteAlgebraic.FiniteExtensionIsAlgebraic.{u, v} := by
  intro K L _ _ _ hfinite
  apply (AlgebraicDefinition.algebraicExtensionCharacterization K L).mpr
  intro α
  obtain ⟨n, hdegree⟩ := hfinite
  obtain ⟨f, hf, _, heval⟩ := exists_annihilating_polynomial K L n hdegree α
  exact ⟨f, hf, heval⟩

end D07.Ch12.FiniteAlgebraic
